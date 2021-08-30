module Main where

import Data.Bifunctor
import Data.Char
import Data.CodePoint.Unicode
import Data.Either
import Data.Maybe
import Data.String.Pattern
import Data.Tuple
import Prelude

import Data.Array as A
import Data.Generic.Rep (class Generic)
import Data.List (List(Nil), (:), concat, length, intercalate, foldl, reverse, filter, zip, range, singleton, index, take, drop, null)
import Data.Map as M
import Data.Show.Generic (genericShow)
import Data.String.CodePoints (CodePoint)
import Data.String.CodePoints as Stc
import Data.String.Common as St
import Effect (Effect)
import Effect.Console (log)

main :: Effect Unit
main = pure unit


type Str = String

infixr 5 append as ++!

strip' :: Str -> Str
strip' = St.trim

data Tree = Node Str (Maybe Str) (List Tree)

derive instance genericTree :: Generic Tree _
instance showTree :: Show Tree where
  show = toOriginal


data Error =
    NoTree    |
    MultiRoot |
    OpenPar

derive instance genericError :: Generic Error _
instance showError :: Show Error where
  show = genericShow


data End =
    Close |
    Comma |
    EOT
    
derive instance genericEnd :: Generic End _
instance showEnd :: Show End where
  show = genericShow


data Closed = Closed Tree End (List Str)
    
derive instance genericClosed :: Generic Closed _
instance showClosed :: Show Closed where
  show = genericShow


root :: (List Tree) -> End -> (List Str) -> Either Error Closed
root children reason ls =
    case children of
        Nil   -> Left NoTree
        c:Nil -> Right $ Closed c reason ls
        _     -> Left MultiRoot

readTree :: (List Str) -> Either Error Closed
readTree = go Nil
    where
        go children Nil = root children EOT Nil
        go children (l:ls) =
            case l of
                "{" -> do
                        result <- readSubTrees ls
                        go result.children result.leftstr
    
                "," -> root children Comma ls
            
                "}" -> root children Close ls
    
                str -> let splitted = splitLineOnSharp str
                       in  go (singleton(Node splitted.body splitted.rule children)) ls

splitLineOnSharp :: Str -> {body::Str, rule::Maybe Str}
splitLineOnSharp str = {body: strip' body', 
                        rule: (\r -> strip' $ r.tail) <$> Stc.uncons rule'}
    where
        body' = Stc.takeWhile (_ /= frc '#') str
        rule' = Stc.dropWhile (_ /= frc '#') str

unsplitLineOnSharp :: {body::Str, rule::Maybe Str} -> Str
unsplitLineOnSharp b = b.body ++! fromMaybe "" ((" #"++!_) <$> b.rule)

readSubTrees :: (List Str) -> Either Error {children :: (List Tree) , leftstr :: (List Str)}
readSubTrees ls = (\(Tuple c l) -> {children: reverse c, leftstr: l}) <$> go Nil ls
    where
      go ts ls =
        case readTree ls of
            Left x -> Left x
            Right (Closed t Comma ls) -> go (t:ts) ls
            Right (Closed t Close ls) -> Right (Tuple (t:ts) ls)
            Right (Closed t EOT   ls) -> Left OpenPar

toLaTeX :: Tree -> Str
toLaTeX tree = "\\begin{prooftree}\n" ++! intercalate "\n" (go tree) ++! "\n\\end{prooftree}"
    where
        go (Node body rule children) =
            let codeChildren = go =<< children

                codeRule =
                    case rule of
                        Nothing -> Nil
                        Just r  -> ("\\RightLabel{${\\scriptsize " ++! r ++! "}$}") : Nil

                bodyReplaced = replaceForLaTeX body

                codeBody =
                    case length children of
                        0 -> (     "\\AxiomC{$" ++! bodyReplaced ++! "$}") : Nil
                        1 -> (  "\\UnaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                        2 -> ( "\\BinaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                        _ -> ("\\TrinaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                        
            in  concat (codeChildren : codeRule : codeBody : Nil)

idPrefix = "node"
toHTML :: Tree -> Str
toHTML tree = go tree "" Nil
  where 
    indentunit = "  " 
    go (Node body rule parents) indents ids =
      indents ++! "<div class='subtree'>\n"  ++!
      (if length parents > 0 then
        indents ++! "<div class='parents'>\n"  ++!
        intercalate "\n" (map (\(Tuple p i) -> go p (indents ++! indentunit) (i:ids)) (zip parents (range 0 (length parents)))) ++!
        indents ++! "</div>\n"  ++!
        indents ++! "<hr>\n"  
      else "") ++!
      indents ++! "<span class='node' contenteditable='true' id='" ++! (idPrefix ++! intercalate "-" (map show $ reverse ids)) ++! "' onkeydown='key();' focusout='focusout();' >"  ++! (escapeWith ruleHTMLChars $ unsplitLineOnSharp {body:body,rule:rule}) ++! "</span>\n" ++!
      --indents ++! "<input class='node' placeholder='_' id='" ++! (idPrefix ++! intercalate "-" (map show $ reverse ids)) ++! "' onkeydown='key();' focusout='focusout();' value='"  ++! (\s -> if s == "_" then "" else escapeWith ruleHTMLChars s) (unsplitLineOnSharp {body:body,rule:rule}) ++! "'>\n" ++!
      indents ++! "</div>\n"

ifEmpty instead str = if str == "" then instead else str

toOriginal :: Tree -> Str
toOriginal tree = go tree ""
  where
    indentunit = "  "
    go (Node body rule Nil) indents =
      indents ++! unsplitLineOnSharp {body:ifEmpty "_" body,rule:rule}
    
    go (Node body rule (parent:Nil)) indents =
      go parent indents ++! "\n" ++!
      indents ++! unsplitLineOnSharp {body:ifEmpty "_" body,rule:rule}
    
    go (Node body rule parents) indents =
      indents ++! "{\n" ++!
      intercalate ("\n" ++! indents ++! ",\n") (map (\p -> go p (indents ++! indentunit)) parents) ++! "\n" ++!
      indents ++! "}\n" ++!
      indents ++! unsplitLineOnSharp {body:ifEmpty "_" body,rule:rule}

_tryrewriteTreeWithIndex :: Tree -> Array Int -> Str -> Tree
_tryrewriteTreeWithIndex oldtree ixarr newbody = go (A.toUnfoldable ixarr) newbody oldtree
  where 
    go Nil nb (Node _ _ ps) = 
      let sp = splitLineOnSharp nb
      in  Node sp.body sp.rule ps
    
    go (i:is) nb (Node ob or ps) =
      Node ob or (modifyNth i (go is nb) ps)

_tryAddParentRightWithIndex :: Tree -> Array Int -> Tree
_tryAddParentRightWithIndex oldtree ixarr = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil (Node ob or ps) = 
      Node ob or (ps ++! (singleton $ Node "" Nothing Nil))
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryAddParentLeftWithIndex :: Tree -> Array Int -> Tree
_tryAddParentLeftWithIndex oldtree ixarr = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil (Node ob or ps) = 
      Node ob or (Node "" Nothing Nil : ps)
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryDelWithIndex :: Tree -> Array Int -> Boolean -> Tree
_tryDelWithIndex oldtree ixarr forceDel = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil x = x

    go (i:Nil) (Node ob or ps) = 
      Node ob or (removeNthIf (\(Node _ _ p) -> null p || forceDel) i ps)
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_addChild :: Tree -> Tree
_addChild oldtree = Node "" Nothing (singleton oldtree)

_killEmptySubTrees :: Tree -> Tree
_killEmptySubTrees (Node body rule children) = 
  Node body rule (filter (
      \child -> 
        case child of
          Node "" Nothing Nil -> false
          x                   -> true
    ) children)


_isAxiom :: Tree -> Array Int -> Boolean
_isAxiom tree ixarr = go (A.toUnfoldable ixarr) tree
  where 
    go Nil    (Node _ _ Nil) = true
    go Nil    (Node _ _ _)   = false
    go (i:is) (Node _ _ ps)  = fromMaybe true (go is <$> index ps i)

_countChildren :: Tree -> Array Int -> Int
_countChildren tree ixarr = go (A.toUnfoldable ixarr) tree
  where 
    go Nil    (Node _ _ ps) = length ps
    go (i:is) (Node _ _ ps) = fromMaybe 0 (go is <$> index ps i)

_getContentOfId :: Tree -> Array Int -> Str
_getContentOfId tree ixarr = go (A.toUnfoldable ixarr) tree
  where 
    go Nil    (Node body rule ps) = unsplitLineOnSharp {body:body,rule:rule}
    go (i:is) (Node body rule ps) = fromMaybe "" (go is <$> index ps i)

strToMappedTree :: Str -> (Tree -> Tree) -> Str
strToMappedTree str f = 
  case parseFromStr str of
    Left error             -> show error
    Right (Closed t EOT _) -> toOriginal $ f t
    Right _                -> "{ is not closed"

addChild                   s     = strToMappedTree s _addChild
killEmptySubTrees          s     = strToMappedTree s _killEmptySubTrees
tryDelWithIndex            s i f = strToMappedTree s (\t -> _tryDelWithIndex            t i f)
tryAddParentRightWithIndex s i   = strToMappedTree s (\t -> _tryAddParentRightWithIndex t i)
tryAddParentLeftWithIndex  s i   = strToMappedTree s (\t -> _tryAddParentLeftWithIndex  t i)
tryrewriteTreeWithIndex    s i b = strToMappedTree s (\t -> _tryrewriteTreeWithIndex    t i b)

strToConvertedStr :: (Tree -> Str) -> Str -> Str
strToConvertedStr tostr str = 
  case parseFromStr str of
    Left error             -> show error
    Right (Closed t EOT _) -> tostr t
    Right _                -> "{ is not closed"

strToHTML     = strToConvertedStr toHTML
strToLaTeX    = strToConvertedStr toLaTeX
strToOriginal = strToConvertedStr toOriginal


strToConvertedA :: forall a. (Tree -> a) -> Str -> a -> a
strToConvertedA f str default = 
  case parseFromStr str of
    Left  _                -> default
    Right (Closed t EOT _) -> f t
    Right _                -> default

isAxiom        s i = strToConvertedA (\t -> _isAxiom t i) s false
countChildren  s i = strToConvertedA (\t -> _countChildren t i) s 0
getContentOfId s i = strToConvertedA (\t -> _getContentOfId t i) s ""


modifyNth :: forall a. Int -> (a -> a) -> List a -> List a
modifyNth i f l = 
  case index l i of
    Just e  -> take i l ++! singleton (f e) ++! drop (i+1) l
    Nothing -> l

removeNthIf :: forall a. (a -> Boolean) -> Int -> List a -> List a
removeNthIf _ _ Nil = Nil
removeNthIf f 0 (x:xs) = if f x then xs else x:xs
removeNthIf f n (x:xs) = x : removeNthIf f (n-1) xs

replaceForLaTeX :: Str -> Str
replaceForLaTeX = replaceUnderbarNumToBlaced <<< escapeWith ruleLaTeXChars

escapeWith  :: M.Map CodePoint Str -> Str -> Str
escapeWith rule str = 
    foldl (\s (Tuple from to)->
                Stc.fromCodePointArray $ Stc.toCodePointArray s >>= (\c -> Stc.toCodePointArray (if c == from then to ++! " " else Stc.singleton c))
            ) str (M.toUnfoldable rule :: List (Tuple CodePoint Str))

replaceUnderbarNumToBlaced :: Str -> Str
replaceUnderbarNumToBlaced str = go str ""
  where
    go s done =
      let ml = Stc.uncons s
      in  case ml of
            Nothing -> done
            Just l ->
              if l.head == frc '_' then
                if Stc.length (Stc.takeWhile isNumber l.tail) > 0 then
                  go (Stc.dropWhile isNumber l.tail) $ done ++! ("_{" ++! Stc.takeWhile isNumber l.tail ++! "}")
                else
                  go (Stc.dropWhile isNumber l.tail) $ done ++! "_"
              else
                go l.tail (done ++! Stc.singleton l.head)

parseFromStr :: String -> Either Error Closed
parseFromStr str = readTree $ map strip' $ A.toUnfoldable $ St.split (Pattern "\n") str

frc :: Char -> CodePoint
frc = Stc.codePointFromChar

fsc :: String -> Maybe CodePoint
fsc = Stc.codePointAt 0

ruleHTMLChars :: M.Map CodePoint Str
ruleHTMLChars = 
    M.fromFoldable $ [
        Tuple (frc '&') "&amp;",
        Tuple (frc '<') "&lt;",
        Tuple (frc '>') "&gt;",
        Tuple (frc '"') "&quot;",
        Tuple (frc ''') "&#39;"
    ]

ruleLaTeXChars :: M.Map CodePoint Str
ruleLaTeXChars =
    M.fromFoldable $ [
        Tuple (frc '∀') "\\forall",
        Tuple (frc '∈') "\\in",
        Tuple (frc '├') "\\vdash",
        Tuple (frc '≈') "\\approx",
        Tuple (frc '⊥') "\\bot",
        Tuple (frc '→') "\\to",
        Tuple (frc '¬') "\\lnot",
        Tuple (frc '∧') "\\land",
        Tuple (frc '∨') "\\lor",
        Tuple (frc 'α') "\\alpha",
        Tuple (frc 'β') "\\beta",
        Tuple (frc 'γ') "\\gamma",
        Tuple (frc 'δ') "\\delta",
        Tuple (frc 'ϵ') "\\epsilon",
        Tuple (frc 'ε') "\\varepsilon",
        Tuple (frc 'ζ') "\\zeta",
        Tuple (frc 'η') "\\eta",
        Tuple (frc 'θ') "\\theta",
        Tuple (frc 'ϑ') "\\vartheta",
        Tuple (frc 'ι') "\\iota",
        Tuple (frc 'κ') "\\kappa",
        Tuple (frc 'λ') "\\lambda",
        Tuple (frc 'μ') "\\mu",
        Tuple (frc 'ν') "\\nu",
        Tuple (frc 'ξ') "\\xi",
        Tuple (frc 'π') "\\pi",
        Tuple (frc 'ϖ') "\\varpi",
        Tuple (frc 'ρ') "\\rho",
        Tuple (frc 'ϱ') "\\varrho",
        Tuple (frc 'σ') "\\sigma",
        Tuple (frc 'ς') "\\varsigma",
        Tuple (frc 'τ') "\\tau",
        Tuple (frc 'υ') "\\upsilon",
        Tuple (frc 'ϕ') "\\phi",
        Tuple (frc 'φ') "\\varphi",
        Tuple (frc 'χ') "\\chi",
        Tuple (frc 'ψ') "\\psi",
        Tuple (frc 'ω') "\\omega",
        Tuple (frc 'Γ') "\\Gamma",
        Tuple (frc 'Λ') "\\Lambda",
        Tuple (frc 'Σ') "\\Sigma",
        Tuple (frc 'Ψ') "\\Psi",
        Tuple (frc 'Δ') "\\Delta",
        Tuple (frc 'Ξ') "\\Xi",
        Tuple (frc 'Υ') "\\Upsilon",
        Tuple (frc 'Ω') "\\Omega",
        Tuple (frc 'Θ') "\\Theta",
        Tuple (frc 'Π') "\\Pi",
        Tuple (frc 'Φ') "\\Phi"
    ] ++! A.mapMaybe (\(Tuple ma b) -> (\a-> Tuple a b) <$> ma) [
      Tuple (fsc "𝒫") "\\mathcal{P}"
    ]
