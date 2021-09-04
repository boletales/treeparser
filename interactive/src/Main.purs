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
import Data.List (List(Nil), (:), head, elem, concat, length, intercalate, foldl, foldr, reverse, filter, zip, range, singleton, index, take, drop, null, snoc, mapMaybe)
import Data.List.Lazy (Pattern)
import Data.Map as M
import Data.Set as S
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

cons :: forall a. a -> List a -> List a
cons a b = a : b

strip' :: Str -> Str
strip' = St.trim

data Tree = 
  Node Str (Maybe Str) (List Tree)
  --Import Str

derive instance genericTree :: Generic Tree _
instance showTree :: Show Tree where
  show = toOriginal


data Error =
    NoTree    |
    MultiRoot |
    OpenPar   |
    MultiDef Str

derive instance genericError :: Generic Error _
instance showError :: Show Error where
  show = genericShow


data End =
    Close  |
    Comma  |
    EOT    |
    SubRoot Str
    
derive instance genericEnd :: Generic End _
instance showEnd :: Show End where
  show = genericShow


data Closed = Closed Tree End (List Str)
    
derive instance genericClosed :: Generic Closed _
instance showClosed :: Show Closed where
  show = genericShow

type Trees = M.Map Str CommentedTree
type CommentedTree = {tree:: Tree, comment:: Str}

readComment :: Tree -> CommentedTree
readComment tree = go Nil tree
  where
    end cs t = {tree: t, comment: (intercalate "\n" $ cs)}
    go cs (Node b r (p:Nil)) =
      let l = unsplitLineOnSharp {body: b, rule:r}
      in case Stc.stripPrefix (Pattern "//") l of
            Just c  -> go (c:cs) p
            Nothing -> end cs p

    go cs t = end cs t

parseFromStrToTree :: String -> Either Error Closed
parseFromStrToTree str = readTree $ map strip' $ A.toUnfoldable $ St.split (Pattern "\n") str

rootname :: Str
rootname = "root"

parseFromStrToTrees :: Str -> Either Error Trees
parseFromStrToTrees str = go (A.toUnfoldable $ St.split (Pattern "\n") str) M.empty
  where
    go lines trees = 
      case readTree $ map strip' lines of
        Left e -> Left e
        Right (Closed t (SubRoot sr) ls) -> 
          if M.member sr trees || sr == rootname then
            Left (MultiDef sr)
          else
            go ls (M.insert sr (readComment t) trees)
        
        Right (Closed t EOT ls) -> Right (M.insert rootname (readComment t) trees)
        Right _                 -> Left OpenPar

root :: (List Tree) -> End -> (List Str) -> Either Error Closed
root parents reason ls =
    case parents of
        Nil   -> Left NoTree
        c:Nil -> Right $ Closed c reason ls
        _     -> Left MultiRoot

readTree :: (List Str) -> Either Error Closed
readTree = go Nil
  where
    go parents Nil = root parents EOT Nil
    go parents (l:ls) =
      case l of
        ""  -> go parents ls
        "{" -> do
                result <- readBranches ls
                go result.parents result.leftstr

        "," -> root parents Comma ls
    
        "}" -> root parents Close ls

        str -> let splitted = splitLineOnSharp str
                in  case isSubRoot str of
                      Just sr -> root parents (SubRoot sr) ls
                      Nothing -> go (singleton(Node splitted.body splitted.rule parents)) ls

readBranches :: (List Str) -> Either Error {parents :: (List Tree) , leftstr :: (List Str)}
readBranches ls = (\(Tuple c l) -> {parents: reverse c, leftstr: l}) <$> go Nil ls
    where
      go ts ls =
        case readTree ls of
            Left x -> Left x
            Right (Closed t Comma       l) -> go (t:ts) l
            Right (Closed t Close       l) -> Right (Tuple (t:ts) l)
            Right (Closed t (SubRoot _) l) -> Left OpenPar
            Right (Closed t EOT         l) -> Left OpenPar

isSubRoot :: Str -> Maybe Str
isSubRoot str = Stc.stripPrefix (Pattern "@") $ strip' str

isImport :: Str -> Maybe Str
isImport str = Stc.stripPrefix (Pattern "$") $ strip' str

splitLineOnSharp :: Str -> {body::Str, rule::Maybe Str}
splitLineOnSharp str = {body: strip' body', 
                        rule: (\r -> strip' $ r.tail) <$> Stc.uncons rule'}
    where
        body' = Stc.takeWhile (_ /= frc '#') str
        rule' = Stc.dropWhile (_ /= frc '#') str

unsplitLineOnSharp :: {body::Str, rule::Maybe Str} -> Str
unsplitLineOnSharp b = b.body ++! fromMaybe "" ((" #"++!_) <$> b.rule)


modifyNth :: forall a. Int -> (a -> a) -> List a -> List a
modifyNth i f l = 
  case index l i of
    Just e  -> take i l ++! singleton (f e) ++! drop (i+1) l
    Nothing -> l

removeNthIf :: forall a. (a -> Boolean) -> Int -> List a -> List a
removeNthIf _ _ Nil = Nil
removeNthIf f 0 (x:xs) = if f x then xs else x:xs
removeNthIf f n (x:xs) = x : removeNthIf f (n-1) xs

getBranchById :: Array Int -> Tree -> Maybe Tree
getBranchById id tree = go (A.toUnfoldable id) tree
  where 
    go Nil x = Just x
    go (i:is) (Node ob or ps) = (go is =<< index ps i)

_tryModifyTreeWithIndex :: Array Int -> Tree -> Tree -> Tree
_tryModifyTreeWithIndex ixarr newbranch oldtree = go (A.toUnfoldable ixarr) newbranch oldtree
  where 
    go Nil nb _ = nb
    
    go (i:is) nb (Node ob or ps) =
      Node ob or (modifyNth i (go is nb) ps)

_tryRewriteTreeWithIndex :: Array Int -> Str -> Tree -> Tree
_tryRewriteTreeWithIndex ixarr newbody oldtree = go (A.toUnfoldable ixarr) newbody oldtree
  where 
    -- go _ _ (Import tree) = (Import tree)

    go (i:Nil) "" (Node ob or ps) = 
      Node ob or (removeNthIf 
        (\t -> case t of
                  (Node _ _ p) -> null p
                  _  -> false
                ) i ps)

    go Nil nb (Node _ _ ps) = 
      let sp = splitLineOnSharp nb
          default = Node sp.body sp.rule ps
      in  if null ps && Stc.contains (Pattern "\n") nb then
            case parseFromStrToTree nb of
              Right (Closed t EOT Nil) -> t
              Right _ -> default
              Left  _ -> default
          else
            default
    
    go (i:is) nb (Node ob or ps) =
      Node ob or (modifyNth i (go is nb) ps)

_tryAddParentRightWithIndex :: Array Int -> Tree -> Tree
_tryAddParentRightWithIndex ixarr oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil (Node ob or ps) = 
      Node ob or (ps ++! (singleton $ Node "" Nothing Nil))
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryAddParentLeftWithIndex :: Array Int -> Tree -> Tree
_tryAddParentLeftWithIndex ixarr oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil (Node ob or ps) = 
      Node ob or (Node "" Nothing Nil : ps)
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryDelWithIndex :: Array Int -> Boolean -> Tree -> Tree
_tryDelWithIndex ixarr forceDel oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil x = x

    -- go _ (Import a) = Import a

    go (i:Nil) (Node ob or ps) = 
      Node ob or (removeNthIf (\(Node _ _ p) -> null p || forceDel) i ps)
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryRuinWithIndex :: Array Int -> Tree -> Tree
_tryRuinWithIndex ixarr oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil x = Node "" Nothing Nil

    -- go _ (Import a) = Import a
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryInsertWithIndex :: Array Int -> Tree -> Tree
_tryInsertWithIndex ixarr oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil x = 
      Node "" Nothing (singleton x)
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_trySquashWithIndex :: Array Int -> Tree -> Tree
_trySquashWithIndex ixarr oldtree = go (A.toUnfoldable ixarr) oldtree
  where 
    go Nil (Node _ _ (p:Nil)) = p

    go Nil x = x
    
    go (i:is) (Node ob or ps) =
      Node ob or (modifyNth i (go is) ps)

_tryMakeNewSubTree :: Tree -> Trees -> (Tuple Str Trees)
_tryMakeNewSubTree tree dict = go 1
  where 
    name i = "subtree" ++! show i
    go i =
      if M.member (name i) dict then
        go (i+1)
      else
        Tuple (name i) (M.insert (name i) {tree:tree, comment:""} dict)

_tryMakeEmptySubTree :: Trees -> Trees
_tryMakeEmptySubTree = snd <<< _tryMakeNewSubTree (Node "" Nothing Nil)

_tryMakeBranchSubTree :: Str -> Array Int -> Trees -> Trees
_tryMakeBranchSubTree name id dict = 
  case M.lookup name dict of
    Nothing   -> dict
    Just tc -> 
      case getBranchById id tc.tree of
        Nothing     -> dict
        Just branch -> (\(Tuple newname newdict) -> M.insert name (applyToTree (_tryRewriteTreeWithIndex id ("$"++!newname)) tc) newdict) $ _tryMakeNewSubTree branch dict

_tryApplyToAllTrees :: (Str -> Str) -> Trees -> Trees
_tryApplyToAllTrees f dict = M.mapMaybe (pure <$> applyToTree go) dict
  where
    go (Node body rule ps) = Node (f body) rule (map go ps)

_tryRenameSubTree :: Str -> Str -> Trees -> Trees
_tryRenameSubTree from to dict =
  if from == rootname then
    dict
  else
    case M.lookup from dict of
      Nothing   -> dict
      Just tree -> 
        case M.lookup to dict of
          Just _  -> dict
          Nothing -> _tryApplyToAllTrees (\b -> if isImport b == Just from then "$"++!to else b) $ M.insert to tree $ M.delete from dict

_tryDeleteSubTree :: Boolean -> Str -> Trees -> Trees
_tryDeleteSubTree force name dict =
  if name == rootname then
    dict
  else
    case M.lookup name dict of
      Just {tree:(Node _ _ Nil), comment:_} -> M.delete name dict
      Just {tree:(Node _ _ _)  , comment:_} -> if force then M.delete name dict else dict
      _                   -> dict

_tryInline :: Str -> Array Int -> Trees -> Trees
_tryInline name id dict = fromMaybe dict (do
    tc <- M.lookup name dict
    (Node b _ _) <- getBranchById id tc.tree
    i  <- isImport b
    it <- M.lookup i dict
    Just $ M.insert name (applyToTree (_tryModifyTreeWithIndex id it.tree) tc) dict
  )

_addChild :: Tree -> Tree
_addChild oldtree = Node "" Nothing (singleton oldtree)

_killEmptyBranches :: Tree -> Tree
_killEmptyBranches (Node body rule parents) = 
  Node body rule (filter (
      \child -> 
        case child of
          Node "" Nothing Nil -> false
          x                   -> true
    ) parents)




_countParents :: Array Int -> Tree -> Int
_countParents ixarr tree = fromMaybe 0 ((\(Node _ _ ps) -> length ps) <$> getBranchById ixarr tree)

_isNodeAxiom :: Array Int -> Tree -> Boolean
_isNodeAxiom ixarr tree =
  case getBranchById ixarr tree of 
    Just (Node _ _ Nil) -> true
    _                   -> false

_isNodeImport :: Array Int -> Tree -> {isImport:: Boolean, importOf:: Str}
_isNodeImport ixarr tree =
  case getBranchById ixarr tree of 
    Just (Node b _ Nil) -> maybe {isImport: false, importOf: ""} (\s -> {isImport: true, importOf: s}) (isImport b)
    _                   -> {isImport: false, importOf: ""}
  

_getContentWithIndex :: Array Int -> Tree -> Str
_getContentWithIndex ixarr tree = 
  case getBranchById ixarr tree of 
    Just (Node body rule ps) -> unsplitLineOnSharp {body:body,rule:rule}
    _                        -> ""

_branchToString :: Array Int -> Tree -> Str
_branchToString ixarr tree = 
  case getBranchById ixarr tree of 
    Just x -> toOriginal x
    _      -> ""

strToMappedTree :: Str -> (Tree -> Tree) -> Str
strToMappedTree str f = 
  case parseFromStrToTree str of
    Left error             -> show error
    Right (Closed t EOT _) -> toOriginal $ f t
    Right _                -> "{ is not closed"

strToMappedTrees :: Str -> (Trees -> Trees) -> Str
strToMappedTrees str f = 
  case parseFromStrToTrees str of
    Left error -> show error
    Right m    -> treesToOriginal $ f m

applyToTree :: (Tree -> Tree) -> (CommentedTree -> CommentedTree)
applyToTree f tc = {tree:f tc.tree, comment: tc.comment}

applyToTrees :: Str -> (Tree -> Tree) -> (Trees -> Trees)
applyToTrees n f = M.alter (map (applyToTree f)) n

addChild                   str name      = strToMappedTrees str $ applyToTrees name $ _addChild
killEmptyBranches          str name      = strToMappedTrees str $ applyToTrees name $ _killEmptyBranches
tryRuinWithIndex           str name id   = strToMappedTrees str $ applyToTrees name $ _tryRuinWithIndex           id  
tryDelWithIndex            str name id f = strToMappedTrees str $ applyToTrees name $ _tryDelWithIndex            id f
tryAddParentRightWithIndex str name id   = strToMappedTrees str $ applyToTrees name $ _tryAddParentRightWithIndex id  
tryAddParentLeftWithIndex  str name id   = strToMappedTrees str $ applyToTrees name $ _tryAddParentLeftWithIndex  id  
tryRewriteTreeWithIndex    str name id b = strToMappedTrees str $ applyToTrees name $ _tryRewriteTreeWithIndex    id b
tryInsertWithIndex         str name id   = strToMappedTrees str $ applyToTrees name $ _tryInsertWithIndex         id
trySquashWithIndex         str name id   = strToMappedTrees str $ applyToTrees name $ _trySquashWithIndex         id
tryMakeBranchSubTree       str name id   = strToMappedTrees str $ _tryMakeBranchSubTree name id
tryRenameSubTree           str from to   = strToMappedTrees str $ _tryRenameSubTree from to
tryDeleteSubTree           str name f    = strToMappedTrees str $ _tryDeleteSubTree f name
tryMakeEmptySubTree        str           = strToMappedTrees str $ _tryMakeEmptySubTree
tryCleanSubTrees           str f         = strToMappedTrees str $ \dict -> foldr (_tryDeleteSubTree f) dict (M.keys dict)
tryInline                  str name id   = strToMappedTrees str $ _tryInline name id
tryRewriteComment          str name c    = strToMappedTrees str $ M.alter (map (\tc -> {tree:tc.tree, comment:c})) name

strToConvertedA :: forall a. (Tree -> a) -> Str -> Str -> a -> a
strToConvertedA f str id default = 
  case (M.lookup id) <$> parseFromStrToTrees str of
    Left  _        -> default
    Right Nothing  -> default
    Right (Just t) -> f t.tree

isNodeAxiom         s t i = strToConvertedA (_isNodeAxiom         i) s t false
isNodeImport        s t i = strToConvertedA (_isNodeImport        i) s t {isImport: false, importOf: ""}
countParents        s t i = strToConvertedA (_countParents        i) s t 0
getContentWithIndex s t i = strToConvertedA (_getContentWithIndex i) s t ""
branchToString      s t i = strToConvertedA (_branchToString      i) s t ""
getComment          s t   = either (const "") (\dict -> maybe "" (\tc -> tc.comment) (M.lookup t dict)) (parseFromStrToTrees s)
getSubTrees         s     = either (const []) (A.fromFoldable <<< getTreesName_rootFirst) (parseFromStrToTrees s)

strToConvertedStr :: (Tree -> Str) -> Str -> Str
strToConvertedStr tostr str = 
  case parseFromStrToTree str of
    Left error             -> show error
    Right (Closed t EOT _) -> tostr t
    Right _                -> "{ is not closed"

strToHTML     s t = (either show (subTreeToHTML t) <<< parseFromStrToTrees) s 
strToLaTeX    s   = (either show toLaTeX           <<< parseFromStrToTrees) s
strToOriginal s   = (strToConvertedStr toOriginal) s

toLaTeX :: Trees -> Str
toLaTeX dict = 
  case M.lookup rootname dict of
    Nothing   -> "No root tree."
    Just tc -> "\\begin{prooftree}\n" ++! intercalate "\n" (go (singleton rootname) tc.tree) ++! "\n\\end{prooftree}"
      where
        go imported (Node body rule parents)=
            case isImport body of
              Just i -> 
                if elem i imported then
                  singleton $ "circular reference of " ++! i
                else case M.lookup i dict of
                        Nothing -> singleton $ "no tree named " ++! i
                        Just t  -> go (i:imported) t.tree
              Nothing ->
                let codeParents = (go imported) =<< parents

                    codeRule =
                        case rule of
                            Nothing -> Nil
                            Just r  -> ("\\RightLabel{${\\scriptsize " ++! r ++! "}$}") : Nil

                    bodyReplaced = replaceForLaTeX body

                    codeBody =
                        case length parents of
                            0 -> (     "\\AxiomC{$" ++! bodyReplaced ++! "$}") : Nil
                            1 -> (  "\\UnaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                            2 -> ( "\\BinaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                            _ -> ("\\TrinaryInfC{$" ++! bodyReplaced ++! "$}") : Nil
                            
                in  concat (codeParents : codeRule : codeBody : Nil)

idPrefix :: Str
idPrefix = "node"

idPrefix_label :: Str
idPrefix_label = "rightlabel"

idPrefix_import :: Str
idPrefix_import = "import"

idPrefix_check :: Str
idPrefix_check = "show"

subTreeToHTML :: Str -> Trees -> Str
subTreeToHTML name dict = -- go tree "" Nil
  case M.lookup name dict of
    Nothing   -> "No such tree."
    Just tc -> go (singleton name) tc.tree "" Nil (escapeWith ruleIDChars $ name)
      where
        indentunit = "  " 
        go imported (Node body rule parents) indents ids log=
          case isImport body of
            Just i -> 
              if elem i imported then
                "circular reference of " ++! i
              else
                indents ++! "<div class='branch'>\n"  ++!(
                  case M.lookup i dict of
                    Nothing -> "[tree not found: " ++! escapeWith ruleHTMLChars i ++! "]<br>" ++!
                      indents ++! "<span class='node editable' contenteditable='true' id='" 
                        ++! (idPrefix ++! "_" ++! log)
                        ++! "' onkeydown='key();' onfocusout='focusout();' >"  ++! (escapeWith ruleHTMLChars $ unsplitLineOnSharp {body:body,rule:rule}) ++! "</span>\n" ++!
                      indents ++! "<span class='rightlabel editable' contenteditable='true' id='" 
                        ++! (idPrefix_label  ++! "_" ++! log)
                        ++! "' onkeydown='key();' onfocusout='focusout();' >"  ++!  "</span>\n"

                    Just tc ->
                      indents ++! "<input type='checkbox' id='" 
                        ++! (idPrefix_check ++! "_" ++! log)
                        ++! "' class='treeswitch'>\n" ++!
                      indents ++! "<div class='parents imported'>\n" ++!
                      go (i:imported) tc.tree (indents ++! indentunit) Nil (log ++! "_" ++! escapeWith ruleIDChars i) ++!
                      indents ++! "</div>\n"  ++!
                      indents ++! "<span class='node editable' contenteditable='true' id='" 
                        ++! (idPrefix ++! "_" ++! log)
                        ++! "' onkeydown='key();' onfocusout='focusout();' >"  ++! (escapeWith ruleHTMLChars $ unsplitLineOnSharp {body:body,rule:rule}) ++! "</span>\n" ++!
                      indents ++! "<span class='rightlabel editable' contenteditable='true' id='" 
                        ++! (idPrefix_label  ++! "_" ++! log)
                        ++! "' onkeydown='key();' onfocusout='focusout();' >"  ++!  "</span>\n" ++!
                      indents ++! "<span type='checkbox'>\n" ++!
                      indents ++! "<label type='checkbox' for='" 
                        ++! (idPrefix_check ++! "_" ++! log)
                        ++! "' class='switchlabel'>↑</label>\n" ++!
                      indents ++! "<div class='omitted'>\n" ++!
                      escapeWith ruleHTMLChars ((\(Node b _ _) -> b) tc.tree) ++!
                      indents ++! "</div>\n"++!
                      indents ++! "</span>\n"
                ) ++!
                indents ++! "</div>\n"
            
            Nothing ->
              indents ++! "<div class='branch'>\n"  ++!
              (if length parents > 0 then
                indents ++! "<div class='parents'>\n"  ++!
                intercalate "\n" (map (\(Tuple p i) -> go imported p (indents ++! indentunit) (i:ids) (log ++! "-" ++! show i)) (zip parents (range 0 (length parents)))) ++!
                indents ++! "</div>\n"  ++!
                indents ++! "<hr class='proofline'>\n"  
              else "") ++!
              indents ++! "<span class='rightlabel editable' contenteditable='true' id='" 
                ++! (idPrefix_label  ++! "_" ++! log)
                ++! "' onkeydown='key();' onfocusout='focusout();' >"  ++! (escapeWith ruleHTMLChars $ fromMaybe "" rule) ++! "</span>\n" ++!
              indents ++! "<span class='node editable' contenteditable='true' id='" 
                ++! (idPrefix  ++! "_" ++! log)
                ++! "' onkeydown='key();' onfocusout='focusout();'>"  ++! (escapeWith ruleHTMLChars $ body) ++! "</span>\n" ++!
              indents ++! "</div>\n"

ifEmpty :: Str -> Str -> Str
ifEmpty instead str = if str == "" then instead else str

placeHolder = "_"

toOriginal :: Tree -> Str
toOriginal tree = go tree ""
  where
    indentunit = "  "
    -- go (Import name) indents =
    --   indents ++! "$" ++! name

    go (Node body rule Nil) indents =
      indents ++! unsplitLineOnSharp {body:ifEmpty placeHolder body,rule:rule}
    
    go (Node body rule (parent:Nil)) indents =
      go parent indents ++! "\n" ++!
      indents ++! unsplitLineOnSharp {body:ifEmpty placeHolder body,rule:rule}
    
    go (Node body rule parents) indents =
      indents ++! "{\n" ++!
      intercalate ("\n" ++! indents ++! ",\n") (map (\p -> go p (indents ++! indentunit)) parents) ++! "\n" ++!
      indents ++! "}\n" ++!
      indents ++! unsplitLineOnSharp {body:ifEmpty placeHolder body,rule:rule}

treesToOriginal :: Trees -> Str
treesToOriginal dict =
  intercalate "\n" $ mapMaybe (\k -> (\tc -> toOriginal tc.tree ++! intercalate "" (map ("\n//" ++! _) (St.split (Pattern "\n") tc.comment)) ++! if k == rootname then "" else ("\n@" ++! k ++! "\n\n")) <$> M.lookup k dict) $ getTreesName_rootLast dict

getTreesName_rootFirst :: Trees -> List Str
getTreesName_rootFirst dict =      cons rootname (S.toUnfoldable $ (S.filter (_ /= rootname)) (M.keys dict))

getTreesName_rootLast :: Trees -> List Str
getTreesName_rootLast  dict = flip snoc rootname (S.toUnfoldable $ (S.filter (_ /= rootname)) (M.keys dict))

replaceForLaTeX :: Str -> Str
replaceForLaTeX = replaceUnderbarNumToBlaced <<< escapeWith ruleLaTeXChars

escapeWith  :: M.Map CodePoint Str -> Str -> Str
escapeWith rule str = 
    foldl (\s (Tuple from to)->
                Stc.fromCodePointArray $ Stc.toCodePointArray s >>= (\c -> Stc.toCodePointArray (if c == from then to else Stc.singleton c))
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

      

frc :: Char -> CodePoint
frc = Stc.codePointFromChar

fsc :: String -> Maybe CodePoint
fsc = Stc.codePointAt 0

ruleIDChars :: M.Map CodePoint Str
ruleIDChars = 
    M.fromFoldable $ [
        Tuple (frc '\\') "\\\\",
        Tuple (frc '-') "\\h",
        Tuple (frc '_') "\\u"
    ]

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
    map (_ ++! " ") $ M.fromFoldable $ [
        Tuple (frc '$') "\\$",
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
