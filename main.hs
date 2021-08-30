import Data.Char
import Data.List
import System.Exit
import Data.Bifunctor
import System.Environment (getArgs)
import qualified Data.Map as M
import qualified Data.Set as S

type Str = String

(++!) :: Str -> Str -> Str
(++!) = (++)

strip' :: Str -> Str
strip' = f.f
    where f = reverse . dropWhile isSpace

data Tree = Node Str (Maybe Str) [Tree] deriving (Show,Eq)
data Error =
    NoTree    |
    MultiRoot |
    OpenPar deriving (Show,Eq)

data End =
    Close |
    Comma |
    EOT deriving (Show,Eq)

type Closed = (Tree,End,[Str])

main = do
    args <- getArgs
    fileToMathJaxHTML (head args)

root :: [Tree] -> End -> [Str] -> Either Error Closed
root children reason ls =
    case children of
        []  -> Left NoTree
        [c] -> Right (c,reason,ls)
        cs  -> Left MultiRoot

readTree :: [Str] -> Either Error Closed
readTree = go []
    where
        go children [] = root children EOT []
        go children (l:ls) =
            case l of
                "{" -> do
                        (subtrees,ls') <- readSubTrees ls
                        go subtrees ls'
    
                "," -> root children Comma ls
            
                "}" -> root children Close ls
    
                str -> let (body,rule) = splitLineOnSharp str
                       in  go [Node body rule children] ls

readSubTrees :: [Str] -> Either Error ([Tree], [Str])
readSubTrees ls = first reverse <$> go [] ls
    where
      go ts ls =
        case readTree ls of
            Left x -> Left x
            Right (t,Comma,ls) -> go (t:ts) ls
            Right (t,Close,ls) -> Right (t:ts,ls)
            Right (t,EOT,ls)   -> Left OpenPar

splitLineOnSharp :: Str -> (Str, Maybe Str)
splitLineOnSharp str = (strip' body', if null rule' then Nothing else Just (strip' $ tail rule'))
    where
        (body',rule') = (takeWhile (/='#') str, dropWhile (/='#') str)

toLaTeX :: Tree -> Str
toLaTeX tree = "\\begin{prooftree}\n" ++! intercalate "\n" (go tree) ++! "\n\\end{prooftree}"
    where
        go (Node body rule children) =
            let codeChildren = go =<< children

                codeRule =
                    case rule of
                        Nothing -> []
                        Just r  -> ["\\RightLabel{${\\scriptsize " ++! r ++! "}$}"]

                bodyReplaced = replaceForLaTeX body

                codeBody =
                    case length children of
                        0 -> [     "\\AxiomC{$" ++! bodyReplaced ++! "$}"]
                        1 -> [  "\\UnaryInfC{$" ++! bodyReplaced ++! "$}"]
                        2 -> [ "\\BinaryInfC{$" ++! bodyReplaced ++! "$}"]
                        _ -> ["\\TrinaryInfC{$" ++! bodyReplaced ++! "$}"]
                        
            in concat [codeChildren, codeRule, codeBody]


toMathJaxHTML :: Tree -> Str
toMathJaxHTML tree = intercalate "\n"
    [
        "<html>",
        "<head>",
        "<script type='text/javascript' id='MathJax-script' async",
        "src='https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js'></script>",
        "<title>result</title>",
        "</head>",
        "<body>",
        toLaTeX tree,
        "</body>",
        "</html>"
    ]
replaceForLaTeX = replaceUnderbarNumToBlaced.replaceSingleCharForLaTeX

replaceSingleCharForLaTeX str = 
    foldl (\s (from,to)->
                s >>= (\c -> if c == from then to++" " else [c])
            ) str (M.assocs ruleLaTeXChars)

replaceUnderbarNumToBlaced str = go str ""
    where
        go ('_':l) done =
            go (dropWhile isNumber l) $ reverse ("_{" ++ takeWhile isNumber l ++ "}") ++ done
        go (x:l) done = go l (x:done) 
        go "" done = reverse done 


parseFromStr :: String -> Either Error Closed
parseFromStr str = readTree $ map strip' $ lines str

parseFromFile :: FilePath -> IO (Either Error Closed)
parseFromFile path = parseFromStr <$> readFile path

fileToLaTeX :: FilePath -> IO ()
fileToLaTeX path = do
    str <- loadFile path
    case parseFromStr str of
        Left a  -> print (show a)
        Right (t,e,l) ->
            case e of
                EOT -> writeFile (path ++ "_tex.txt") (toLaTeX t)
                _   -> print (show "{ is not closed")

fileToMathJaxHTML :: FilePath -> IO ()
fileToMathJaxHTML path = do
    str <- loadFile path
    case parseFromStr str of
        Left a  -> print (show a)
        Right (t,e,l) ->
            case e of
                EOT -> writeFile (path ++ ".html") (toMathJaxHTML t)
                _   -> print (show "{ is not closed")

fileToImported :: FilePath -> IO ()
fileToImported path = do
    str <- loadFile path
    writeFile (path ++ "_.txt") str

resolveImports :: [Char] -> [Char] -> IO (Either [Char] [Char])
resolveImports str path = go str "" (S.fromList [path])
  where
    go "" done _ = return $ Right done
    go str done imported =
      case dropWhile (/= '%') str of
        ""  -> return $ Right $ done ++ str
        b:s -> 
          case dropWhile (/= '%') s of
            ""  -> return $ Left "unclosed import"
            _:after -> 
              let before  = takeWhile (/= '%') str
                  newpath = takeWhile (/= '%') s
              in if newpath `S.member` imported then
                    return $ Left $ "circular reference of " ++! newpath
                 else do
                    print ("importing " ++! newpath)
                    raw <- readFile newpath
                    resolved <- go raw "" (S.insert newpath imported)
                    either (return.Left) (\r -> go (r++after) (done++before) imported) resolved

loadFile path = do
  raw <- readFile path
  resolved <- resolveImports raw path
  case resolved of
    Left err  -> print err >>= const exitFailure
    Right str -> return str


ruleLaTeXChars =
    M.fromList [
        ('∀', "\\forall"),
        ('∈', "\\in"),
        ('├', "\\vdash"),
        ('≈', "\\approx"),
        ('⊥', "\\bot"),
        ('→', "\\to"),
        ('¬', "\\lnot"),
        ('∧', "\\land"),
        ('∨', "\\lor"),
        ('α', "\\alpha"),
        ('β', "\\beta"),
        ('γ', "\\gamma"),
        ('δ', "\\delta"),
        ('ϵ', "\\epsilon"),
        ('ε', "\\varepsilon"),
        ('ζ', "\\zeta"),
        ('η', "\\eta"),
        ('θ', "\\theta"),
        ('ϑ', "\\vartheta"),
        ('ι', "\\iota"),
        ('κ', "\\kappa"),
        ('λ', "\\lambda"),
        ('μ', "\\mu"),
        ('ν', "\\nu"),
        ('ξ', "\\xi"),
        ('π', "\\pi"),
        ('ϖ', "\\varpi"),
        ('ρ', "\\rho"),
        ('ϱ', "\\varrho"),
        ('σ', "\\sigma"),
        ('ς', "\\varsigma"),
        ('τ', "\\tau"),
        ('υ', "\\upsilon"),
        ('ϕ', "\\phi"),
        ('φ', "\\varphi"),
        ('χ', "\\chi"),
        ('ψ', "\\psi"),
        ('ω', "\\omega"),
        ('Γ', "\\Gamma"),
        ('Λ', "\\Lambda"),
        ('Σ', "\\Sigma"),
        ('Ψ', "\\Psi"),
        ('Δ', "\\Delta"),
        ('Ξ', "\\Xi"),
        ('Υ', "\\Upsilon"),
        ('Ω', "\\Omega"),
        ('Θ', "\\Theta"),
        ('Π', "\\Pi"),
        ('Φ', "\\Phi"),
        ('𝒫', "\\mathcal{P}")
    ]