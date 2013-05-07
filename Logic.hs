module Logic where
import Logic.Pretty() -- for Pretty instance
import Logic.Parse
import Logic.ExampleParser
import Logic.Formula
import Logic.CNF
import Logic.Skolem
import Logic.Resolution
import Logic.Orders
import Logic.Unification

import Data.Traversable
import Control.Monad.State
import Control.Applicative
import Text.PrettyPrint.Leijen(Pretty(pretty),(<+>),text)
import Text.ParserCombinators.Parsec
import System.Environment
import System.IO

parsef = parse formula "<interactive>"

prepare f = clausify . liftUniversal . skol . existentialClosure . struct . nnf $ f

skol :: Formula -> Formula
skol = fst . flip runState (0,[]) . unSkolM . skolemize

struct :: Formula -> Formula
struct = fst . flip runState (0,[]) . unStructM . structTrans

runParsed :: Either String (IO ()) -> IO ()
runParsed = either putStrLn id

prettyParsed :: (Pretty a) => Either String a -> IO ()
prettyParsed = runParsed . fmap (print . pretty)

onParse :: Parser a -> (a -> IO ()) -> String -> IO ()
onParse parser f input = runParsed $ f <$> parseWhole parser input

withParsed parser f input = prettyParsed $ f <$> parseWhole parser input
withParsed2 parser f i1 i2 = prettyParsed $ f <$> parseWhole parser i1 <*> parseWhole parser i2

withParseM parser f input = runParsed $ f <$> parseWhole parser input

testLitOrder :: MbOrder Literal
testLitOrder = negGreatestLitOrder (lexAtomOrder compare (kboLift compare (const 1)))

testForm = prettyParsed . parseFormula

l = withParsed2 literal testLitOrder

r = withParsed2 clause (orderedResolution testLitOrder)
f = withParsed clause (orderedFactoring testLitOrder)

withCNF :: (CNF -> IO ()) -> Formula -> IO ()
withCNF useCNF f = do
  let (f',defPreds) = runStructM (structTrans (nnf f))
      (f'',skolFuns) = runSkolM (skolemize (existentialClosure f'))
  putStrLn "Original formula:"
  print (pretty f)
  putStrLn "Definition predicates:"
  mapM_ print [pretty p <+> text "=>" <+>  pretty f | (p,f) <- defPreds]
  putStrLn "Skolem functions:"
  mapM_ print [pretty t <+> text "~" <+>  pretty f | (t,f) <- skolFuns]
  let cnf = clausify (liftUniversal f'')
  putStrLn "CNF:"
  print (pretty cnf)
  putStrLn "Result:"
  useCNF cnf
      
cnf = onParse formula $ withCNF (\_ -> return ())

sat = onParse formula $ withCNF (printResult . orSat testLitOrder . cnfClauses)

{- equalish, rewrite, reflexive-rewrite, goal, c-b, c-c, c-a, f-D -}

prepCnf = map (runRenameBase clauseVars "x") . cnfClauses

s = runParsed . fmap (mapM_ (print . pretty). orTrace testLitOrder . prepCnf) . parseWhole clauses 
s' = prettyParsed . parseWhole clauses 

printResult sol@(Sat _) = print (pretty sol)
printResult (Unsat s cs _) = do
  putStr "Unsat "
  print (pretty s)
  print (pretty cs)

runSat :: CNF -> IO ()
runSat = printResult . orSat testLitOrder . prepCnf

-- main = readFile "test2.cnf" >>= onParse clauses runSat

main = do
  args <- getArgs
  let (verbose,file) =
        case args of
          ["-v",file] -> (True,file)
          [file] -> (False,file)
  contents <- readFile file
  case parseWhole maudeExample contents of
    Left err -> hPutStrLn stderr err
    Right cnf -> do
      let result = orSat testLitOrder (prepCnf cnf)
      if verbose
        then printResult result
        else case result of
          Unsat _ _ _ -> putStrLn "Unsat"
          Sat _ -> putStrLn "Sat"
