import Logic.Pretty() -- for Pretty instances
import Logic.Parse ( parseWhole )
import Logic.ExampleParser ( maudeExample )
import Logic.Formula ( Literal, runRenameBase )
import Logic.CNF ( cnfClauses, clauseVars )
import Logic.Resolution ( Result(Sat, Unsat), orSat )
import Logic.Orders
    ( MbOrder, negGreatestLitOrder, lexAtomOrder, kboLift )
import Text.PrettyPrint.Leijen ( pretty )
import System.Environment ( getArgs )
import System.IO ( hPutStrLn, stderr )

testLitOrder :: MbOrder Literal
testLitOrder = negGreatestLitOrder (lexAtomOrder compare (kboLift compare (const 1)))

prepCnf = map (runRenameBase clauseVars "x") . cnfClauses

printResult sol@(Sat _) = print (pretty sol)
printResult (Unsat s cs _) = do
  putStr "Unsat "
  print (pretty s)
  print (pretty cs)

{- Read and attempt to solve an example from the maude RTP benchmarks
   available at
   http://maude.cs.uiuc.edu/tools/rtp/
 -}

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
