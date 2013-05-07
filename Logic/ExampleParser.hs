module Logic.ExampleParser(
  maudeExample
  ) where

import Logic.Formula
import Logic.CNF

import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Text.PrettyPrint.Leijen(pretty)

import Control.Applicative hiding (many,(<|>))
import Control.Monad

{-
 Parse just enough maude to recover CNF from the examples of Maude's RTP
 http://maude.cs.uiuc.edu/tools/rtp/
 which were in turn generated from the examples of Harrison's
 "Handbook of Practical Logic and Automated Reasoning",
 http://www.cl.cam.ac.uk/~jrh13/atp/index.html
 and from The TPTP Problem Library for Automated Theorem Proving
 http://www.cs.miami.edu/~tptp/
 -}

type Parser = Parsec String ()

parens = between (char '(') (char ')')
commaSep p = sepBy p (char ',')
commaSep1 p = sepBy1 p (char ',')

identChar = alphaNum <|> oneOf "-_'"
ident = many1 identChar

predicate :: Parser Predicate
predicate = Predicate <$> ident

atom = Atom <$> predicate <*> option [] (parens (commaSep term))

term = do
  str <- ident
  (VarTerm (Var str) <$ char ':' <* ident)
    <|> Term (Function str) <$> option [] (parens (commaSep term))
  
clause = parens $ do
  negative <- commaSep1 atom <|> (string "(empty).AtomMagma" >> return [])
  string " -> "
  positive <- commaSep1 atom <|> (string "(empty).AtomMagma" >> return [])
  return . Clause $ map (Literal False) negative ++ map (Literal True) positive

line :: Parser String
line = manyTill anyToken (char '\n')

prelude = do
  l <- line
  if l == "red !((" 
    then string "  "
    else prelude
postlude :: Parser ()
postlude = void $ string "\n)) .\n" >> many line

maudeExample = between prelude postlude $ 
  CNF <$> sepBy1 clause (string ",\n  ")

test = readFile "benchmarks/tptp-bang/pCSR-zero-three-one-plus-one-dotp.maude"
      >>= print . fmap pretty . parse maudeExample ""
