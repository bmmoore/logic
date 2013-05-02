module Logic.Parse(
  parseWhole,
  parseFormula,
  parseTerm,
  formula,
  clauses,
  clause,
  literal,
  atom,
  term,
  tokenParser
  ) where

import Logic.Formula
import Logic.CNF

import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import qualified Text.Parsec.Token as P

import Control.Applicative

type Parser = Parsec String ()

-- apply a list of prefix operators, to work around parsec parsing only one
prefix p = Prefix (chainl1 p (return (.)))

parseWhole :: Parser a -> String -> Either String a
parseWhole p input = case parse (whiteSpace *> p <* eof) "" input of
  Left err -> Left (show err)
  Right f -> Right f

parseFormula :: String -> Either String Formula
parseFormula = parseWhole formula

parseTerm :: String -> Either String Term
parseTerm = parseWhole term

formula :: Parser Formula
formula = buildExpressionParser [[prefix (Not <$ symbol "~")],
                                 [Infix (And <$ symbol "/\\") AssocRight],
                                 [Infix (Or <$ symbol "\\/") AssocRight]
                                 ]
          (chainl (do quantifier <- (Forall <$ reserved "forall"
                                 <|> Exists <$ reserved "exists")
                      vars <- many1 (Var <$> identifier)
                      symbol "."
                      return (\f -> foldr quantifier f vars))
            (return (.)) id
           <*> (parens formula <|> Lit . Literal True <$> atom))

clauses :: Parser CNF
clauses = CNF <$> semiSep clause

clause :: Parser Clause
clause = Clause <$> commaSep literal

literal :: Parser Literal
literal = Literal False <$> (symbol "~" *> atom) <|> Literal True <$> atom

atom :: Parser Atom
atom = Atom <$> (Predicate <$> identifier) <*> option [] (parens (commaSep term)) <?> "atomic formula"

term :: Parser Term
term = Term <$> (Function <$> identifier) <*> option [] (parens (commaSep term)) 
   <|> VarTerm <$> (char '?' >> Var <$> identifier)
   <?> "term"

tokenParser = P.makeTokenParser (emptyDef {P.reservedNames = ["forall","exists"]})

parens = P.parens tokenParser
symbol = P.symbol tokenParser
reserved = P.reserved tokenParser
identifier = P.identifier tokenParser
commaSep = P.commaSep tokenParser
semiSep = P.semiSep tokenParser
whiteSpace = P.whiteSpace tokenParser