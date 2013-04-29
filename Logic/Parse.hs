module Logic.Parse(
  parseFormula,
  formula,
  atom,
  term,
  tokenParser
  ) where

import Logic.Formula

import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import Text.Parsec.Language(emptyDef)
import qualified Text.Parsec.Token as P

import Control.Applicative

type Parser = Parsec String ()

-- apply a list of prefix operators, to work around parsec parsing only one
prefix p = Prefix (chainl1 p (return (.)))

parseFormula :: String -> Either String Formula
parseFormula input = case parse (whiteSpace *> formula <* eof) "" input of
  Left err -> Left (show err)
  Right f -> Right f

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
whiteSpace = P.whiteSpace tokenParser