module Logic.Pretty where

import Logic.Types
import Prelude hiding (Left,Right)

import Text.PrettyPrint.Leijen

instance Pretty Var where
  pretty (Var v) = text v
instance Pretty Function where  
  pretty (Function f) = text f
instance Pretty Term where
  pretty (Term f []) = pretty f
  pretty (Term f ts) = pretty f <> tupled (map pretty ts)
  pretty (VarTerm v) = char '?'<>pretty v
instance Pretty Predicate where  
  pretty (Predicate p) = text p
instance Pretty Atom where
  pretty (Atom p []) = pretty p
  pretty (Atom p ts) = pretty p <> tupled (map pretty ts)
instance Pretty Formula where
  pretty f = snd (prettyFormula f)

-- Norman Ramsey's fixity unparsing
data Fixity = Prefix | Postfix | Infix Side
  deriving (Show,Eq)
data Side = Left | Right | Nonassoc
  deriving (Show,Eq)
  -- as a direction, Nonassoc means child is argument of a unary operator
type OpInfo = (Int,Fixity)
noparens :: OpInfo -> OpInfo -> Side -> Bool
noparens inner@(pi,fi) outer@(po,fo) side =
  pi > po ||
  case (fi,side) of
    (Postfix,Left) -> True
    (Prefix, Right) -> True
    (Infix Left, Left) -> pi == po && fo == Infix Left
    (Infix Right, Right) -> pi == po && fo == Infix Right
    (_, Nonassoc) -> fi == fo
    _ -> False
bracket :: (OpInfo,Doc) -> Side -> OpInfo -> Doc
bracket (inner,image) side outer
  | noparens inner outer side = image
  | otherwise = parens image

prettyFormula :: Formula -> (OpInfo, Doc)
prettyFormula f = case f of
  Atomic a -> (maxrator, pretty a)
  Not f -> unary (text"~"<>) notOp f
  And l r -> binary "/\\" andOp l r
  Or l r -> binary "\\/" orOp l r
  Forall v f -> unary ((text"forall"<+>pretty v<+>text".")<+>) quantOp f
  Exists v f -> unary ((text"exists"<+>pretty v<+>text".")<+>) quantOp f
 where binary sym o l r =  
         let l' = bracket (prettyFormula l) Left o
             r' = bracket (prettyFormula r) Right o
         in (o, l'<+>text sym<+>r')
       unary wrap o f =
         let f' = bracket (prettyFormula f) Nonassoc o
         in (o, wrap f')
       [quantOp,orOp,andOp,notOp,maxrator] =
         zip [0..] [Prefix,Infix Right,Infix Right,Prefix,Infix Nonassoc]
