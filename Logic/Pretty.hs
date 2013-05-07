module Logic.Pretty where

import Logic.Formula
import Prelude hiding (Left,Right)

import Text.PrettyPrint.Leijen

args as = char '(' <> hcat (punctuate comma as) <> char ')'

instance Pretty Var where
  pretty (Var v) = text v
instance Pretty Function where  
  pretty (Function f) = text f
instance Pretty Term where
  pretty (Term f []) = pretty f
  pretty (Term f ts) = pretty f <> args (map pretty ts)
  pretty (VarTerm v) = char '?'<>pretty v
instance Pretty Predicate where  
  pretty (Predicate p) = text p
instance Pretty Atom where
  pretty (Atom p []) = pretty p
  pretty (Atom p ts) = pretty p <> args (map pretty ts)
instance Pretty Literal where
  pretty (Literal True a) = pretty a
  pretty (Literal False a) = char '~' <> pretty a
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
  | otherwise = parens (align image)

prettyFormula :: Formula -> (OpInfo, Doc)
prettyFormula f = case f of
  Lit a -> (maxrator, pretty a)
  Not f -> unary (text"~"<>) notOp f
--  Not f -> (maxrator, text"~"<>parens (pretty f))
  And l r -> binary "/\\" andOp l r
  Or l r -> binary "\\/" orOp l r
  Forall v f -> gatherForall id [v] f
  Exists v f -> gatherExists id [v] f
 where binary sym o l r =  
         let l' = bracket (prettyFormula l) Left o
             r' = bracket (prettyFormula r) Right o
         in (o, l'</>text sym<+>r')
       unary wrap o f =
         let f' = bracket (prettyFormula f) Nonassoc o
         in (o, wrap f')
       mkForall vs = text"forall"<+>hsep(map pretty vs)<+>text "."     
       mkExists vs = text"exists"<+>hsep(map pretty vs)<+>text "."     
       gatherForall doc vs (Forall v f) =
         gatherForall doc (v:vs) f
       gatherForall doc vs (Exists v f) =
         gatherExists (doc.(mkForall (reverse vs)<+>)) [v] f
       gatherForall doc vs f =
         unary (nest 2 . doc . (mkForall (reverse vs)<+>)) quantOp f
       gatherExists doc vs (Exists v f) =
         gatherExists doc (v:vs) f
       gatherExists doc vs (Forall v f) =
         gatherForall (doc.(mkExists (reverse vs)<+>)) [v] f
       gatherExists doc vs f =
         unary (nest 2 . doc .  (mkExists (reverse vs)<+>)) quantOp f
       [quantOp,orOp,andOp,notOp,maxrator] =
         zip [0..] [Prefix,Infix Right,Infix Right,Prefix,Infix Nonassoc]

{-
--A CNF-derived example
example = pretty (And (Or (Atomic (Atom (Predicate "A") [])) (Or (Atomic (Atom (Predicate "B") [])) (Not (Atomic (Atom (Predicate "C") []))))) (And (Or (Atomic (Atom (Predicate "C") [])) (Not (Atomic (Atom (Predicate "D") [])))) (And (Or (Atomic (Atom (Predicate "D") [])) (Not (Atomic (Atom (Predicate "A") [])))) (Atomic (Atom (Predicate "false") [])))))
-}