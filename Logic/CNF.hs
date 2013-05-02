{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.CNF where
import Control.Applicative
import Control.Monad.State
import Data.Char
import qualified Data.Set as Set

import Logic.Formula
import Logic.Pretty
import Text.PrettyPrint.Leijen
  hiding ((<$>))

newtype Clause = Clause [Literal]
  deriving Show
clauseLiterals (Clause ls) = ls
newtype CNF = CNF [Clause] -- conjuction of disjunctions
  deriving Show
cnfClauses (CNF cs) = cs

instance Pretty CNF where
  pretty (CNF clauses) =
    cat . punctuate semi . map pretty $ clauses
instance Pretty Clause where
  pretty (Clause literals) =
    fillSep . punctuate comma . map pretty $ literals

join1 :: (a -> a -> a) -> a -> [a] -> a
join1 op unit [] = unit
join1 op unit [x] = x
join1 op unit xs = foldr1 op xs

toFormula :: CNF -> Formula
toFormula (CNF clauses) = conj . map (disj . map Lit . clauseLiterals) $ clauses

conj :: [Formula] -> Formula 
conj = join1 And (Lit (Literal True (Atom (Predicate "true") [])))
disj :: [Formula] -> Formula 
disj = join1 Or (Lit (Literal False (Atom (Predicate "true") [])))

-- direct translation, must be negation and quantifier free
-- must be negation and quantifier free
clausify :: Formula -> CNF
clausify (Lit l) = CNF [Clause [l]]
clausify (And f1 f2) =
  let CNF cs1 = clausify f1
      CNF cs2 = clausify f2
  in CNF (cs1++cs2)
clausify (Or f1 f2) =
  let CNF cs1 = clausify f1
      CNF cs2 = clausify f2
  in CNF [Clause (c1++c2) 
         | Clause c1 <- cs1,
           Clause c2 <- cs2]

rename :: Formula -> State (Set.Set Var) Formula
rename (Lit l) = return $ Lit l
rename (And f1 f2) = And <$> rename f1 <*> rename f2
rename (Or f1 f2) = Or <$> rename f1 <*> rename f2
rename (Forall v@(Var s) f) = do
  used <- get
  if Set.member v used then do
    let base = reverse . dropWhile isDigit . reverse $ s
        v' = head $ filter (\v -> not (Set.member v used)) (Var s:[Var (s++show i) | i <- [0..]])
    put (Set.insert v' used)
    rename (substF v (VarTerm v') f)
   else do
    put (Set.insert v used)
    rename f

liftUniversal :: Formula -> Formula
liftUniversal f = evalState (rename f) (fvs f)

-- add new variables.
data DefPredInfo = DefPred [Var] Formula
  deriving Show
newtype StructM a = StructM {unStructM :: State (Int,[DefPredInfo]) a}
  deriving (Functor,Applicative,Monad)

-- should share
getDefPred :: Formula -> StructM (Predicate,[Var])
getDefPred f = StructM $ do
  (n,info) <- get
  let vars = Set.toList (fvs f)
  case [((Predicate ("pdef"++show i)), vars)
       | (i,DefPred vars' f') <- zip [n-1,n-2..0] info,
         alphaEquiv vars vars' f f'] of
    (t:_) -> return t
    _ -> do
      put (n+1,(DefPred vars f:info))
      return ((Predicate ("pdef"++show n)), vars)

-- assumes input in NNF
structTrans :: Formula -> StructM Formula
structTrans f = do
  p <- getDefPred f
  dfn <- mkDef p f
  return (And (ltrue p) dfn)
  
plit (p,vars) = Atom p (map VarTerm vars)

ltrue = Lit . Literal True . plit
lfalse = Lit . Literal False . plit

limpl p f = Or (lfalse p) f

foralls :: [Var] -> Formula -> Formula
foralls = flip (foldr Forall)

def :: Formula -> StructM ((Predicate,[Var]),Formula)
def f = do
  p <- getDefPred f
  d <- mkDef p f
  return (p,d)

-- this considers every subterm.
-- see note about "recursive definition" in survey,
-- basically we only need to do this transformation
-- at chosen subterms.

mkDef :: (Predicate,[Var]) -> Formula -> StructM Formula
mkDef p@(_,vars) (Lit l) =
  return $ foralls vars (limpl p (Lit l))
mkDef p@(_,vars) (Or f1 f2) = do
  (p1,d1) <- def f1
  (p2,d2) <- def f2
  return $
    And (foralls vars (limpl p (Or (ltrue p1) (ltrue p2)))) (And d1 d2)
mkDef p@(_,vars) (And f1 f2) = do
  (p1,d1) <- def f1
  (p2,d2) <- def f2
  return $
    And (foralls vars (limpl p (And (ltrue p1) (ltrue p2)))) (And d1 d2)
mkDef p@(_,vars) (Forall v f1) = do
  (p1,d1) <- def f1
  return $
    And (foralls vars (limpl p (Forall v (ltrue p1)))) d1
mkDef p@(_,vars) (Exists v f1) = do
  (p1,d1) <- def f1
  return $
    And (foralls vars (limpl p (Exists v (ltrue p1)))) d1


g = Or
    (Exists y (Or (Lit (Literal False (Atom a [VarTerm x])))
                  (Lit (Literal False (Atom a [VarTerm y])))))
    (Exists z (Lit (Literal True (Atom c [VarTerm x,VarTerm z]))))
  where [x,y,z] = map Var ["x","y","z"]
        [a,c] = map Predicate ["a","c"]

q = (Exists y (Or (Lit (Literal False (Atom a [VarTerm y])))
                  (Lit (Literal False (Atom a [VarTerm y])))))
  where [y] = map Var ["y"]
        [a] = map Predicate ["a"]


prettyDefs :: (Int,[DefPredInfo]) -> Doc
prettyDefs (n,ds) =
  vcat [pretty (Atom (Predicate ("pdef"++show i)) (map VarTerm args))
        <+> text " <-> " <+> pretty f
        | (i,DefPred args f) <- zip [n-1,n-2..0] ds]
