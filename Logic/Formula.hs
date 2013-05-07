{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Formula where
import qualified Data.Set as Set
import Data.List(elemIndex)
import Data.String
import Control.Applicative
import Data.Traversable
import Control.Monad.State
import Data.Map(Map)
import qualified Data.Map as Map

newtype Var = Var {varName :: String}
  deriving (Eq,Ord,Show,IsString)
newtype Function = Function String
  deriving (Eq,Ord,Show,IsString)
newtype Predicate = Predicate String
  deriving (Eq,Ord,Show,IsString)

data Term = Term Function [Term] | VarTerm Var
  deriving (Show,Eq)
data Atom = Atom Predicate [Term]
  deriving (Show,Eq)
data Literal = Literal Bool Atom
  deriving (Show,Eq)
complement :: Literal -> Literal
complement (Literal s a) = (Literal (not s) a)

data Formula =
    Lit Literal
  | Not Formula
  | And Formula Formula
  | Or  Formula Formula
  | Forall Var Formula
  | Exists Var Formula
  deriving Show

cformula :: (Formula -> Formula) -> (Formula -> Formula)
cformula rec (Lit l) = Lit l
cformula rec (Not f) = Not (rec f)
cformula rec (And f1 f2) = And (rec f1) (rec f2)
cformula rec (Or f1 f2) = Or (rec f1) (rec f2)
cformula rec (Forall v f) = Forall v (rec f)
cformula rec (Exists v f) = Exists v (rec f)

class Binding t where
  vars :: t -> Set.Set Var
  fvs :: t -> Set.Set Var
  fvs = vars
  alphaEquiv :: [Var] -> [Var] -> t -> t -> Bool

instance Binding Term where
  vars (Term _ ts) = Set.unions (map vars ts)
  vars (VarTerm v) = Set.singleton v
  alphaEquiv bound1 bound2 (Term t1 ts1) (Term t2 ts2)
    = t1 == t2 && length ts1 == length ts2
      && and (zipWith (alphaEquiv bound1 bound2) ts1 ts2)
  alphaEquiv bound1 bound2 (VarTerm v1) (VarTerm v2)
    = case (elemIndex v1 bound1, elemIndex v2 bound2) of
        (Just i1, Just i2) -> i1 == i2
        (Nothing, Nothing) -> v1 == v2
        _ -> False
  alphaEquiv _ _ _ _ = False
instance Binding Atom where
  vars (Atom _ ts) = Set.unions (map vars ts)
  alphaEquiv bound1 bound2 (Atom p1 ts1) (Atom p2 ts2) =
    p1 == p2 && length ts1 == length ts2
    && and (zipWith (alphaEquiv bound1 bound2) ts1 ts2)
instance Binding Literal where
  vars (Literal _ a) = vars a
  alphaEquiv bound1 bound2 (Literal s1 p1) (Literal s2 p2) =
    s1 == s2 && alphaEquiv bound1 bound2 p1 p2
instance Binding Formula where
  fvs (Lit l) = fvs l
  fvs (Not f) = fvs f
  fvs (And f1 f2) = Set.union (fvs f1) (fvs f2)
  fvs (Or f1 f2) = Set.union (fvs f1) (fvs f2)
  fvs (Forall v f) = Set.delete v (fvs f)
  fvs (Exists v f) = Set.delete v (fvs f)

  vars (Lit l) = vars l
  vars (Not f) = vars f
  vars (And f1 f2) = Set.union (vars f1) (vars f2)
  vars (Or f1 f2) = Set.union (vars f1) (vars f2)
  vars (Forall v f) = Set.insert v (vars f)
  vars (Exists v f) = Set.insert v (vars f)

  alphaEquiv bound1 bound2 (Lit l1) (Lit l2) = alphaEquiv bound1 bound2 l1 l2
  alphaEquiv bound1 bound2 (Not f1) (Not f2) = alphaEquiv bound1 bound2 f1 f2
  alphaEquiv bound1 bound2 (And f1l f1r) (And f2l f2r) =
    alphaEquiv bound1 bound2 f1l f2l && alphaEquiv bound1 bound2 f1r f2r
  alphaEquiv bound1 bound2 (Or f1l f1r) (Or f2l f2r) =
    alphaEquiv bound1 bound2 f1l f2l && alphaEquiv bound1 bound2 f1r f2r
  -- TODO: Really ought to also allow permuting quantifiers,
  -- but that's a bit more involved.
  alphaEquiv bound1 bound2 (Forall v1 f1) (Forall v2 f2) =
    alphaEquiv (v1:bound1) (v2:bound2) f1 f2
  alphaEquiv bound1 bound2 (Exists v1 f1) (Forall v2 f2) =
    alphaEquiv (v1:bound1) (v2:bound2) f1 f2
  alphaEquiv _ _ _ _ = False

substTerm :: Var -> Term -> Term -> Term
substTerm x t (Term f ts) = Term f (map (substTerm x t) ts)
substTerm x t (VarTerm x') | x == x' = t
                           | otherwise = VarTerm x'

substF :: Var -> Term -> Formula -> Formula
substF v t = go
  where go (Lit (Literal pos (Atom p ts))) = Lit (Literal pos (Atom p (map (substTerm v t) ts)))
        go (And f1 f2) = And (go f1) (go f2)
        go (Or f1 f2) = Or (go f1) (go f2)
        go (Forall v2 f)
          | v == v2 = (Forall v2 f)
          | otherwise = Forall v2 (go f)
        go (Exists v2 f)
          | v == v2 = (Exists v2 f)
          | otherwise = Exists v2 (go f)
        
nnf :: Formula -> Formula
nnf = nnf' True

nnf' :: Bool -> Formula -> Formula
nnf' pos (Lit l) = Lit (if pos then l else complement l)
nnf' pos (Not f) = nnf' (not pos) f
nnf' True f = cformula (nnf' True) f
nnf' False (And f1 f2) = Or (nnf' False f1) (nnf' False f2)
nnf' False (Or f1 f2) = And (nnf' False f1) (nnf' False f2)
nnf' False (Forall v f) = Exists v (nnf' False f)
nnf' False (Exists v f) = Forall v (nnf' False f)

-- Traversal' Var Atom in the language of Control.Lens
-- used for freshening vars in clauses before unification
literalVars :: (Applicative m) => (Var -> m Var) -> Literal -> m Literal
literalVars renameVar (Literal s a) = Literal s <$> atomVars renameVar a

atomVars :: (Applicative m) => (Var -> m Var) -> Atom -> m Atom
atomVars renameVar (Atom p ts) = Atom p <$> traverse (termVars renameVar) ts

termVars :: (Applicative m) => (Var -> m Var) -> Term -> m Term
termVars renameVar (VarTerm v) = VarTerm <$> renameVar v
termVars renameVar (Term f ts) = Term f <$> traverse (termVars renameVar) ts

-- add an integer suffix
runRenameBase :: ((Var -> State (Int,Map Var Var) Var) ->
                  (a -> State (Int,Map Var Var) a)) ->
                 String -> a -> a
runRenameBase renamer base t =
    fst $ runState (renamer renameVar t) (0,Map.empty)
  where renameVar v = do
          (n,sigma) <- get
          case Map.lookup v sigma of
            Just v' -> return v'
            Nothing -> do
              let v' = Var (base++show n)
              put (n+1,Map.insert v v' sigma)
              return v'          
                  