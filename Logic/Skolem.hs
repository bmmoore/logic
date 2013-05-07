{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic.Skolem where
import Data.List
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import qualified Data.Set as Set

import Logic.Formula

data SkolInfo = SkolInfo Var [Var] Formula
  deriving Show
newtype SkolM a = SkolM {unSkolM :: State (Int,[SkolInfo]) a}
  deriving (Functor,Applicative,Monad)

runSkolM :: SkolM a -> (a,[(Term,Formula)])
runSkolM m =
  let (x,(_ndefined,info)) = runState (unSkolM m) (0,[])
  in (x,[(Term (Function ("sk"++show i)) (map VarTerm args),
          Exists sv f)
         | (i,SkolInfo sv args f) <- zip [0..] info])

-- allocSkol v f makes a skolem function for exists v . f,
-- and returns a term with the function applied to the free variables.
allocSkol :: Var -> Formula -> SkolM Term
allocSkol sv f = SkolM $ do
  let args = Set.toList (fvs (Exists sv f))
  (n,tbl) <- get
  put (n+1,(SkolInfo sv args f:tbl))
  return (Term (Function ("sk"++show n)) (map VarTerm args))

skolemize :: Formula -> SkolM Formula
skolemize (Lit l) = pure $ Lit l
skolemize (And f1 f2) = And <$> skolemize f1 <*> skolemize f2
skolemize (Or  f1 f2) = Or  <$> skolemize f1 <*> skolemize f2
skolemize (Forall v f) = Forall v <$> skolemize f
skolemize (Exists v f) = do
  sf <- allocSkol v f
  skolemize (substF v sf f)

exists :: [Var] -> Formula -> Formula
exists = flip (foldr Exists)

existentialClosure :: Formula -> Formula
existentialClosure f = exists (Set.toList (fvs f)) f

