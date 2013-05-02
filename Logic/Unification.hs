{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses #-}
module Logic.Unification where
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)

import Logic.Formula

-- Pretty-printing for debugging
import Logic.Pretty()
import Logic.Parse(parseTerm)
import Text.PrettyPrint.Leijen(pretty,text,tupled,(<+>),Doc)

utest :: String -> String -> IO ()
utest s1 s2 = case do t1 <- parseTerm s1
                      t2 <- parseTerm s2
                      unifyTerms t1 t2 of
  Left msg -> putStrLn msg
  Right (unifier, subst) -> print (prettySubst subst) >> print (pretty unifier)

prettySubst :: Map Var Term -> Doc
prettySubst sigma = tupled [pretty v <+> text "|->" <+> pretty t | (v,t) <- Map.toAscList sigma]
-- Now for the algorithm

unifyTerms :: Term -> Term -> Either String (Term, Map Var Term)
unifyTerms t1 t2 = runEmpty (doUnify t1 t2 >> expandTerm t1)

newtype UnifyM a = UnifyM (ReaderT (Set Var) (StateT (Map Var Term) (Either String)) a)
  deriving (Functor,Applicative,Monad,
            MonadReader (Set Var),MonadState (Map Var Term),MonadError String)
runUnifyM (UnifyM u) occurs sigma = runStateT (runReaderT u occurs) sigma
runEmpty ua = runUnifyM ua Set.empty Map.empty

underVar :: Var -> UnifyM a -> UnifyM a
underVar v body = do
  used <- ask
  if Set.member v used
    then throwError ("Occurs check failed on variable "++varName v)
    else local (Set.insert v) body

getBinding :: Var -> UnifyM (Maybe Term)
getBinding v = Map.lookup v <$> get

-- should only be called 
bind :: Var -> Term -> UnifyM ()
bind v t = modify (Map.insert v t)

expandTerm1 :: Term -> (Term -> UnifyM a) -> UnifyM a
expandTerm1 t@(Term _ _) k = k t
expandTerm1 t@(VarTerm v) k = do
  b <- getBinding v
  case b of
    Nothing -> k t
    Just t' -> underVar v (expandTerm1 t' k)

expandTerm :: Term -> UnifyM Term
expandTerm t = expandTerm1 t $ \t -> case t of
  VarTerm v -> return t
  Term f ts -> Term f <$> mapM expandTerm ts

doUnify :: Term -> Term -> UnifyM ()
doUnify t1 t2 = expandTerm1 t1 $ \t1 -> expandTerm1 t2 $ \t2 -> do
  case (t1, t2) of
    (Term f1 ts1, Term f2 ts2) ->
      if f1 == f2
      then zipWithM_ doUnify ts1 ts2
      else throwError $ "Function symbol missmatch "++show f1++" and "++show f2
    (VarTerm v, VarTerm v2) | v == v2 -> return ()
                            | otherwise -> bind (min v v2) (VarTerm (max v v2))
    (VarTerm v, t) -> bind v t
    (t, VarTerm v) -> bind v t
