module Logic.Resolution where
import Control.Monad
import Data.List

import Logic.Formula
import Logic.CNF
import Logic.Unification
import Logic.Orders
import qualified Data.Map as Map
import Data.Map(Map)

import Text.PrettyPrint.Leijen(Pretty(pretty),text,nest,(<>),(<+>),semiBraces,line)

revApp [] bs = bs
revApp (a:as) bs = revApp as (a:bs)

selections :: [a] -> [(a,[a])]
selections l = select [] l
  where select before [] = []
        select before (a:after) = (a,revApp before after):select (a:before) after

preSimpl :: Clause -> Clause
preSimpl (Clause ls) = Clause (nub ls)

simplify :: Clause -> [Clause]
simplify c@(Clause ls)
  | any (\l -> complement l `elem` ls) ls = []
  | otherwise = [c]

-- Ground unification stuff
resolve :: Clause -> Clause -> [Clause]
resolve (Clause c1)  (Clause c2) = do
  (l@(Literal s t),c1') <- selections c1
  let l' = complement l
  guard $ l' `elem` c2
  return (Clause (nub (c1'++filter (/=l') c2)))

--resolveOn :: Atom -> [Clause] -> [Clause]
resolveOn a clauses =
  let lls = map clauseLiterals clauses
      pos = Literal True a
      neg = Literal False a
      (hasPos,lls')  
        = partition (elem pos) lls
      (hasNeg,hasNeither)
        = partition (elem neg) lls'
      hasPos' = map (filter (/=pos)) hasPos
      hasNeg' = map (filter (/=neg)) hasNeg
  in map Clause hasNeither++
     concatMap simplify
     [Clause (nub (a++b)) | a <- hasPos', b <- hasNeg']

resoPropSat :: [Clause] -> Bool
resoPropSat [] = True
resoPropSat (Clause []:_) = False
resoPropSat cs@(Clause (Literal _ a:_):_) =
  resoPropSat (resolveOn a cs)

expandLiteral (Literal b t) = fmap (Literal b) (expandAtom t)
expandAtom (Atom p ts) = fmap (Atom p) (mapM expandTerm ts)

-- ensures disjoint variables by renaming, consider building into unification
-- resolveFree :: Clause -> Clause -> [Clause]
resolveFree l r =
  let (Clause c1) = runRenameBase clauseVars "l" l
      (Clause c2) = runRenameBase clauseVars "r" r
  in
  [ runRenameBase clauseVars "x" $ Clause (nub cs')
  | (Literal b1 a1@(Atom p1 ts1),cs1) <- selections c1,
    (Literal b2 a2@(Atom p2 ts2),cs2) <- selections c2,
    p1 == p2,
    b1 /= b2,
    length ts1 == length ts2,
    let u@(Right (cs',_)) = runEmpty (do
          zipWithM_ doUnify ts1 ts2
          mapM_ expandTerm ts1
          mapM expandLiteral (cs1++cs2)),
    case u of Left _ -> False; Right _ -> True]

factoring (Clause cs) =
  [ runRenameBase clauseVars "x" $ Clause (nub cs')
  | (Literal b1 a1@(Atom p1 ts1),cs1) <- selections cs,
    (Literal b2 a2@(Atom p2 ts2),cs2) <- selections cs1,
    p1 == p2,
    b1 == b2,
    length ts1 == length ts2,
    let u@(Right (cs',_)) = runEmpty $ do
          zipWithM_ doUnify ts1 ts2
          ts' <- mapM expandTerm ts1
          cs2' <- mapM expandLiteral cs2
          return ((Literal b1 (Atom p1 ts')):cs2'),
    case u of Left _ -> False; Right _ -> True]

-- also directed, so positive clause from left
orderedResolution :: MbOrder Literal -> Clause -> Clause -> [Clause]
orderedResolution litOrder l r =
  let (Clause c1) = runRenameBase clauseVars "l" l
      (Clause c2) = runRenameBase clauseVars "r" r
  in
  [ runRenameBase clauseVars "x" $ Clause (nub (cs1'++cs2'))
  | (l1@(Literal True (Atom p1 ts1)),cs1) <- selections c1,
    all (\c -> litOrder l1 c /= Ordered LT)  cs1, -- early "potentially maximal" check
    (l2@(Literal False (Atom p2 ts2)),cs2) <- selections c2,
    p1 == p2,
    length ts1 == length ts2,
    Right ((l',cs1',cs2'),_) <- [runEmpty $ do
          zipWithM_ doUnify ts1 ts2
          ts' <- mapM expandTerm ts1
                 -- need unified term to check if it's maximal w.r.t the substitution
          cs1' <- mapM expandLiteral cs1
          cs2' <- mapM expandLiteral cs2
          return (Literal True (Atom p1 ts'),cs1',cs2')],
    all (\c -> litOrder l' c /= Ordered LT)  cs1' -- check if actually maximal
    ]

orderedFactoring litOrder (Clause cs) =
  [ runRenameBase clauseVars "x" $ Clause (nub (l':cs'))
  | (Literal b1 a1@(Atom p1 ts1),cs1) <- selections cs,
    (Literal b2 a2@(Atom p2 ts2),cs2) <- selections cs1,
    p1 == p2,
    b1 == b2,
    length ts1 == length ts2,
    Right ((l',cs'),_) <- [runEmpty $ do
          zipWithM_ doUnify ts1 ts2
          ts' <- mapM expandTerm ts1
          cs2' <- mapM expandLiteral cs2
          return ((Literal b1 (Atom p1 ts')),cs2')],
    all (\c -> litOrder l' c /= Ordered LT)  cs' -- check if actually maximal
  ]

data Result = Sat [(Int,Clause,Source)]
            | Unsat Source [(Int,Clause,Source)] [(Clause,Source)] -- used/worklist when [] discovered
  deriving Show
instance Pretty Result where
  pretty (Sat cs) = text"Sat"<+>semiBraces (map pretty cs)
  pretty (Unsat s used work) = nest 2
                               (text"Unsat"<+>pretty s
                                <>line<>semiBraces (map pretty used)
                                <>line<>semiBraces (map pretty work))

type ClauseQueue = Map Int [(Clause,Source)]
enqueue :: (Clause,Source) -> ClauseQueue -> ClauseQueue
dequeue :: ClauseQueue -> Maybe ((Clause,Source),ClauseQueue)

enqueue (c,s) cq = Map.insertWith (++) (clauseSize c) [(c,s)] cq
dequeue cq = do
  ((k,c:cs), cq') <- Map.minViewWithKey cq
  return (c,if null cs then cq' else Map.insert k cs cq')

clauseSize :: Clause -> Int
clauseSize (Clause ls) =
  length ls + sum [termWeight (const 1) t | Literal _ (Atom _ ts) <- ls, t <- ts]

data Source = Orig | Resolve Int Int | Factor Int
  deriving Show
instance Pretty Source where
  pretty = text . show

orSat :: MbOrder Literal -> [Clause] -> Result
orSat litOrder clauses = orSat' litOrder 0 []
                         (foldr enqueue Map.empty [(c,Orig) | c <- clauses])

orSat' :: MbOrder Literal -> Int -> [(Int,Clause,Source)] -> ClauseQueue -> Result
orSat' litOrder ncl used cq = case dequeue cq of
  Nothing -> Sat used
  Just ((Clause [],s),cq') -> Unsat s used (concat (Map.elems cq'))
  Just ((c,s),cq')
    | c `elem` [c' | (_,c',_) <- used] -> orSat' litOrder ncl used cq'
                            -- we're saturating, need to avoid repeating
    | otherwise ->
      let cs' = [(c',Factor ncl) | c' <- orderedFactoring litOrder c]
              ++[(c'',Resolve ncl i) |
                 (i,c',_) <- used,
                 c'' <- orderedResolution litOrder c c']
              ++[(c'',Resolve i ncl) |
                 (i,c',_) <- used,
                 c'' <- orderedResolution litOrder c' c]
      in orSat' litOrder (ncl+1) ((ncl,c,s):used) (foldr enqueue cq' cs')
       
orTrace :: MbOrder Literal -> [Clause] -> [(Int,Clause,Source)]
orTrace litOrder clauses = orTrace' litOrder 0 [] [(c,Orig) | c <- clauses]

orTrace' :: MbOrder Literal -> Int -> [(Int,Clause,Source)] -> [(Clause,Source)] -> [(Int,Clause,Source)]
orTrace' litOrder ncl used [] = []
orTrace' litOrder ncl used ((Clause [],s):cs) = []
orTrace' litOrder ncl used ((c,s):cs) 
  | c `elem` [c' | (_,c',_) <- used] = orTrace' litOrder ncl used cs
                            -- we're saturating, need to avoid repeating
  | otherwise =
    let cs' =  [(c',Factor ncl) | c' <- orderedFactoring litOrder c]
            ++ [(c'',Resolve ncl i) |
               (i,c',_) <- used,
               c'' <- orderedResolution litOrder c c']
            ++[(c'',Resolve i ncl) |
               (i,c',_) <- used,
               c'' <- orderedResolution litOrder c' c]
    in (ncl,c,s):orTrace' litOrder (ncl+1) ((ncl,c,s):used) (cs++cs')
