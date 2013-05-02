module Logic.Resolution where
import Control.Monad
import Data.List

import Logic.Formula
import Logic.CNF

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

resolve :: Clause -> Clause -> [Clause]
resolve (Clause c1)  (Clause c2) = do
  (l@(Literal s t),c1') <- selections c1
  let l' = complement l
  guard $ l' `elem` c2
  return (Clause (nub (c1++filter (/=l') c2)))

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

resoSat :: [Clause] -> Bool
resoSat [] = True
resoSat (Clause []:_) = False
resoSat cs@(Clause (Literal _ a:_):_) =
  resoSat (resolveOn a cs)