module Logic.Orders where
import Data.Monoid
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Function(on)
import Debug.Trace

import Logic.Formula

varOccs :: Term -> Map.Map Var Int
varOccs (VarTerm v) = Map.singleton v 1
varOccs (Term f ts) = Map.unionsWith (+) (map varOccs ts)

data MbOrdering = Unordered | Ordered Ordering
  deriving (Show,Eq,Ord)

instance Monoid MbOrdering where
  mempty = Ordered EQ
  Unordered `mappend` _ = Unordered
  Ordered EQ `mappend` b = b
  o@(Ordered a) `mappend` _ = o

type Order a = a -> a -> Ordering
type MbOrder a = a -> a -> MbOrdering

-- assumes same length
lexico :: (Monoid c) => (a -> b -> c) -> ([a] -> [b] -> c)
lexico o l1 l2 = mconcat (zipWith o l1 l2)

type Multiset a = [(a,Int)]

-- kinda like lexicographic by the key order.
-- if multisets are unequal, find
-- the highest-ordered element where
-- they have a different number of occurances,
-- and the multiset with more copies is bigger
multiset :: Order a -> Order (Multiset a)
multiset o m1 m2 = go (desc m1) (desc m2)
  where desc = sortBy (flip o `on` fst)
        go (_:_) [] = GT
        go [] [] = EQ
        go [] (_:_) = LT
        go ((a,na):as) ((b,nb):bs) =
          o a b <> compare na nb <> go as bs

-- total order
type Precedence = Order Function

{- Weight must be non-negative for all symbols,
   strictly positive for constants.

   Probably needs to be strictly positive to be liftable.
   
   if it assigns a unary function weight 0
   it must be used with a precedence that makes that
   function the greatest element.
 -}
type Weight = Function -> Int

termWeight :: Weight -> Term -> Int
termWeight funWeight (Term f ts)
  = funWeight f + sum (map (termWeight funWeight) ts)
termWeight _ (VarTerm _) = 1
  -- every constant has strictly positive weight, so any ground instance
  -- must have weight at least 1. Might be able to get fancier in a multisorted
  -- setting, with a sort-dependent lower bound on weight of ground instances.

kboGround :: Precedence -> Weight -> Term -> Term -> Ordering
kboGround prec funWeight t1@(Term f1 ts1) t2@(Term f2 ts2) =
    compare (weight t1) (weight t2) <>
    prec f1 f2 <>
    lexico (kboGround prec funWeight) ts1 ts2
  where
    weight = termWeight funWeight


-- trace' msg x = trace (msg++show x) x
trace' _ x = x

-- With variables, there's a preliminary pass that checks which variables
-- occur, and enforces that you can never have t1 > t2 if any variable occurs
-- more often in t2 (by setting it to a term of large enough weight) and conversely.
-- after that, we can compare as usual - if the weight even counting variables as
-- not weighing enough is enough to make one heavier then it's greater,
-- if vars differ but weights are equal, then the weight difference can only
-- ever grow in favor of the one already favored by var occurance count.
kboLift :: Precedence -> Weight -> MbOrder Term
kboLift _ _ (VarTerm v1) (VarTerm v2) = if v1 == v2 then Ordered EQ else Unordered
kboLift _ _ (VarTerm v) t@(Term _ _) = if Set.member v (vars t) then Ordered LT else Unordered
kboLift _ _ t@(Term _ _) (VarTerm v) = if Set.member v (vars t) then Ordered GT else Unordered
kboLift prec funWeight t1@(Term f1 ts1) t2@(Term f2 ts2) =
  let vs1 = varOccs t1
      vs2 = varOccs t2
      varDiffs = Map.elems (Map.map (flip compare 0) (Map.unionWith (+) vs1 (Map.map negate vs2)))
      someGt = GT `elem` varDiffs
      someLt = LT `elem` varDiffs
  in (if someGt
     then (if someLt then const Unordered else canOnly GT)
     else (if someLt then canOnly LT else id)) $
     (Ordered (compare (weight t1) (weight t2))) -- variables cancel
     <> Ordered (prec f1 f2) <>
        lexico (kboLift prec funWeight) ts1 ts2
 where weight = termWeight funWeight
       canOnly o (Ordered o') | o /= o' = Unordered
       canOnly _ mo = mo

lpoGround :: Precedence -> Order Term
lpoGround prec s@(Term f ss) t@(Term g ts) =
  (if (maximum (LT:[lpoGround prec si t | si <- ss]) /= LT)
     then GT else EQ)
  <>                
  (if (maximum (LT:[lpoGround prec ti s | ti <- ts]) /= LT)
     then LT else EQ)
  <> prec f g
  <> lexico (lpoGround prec) ss ts

-- LPO on non-ground terms.
-- The subterm/headsymbol/lex part actually works fine even if there might be variables,
-- just need to add base cases for var vs. term
lpo :: Precedence -> MbOrder Term
lpo _ (VarTerm v1) (VarTerm v2) = if v1 == v2 then Ordered EQ else Unordered
lpo _ (VarTerm v) t@(Term _ _) = if Set.member v (vars t) then Ordered LT else Unordered
lpo _ t@(Term _ _) (VarTerm v) = if Set.member v (vars t) then Ordered GT else Unordered
lpo prec s@(Term f ss) t@(Term g ts) =
  (if any (\si -> let o = lpo prec si t
                  in o == Ordered GT || o == Ordered EQ) ss
      then Ordered GT else Ordered EQ)
  <>
  (if any (\tj -> let o = lpo prec tj s
                  in o == Ordered GT || o == Ordered EQ) ts
      then Ordered LT else Ordered EQ)
  <> Ordered (prec f g)
  <> lexico (lpo prec) ss ts

{-
t = Term . Function
v = VarTerm . Var
-}

-- annotate term with weight, for faster kbo
data KBTerm label = KBTerm Int label [KBTerm label]
weight (KBTerm w _ _) = w

kboConst :: Order a -> Order (KBTerm a)
kboConst prec (KBTerm w1 f1 ts1) (KBTerm w2 f2 ts2) =
    compare w1 w2 <> prec f1 f2 <> lexico (kboConst prec) ts1 ts2

label :: (Function -> Int) -> Term -> KBTerm (Either Function Var)
label funWeight (VarTerm v) = KBTerm 1 (Right v) []
label funWeight (Term f ts) = KBTerm (funWeight f + sum (map weight ts')) (Left f) ts'
  where ts' = map (label funWeight) ts