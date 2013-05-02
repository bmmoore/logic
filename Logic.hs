module Logic where
import Logic.Pretty() -- for Pretty instance
import Logic.Parse
import Logic.Formula
import Logic.CNF
import Logic.Skolem
import Logic.Resolution

import Control.Monad.State
import Text.PrettyPrint.Leijen(pretty)
import Text.ParserCombinators.Parsec

parsef = parse formula "<interactive>"

prepare f = clausify . liftUniversal . skol . existentialClosure . struct . nnf $ f

skol :: Formula -> Formula
skol = fst . flip runState (0,[]) . unSkolM . skolemize

struct :: Formula -> Formula
struct = fst . flip runState (0,[]) . unStructM . structTrans

f = "(~forall y . (a(?x) /\\ b(?y))) \\/ exists z . c(?x,?z)"