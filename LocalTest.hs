import PatternUnify.Tm as Tm
import PatternUnify.Context as C
import PatternUnify.Test as PUtest
import qualified Unbound.LocallyNameless as LN

let x = Tm.vv "x"
let l = Tm.vv "l"
let tm = x Tm.$$ (Tm.Succ l )
let unif = C.EQN Tm.SET tm Tm.SET tm
let p1 = (C.P $ Tm.Nat Tm.--> Tm.SET)
let p2 = C.P Tm.Nat
let quantUnif = C.All p1 $ LN.bind (LN.s2n "x") $ C.All p2 $ LN.bind (LN.s2n "l") $ C.Unify unif
let entry = C.Prob (C.ProbId $ LN.s2n "prob") quantUnif C.Active
PUtest.solveEntries [entry]
