open GT
open MiniKanren
open Std
open Nat

let topLevel x0 x1 =
  let rec maxo y0 y1 = fresh (q1 q2 q3) (y0 === nil () &&& (y1 === zero) ||| (y0 === zero % q1 &&& maxo1 y1 q1) ||| (y0 === succ q2 % q3 &&& _maxo1 y1 q3 q2))
  and maxo1 y2 y3 = fresh (q1 q2 q3) (y3 === nil () &&& (y2 === zero) ||| (y3 === zero % q1 &&& maxo1 y2 q1) ||| (y3 === succ q2 % q3 &&& _maxo1 y2 q3 q2))
  and _maxo1 y4 y5 y6 =
    fresh (q1 q2 q3 q4) (y5 === nil () &&& (y4 === succ y6) ||| (y5 === q1 % q2 &&& leoMaxo1 y4 y6 q1 q2) ||| (y5 === succ q3 % q4 &&& gtoMaxo1 y4 q4 q3 y6))
  and leoMaxo1 y7 y8 y9 y10 = fresh q1 (y9 === zero &&& _maxo1 y7 y10 y8 ||| (y9 === succ q1 &&& (leo q1 y8 &&& _maxo1 y7 y10 y8)))
  and leo y11 y12 = fresh (q1 q2) (y11 === zero ||| (y11 === succ q1 &&& (y12 === succ q2) &&& leo q1 q2))
  and gtoMaxo1 y13 y14 y15 y16 =
    fresh (q1 q2 q3)
      (y15 === succ q1 &&& (y16 === zero) &&& _maxo1 y13 y14 (succ q1) ||| (y15 === succ q2 &&& (y16 === succ q3) &&& (gto q2 q3 &&& _maxo1 y13 y14 (succ q2))))
  and gto y17 y18 = fresh (q1 q2 q3) (y17 === succ q1 &&& (y18 === zero) ||| (y17 === succ q2 &&& (y18 === succ q3) &&& gto q2 q3)) in
  maxo x0 x1
