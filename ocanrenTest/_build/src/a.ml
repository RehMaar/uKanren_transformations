module L = List

open GT
open OCanren
open Std
open Nat

let v = ocanren([1; 2])
let e = ocanren([(1, 1)])

let topLevel1 x0 x1 =
 let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& elemIsPath y1 q2 q3 q4))
 and elemIsPath y2 y3 y4 y5 =
   fresh (q1 q2 q3 q4 q5)
     ( y2
     === pair (zero) q1 % q2
     &&& (y3 === zero)
     &&& (___eqNat y4 q1 !!true &&& isPath (y4 % y5) (pair (zero) q1 % q2))
     ||| (y2 === pair (s q3) q1 % q2 &&& (y3 === s q4) &&& (___eqNat q4 q3 !!true &&& ___eqNat y4 q1 !!true &&& isPath (y4 % y5) (pair (s q3) q1 % q2)))
     ||| (y2 === q5 % q2 &&& (__eqPairElem y4 q5 q2 &&& isPath (y4 % y5) (q5 % q2))) )
 and eqPairElem y8 = fresh (q1 q2 q3 q4 q5) (_eqNatElem q1 q2 y8 q3 &&& ___eqNat q2 q4 q5 ||| (_eqNatElem q1 q2 q2 q4 &&& ___eqNat y8 q3 !!true))
 and eqNatElem y12 y13 y14 y15 =
   fresh (q1 q2 q3 q4)
     ( y13 === s q1
     &&& (y15 === zero)
     &&& ______elem y12 y14 (s q1)
     ||| (y13 === zero &&& (y15 === s q2) &&& ______elem y12 y14 (zero))
     ||| (y13 === s q3 &&& (y15 === s q4) &&& _eqNatElem y12 y14 q3 q4) )
 and _eqPairElem y21 =
   fresh (q1 q2 q3 q4)
     ( y21 === zero
     &&& ______elem q1 (zero) (zero)
     ||| (y21 === s q2 &&& ______elem q1 (s q2) (zero))
     ||| (y21 === zero &&& ______elem q1 (zero) (zero))
     ||| (y21 === s q3 &&& eqNatElem q1 q3 (s q3) q4)
     ||| (y21 === s q2 &&& ______elem q1 (s q2) (zero))
     ||| (y21 === zero &&& ______elem q1 (zero) (zero))
     ||| (y21 === s q3 &&& eqNatElem q1 q3 (s q3) q4) )
 and _eqNatElem y26 y27 y28 y29 =
   fresh (q1 q2 q3 q4)
     ( y28 === s q1
     &&& (y29 === zero)
     &&& ______elem y26 y27 (s (s q1))
     ||| (y28 === zero &&& (y29 === s q2) &&& ______elem y26 y27 (s (zero)))
     ||| (y28 === s q3 &&& (y29 === s q4) &&& _eqNatElem y26 y27 q3 q4) )
 and __eqPairElem y35 y36 y37 =
   fresh (q1 q2 q3 q4 q5 q6 q7)
     ( y36 === pair q1 q2
     &&& (eqNatElem y37 (s (zero)) y35 q1 &&& ___eqNat y35 q2 q3)
     ||| (y36 === pair (s (zero)) (zero) &&& (y35 === s q4) &&& ______elem y37 (s q4) (s (zero)))
     ||| (y36 === pair (s (zero)) (s q5) &&& (y35 === zero) &&& ______elem y37 (zero) (s (zero)))
     ||| (y36 === pair (s (zero)) (s q6) &&& (y35 === s q7) &&& _eqNatElem y37 (s q7) q7 q6) )
 and ______elem y43 y44 y45 =
   fresh (q1 q2 q3 q4 q5)
     ( y43
     === pair (zero) q1 % q2
     &&& (y45 === zero)
     &&& ___eqNat y44 q1 !!true
     ||| (y43 === pair (s q3) q1 % q2 &&& (y45 === s q4) &&& (___eqNat q4 q3 !!true &&& ___eqNat y44 q1 !!true))
     ||| (y43 === q5 % q2 &&& __eqPairElem y44 q5 q2) )
 and ___eqNat y46 y47 y48 =
   fresh (q1 q2 q3 q4)
     ( y46 === zero
     &&& (y47 === zero)
     &&& (y48 === !!true)
     ||| (y46 === s q1 &&& (y47 === zero) &&& (y48 === !!false))
     ||| (y46 === zero &&& (y47 === s q2) &&& (y48 === !!false))
     ||| (y46 === s q3 &&& (y47 === s q4) &&& ___eqNat q3 q4 y48) )
 in
 isPath x0 x1

let topLevel x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4 q5)
      ( y0
      === q1 % (q2 % q3)
      &&& elem q1 q2 y1
      &&& (y0 === q1 % (q2 % q3) &&& (!!true === !!true) &&& (!!true === !!true) &&& isPath q4 y1)
      ||| (y0 === q5 % nil ())
      ||| (y0 === nil ()) )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4)
      ( y4 === q1 % q2 &&& eqPair y2 y3 q1
      &&& (y2 % (y3 % q3) === y2 % (y3 % q3) &&& (!!true === !!true) &&& (!!true === !!true) &&& (y4 === q1 % q2) &&& (!!false === !!false) &&& elem y2 y3 q4)
      ||| (y4 === q1 % q2 &&& eqPair y2 y3 q1) )
  and eqPair y5 y6 y7 = fresh (q1 q2) (y7 === pair q1 q2 &&& eqNatEqNat y5 q1 y6 q2)
  and eqNatEqNat y8 y9 y10 y11 =
    fresh (q1 q2) (y8 === s q1 &&& (y9 === s q2) &&& eqNatEqNat q1 q2 y10 y11 ||| (y8 === zero &&& (y9 === zero) &&& eqNat y10 y11))
  and eqNat y12 y13 = fresh (q1 q2) (y12 === s q1 &&& (y13 === s q2) &&& eqNat q1 q2 ||| (y12 === zero &&& (y13 === zero))) in
  isPath x0 x1

(*
let topLevel x0 x1 x2 =
  let rec isPath y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5)
      ( y0
      === q1 % (q2 % q3)
      &&& elemIsPath q1 q2 y1 q3 y2
      ||| (y0 === q1 % (q2 % q3) &&& (y2 === !!false) &&& elemIsPath q1 q2 y1 q3 q4)
      ||| (y0 === q5 % nil () &&& (y2 === !!true))
      ||| (y0 === nil () &&& (y2 === !!true)) )
  and elemIsPath y3 y4 y5 y6 y7 =
    fresh (q1 q2) (elem y3 y4 y5 &&& (y3 % (y4 % y6) === y3 % (y4 % y6) &&& (!!false === !!false) &&& (!!false === !!false) &&& isPath q1 y5 q2))
  and elem y8 y9 y10 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y8 % (y9 % q1)
      === y8 % (y9 % q1)
      &&& (!!false === !!false) &&& (!!false === !!false)
      &&& (y10 === q2 % q3)
      &&& (!!false === !!false)
      &&& (q2 === pair q4 q5)
      &&& eqNatEqNat y8 q4 y9 q5
      ||| ( y8 % (y9 % q1)
          === y8 % (y9 % q1)
          &&& (!!false === !!false) &&& (!!false === !!false)
          &&& (y10 === q2 % q3)
          &&& (!!false === !!false)
          &&& (q2 === pair q4 q5)
          &&& _eqNatEqNat y8 q4 y9 q5 )
      &&& (y10 === q2 % q3 &&& elem y8 y9 q6)
      ||| (y10 === nil ()) )
  and eqNatEqNat y11 y12 y13 y14 =
    fresh (q1 q2) (y11 === s q1 &&& (y12 === s q2) &&& eqNatEqNat q1 q2 y13 y14 ||| (y11 === zero &&& (y12 === zero) &&& eqNat y13 y14))
  and eqNat y15 y16 =
    fresh (q1 q2 q3 q4) (y15 === s q1 &&& (y16 === s q2) &&& eqNat q1 q2 ||| (y15 === zero &&& (y16 === s q3)) ||| (y15 === s q4 &&& (y16 === zero)))
  and _eqNatEqNat y17 y18 y19 y20 =
    fresh (q1 q2 q3 q4)
      ( y17 === s q1
      &&& (y18 === s q2)
      &&& _eqNatEqNat q1 q2 y19 y20
      ||| (y17 === zero &&& (y18 === s q3) &&& _eqNat y19 y20)
      ||| (y17 === s q4 &&& (y18 === zero) &&& _eqNat y19 y20) )
  and _eqNat y22 y23 =
    fresh (q1 q2 q3 q4)
      ( y22 === s q1
      &&& (y23 === s q2)
      &&& _eqNat q1 q2
      ||| (y22 === zero &&& (y23 === s q3))
      ||| (y22 === s q4 &&& (y23 === zero))
      ||| (y22 === zero &&& (y23 === zero)) )
  in
  isPath x0 x1 x2
*)

let result = run q (fun q -> topLevel1 q e) (fun c -> c)

let _ = Printf.printf "Work\n";
   let t1 = Sys.time() in
   let x = Stream.take ~n:10 result in
   let t2 = Sys.time() in
   Printf.printf "%fs\n" (t2 -. t1);
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
