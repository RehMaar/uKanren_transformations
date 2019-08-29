(*
Запрос: Path.query1.
*)


module L = List

open GT
open OCanren
open Std
open Nat

let topLevelCPD x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& elemIsPath y1 q2 q3 q4))
  and elemIsPath y2 y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y2
      === pair q1 q2 % q3
      &&& (___eqNat y3 q1 !!true &&& ___eqNat y4 q2 !!true &&& isPath (y4 % y5) (pair q1 q2 % q3))
      ||| (y2 === q4 % q3 &&& (eqPairElem y3 y4 q4 q3 &&& isPath (y4 % y5) (q4 % q3))) )
  and eqPairElem y10 y11 y12 y13 =
    fresh (q1 q2 q3)
      ( y12 === pair q1 q2
      &&& (eqNatElem y13 y10 y11 q1 &&& ___eqNat y11 q2 q3)
      ||| (y12 === pair q1 q2 &&& (___eqNat y10 q1 !!true &&& ___eqNat y11 q2 !!false &&& ____elem y13 y11 y10)) )
  and eqNatElem y14 y15 y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y15 === s q1 &&& (y17 === zero)
      &&& ____elem y14 y16 (s q1)
      ||| (y15 === zero &&& (y17 === s q2) &&& ____elem y14 y16 zero)
      ||| (y15 === s q3 &&& (y17 === s q4) &&& _eqNatElem y14 y16 q3 q4) )
  and _eqNatElem y26 y27 y28 y29 =
    fresh (q1 q2 q3 q4)
      ( y28 === s q1 &&& (y29 === zero)
      &&& ____elem y26 y27 (s (s q1))
      ||| (y28 === zero &&& (y29 === s q2) &&& ____elem y26 y27 (s zero))
      ||| (y28 === s q3 &&& (y29 === s q4) &&& (___eqNat q3 q4 !!false &&& ____elem y26 y27 (s (s q3)))) )
  and ____elem y39 y40 y41 =
    fresh (q1 q2 q3 q4) (y39 === pair q1 q2 % q3 &&& (___eqNat y41 q1 !!true &&& ___eqNat y40 q2 !!true) ||| (y39 === q4 % q3 &&& eqPairElem y41 y40 q4 q3))
  and ___eqNat y42 y43 y44 =
    fresh (q1 q2 q3 q4)
      ( y42 === zero &&& (y43 === zero) &&& (y44 === !!true)
      ||| (y42 === s q1 &&& (y43 === zero) &&& (y44 === !!false))
      ||| (y42 === zero &&& (y43 === s q2) &&& (y44 === !!false))
      ||| (y42 === s q3 &&& (y43 === s q4) &&& ___eqNat q3 q4 y44) )
  in
  isPath x0 x1

let topLevelMy x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4)
      ( y0 === q1 % (q2 % q3)
      &&& elem q1 q2 y1
      &&& (y0 === q1 % (q2 % q3)
      &&& isPath (q2 % q3) y1)
      ||| (y0 === q4 % nil () ||| (y0 === nil ())) )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4)
      ( y4 === q1 % q2 &&& eqPair y2 y3 q1
      &&& (y4 === q1 % q2) &&& elem y2 y3 q2
      ||| (y4 === q1 % q4 &&& eqPair y2 y3 q1) )
  and eqPair y5 y6 y7 = fresh (q1 q2) (y7 === pair q1 q2 &&& eqNatEqNat y5 q1 y6 q2)
  and eqNatEqNat y8 y9 y10 y11 =
    fresh (q1 q2) (y8 === s q1 &&& (y9 === s q2) &&& eqNatEqNat q1 q2 y10 y11 ||| (y8 === zero &&& (y9 === zero) &&& eqNat y10 y11))
  and eqNat y12 y13 = fresh (q1 q2) (y12 === s q1 &&& (y13 === s q2) &&& eqNat q1 q2 ||| (y12 === zero &&& (y13 === zero))) in
  isPath x0 x1

let topLevelMyNew x0 x1 =
  let rec isPath y0 y1 =
    fresh (q1 q2 q3 q4)
      ( y0 === nil ()
      ||| ( y0 === q1 % nil ()
      ||| (y0 === q2 % (q3 % q4) &&& isPath (q3 % q4) y1 &&& (y0 === q2 % (q3 % q4) &&& elem q2 q3 y1)) )
      )
  and elem y2 y3 y4 =
    fresh (q1 q2 q3 q4)
      ( y4 === q1 % q2 &&& eqPair y2 y3 q1
      ||| ( y4 === q1 % q3 &&& elem y2 y3 q3
          &&& ( y2 % (y3 % q4)
              === y2 % (y3 % q4)
              &&& (!!true === !!true) &&& (!!true === !!true)
              &&& (y4 === q1 % q3)
              &&& (!!false === !!false) &&& eqPair y2 y3 q1 ) ) )
  and eqPair y5 y6 y7 = fresh (q1 q2) (y7 === pair q1 q2 &&& eqNatEqNat y5 q1 y6 q2)
  and eqNatEqNat y8 y9 y10 y11 =
    fresh (q1 q2) (y8 === zero &&& (y9 === zero) &&& eqNat y10 y11 ||| (y8 === s q1 &&& (y9 === s q2) &&& eqNatEqNat q1 q2 y10 y11))
  and eqNat y12 y13 = fresh (q1 q2) (y12 === zero &&& (y13 === zero) ||| (y12 === s q1 &&& (y13 === s q2) &&& eqNat q1 q2)) in
  isPath x0 x1


let topLevel x0 x1 = let rec isPath y0 y1 = (fresh (q1 q2 q3 q4) (((y0 === nil ()) ||| ((y0 === (q1 % nil ())) ||| (((y0 === (q2 % (q3 % q4))) &&& (isPath ((q3 % q4)) y1)) &&& ((((y0 === (q2 % (q3 % q4))) &&& (!!true === !!true)) &&& (!!true === !!true)) &&& (elem q2 q3 y1))))))) and elem y2 y3 y4 =
 (fresh (q1 q2 q3) ((((y4 === (q1 % q2)) &&& (eqPair y2 y3 q1)) ||| (((y4 === (q1 % q3)) &&& (elem y2 y3 q3)) &&& (((y4 === (q1 % q3)) &&& (!!false === !!false)) &&& (eqPair y2 y3 q1)))))) and eqPair y5 y6 y7 = (fresh (q1 q2) (((y7 === (pair q1 q2)) &&& (eqNatEqNat y5 q1 y6 q2)))) and eqNatEqNat y8
 y9 y10 y11 = (fresh (q1 q2) (((((y8 === zero) &&& (y9 === zero)) &&& (eqNat y10 y11)) ||| (((y8 === s (q1)) &&& (y9 === s (q2))) &&& (eqNatEqNat q1 q2
 y10 y11))))) and eqNat y12 y13 = (fresh (q1 q2) ((((y12 === zero) &&& (y13 === zero)) ||| (((y12 === s (q1)) &&& (y13 === s (q2))) &&& (eqNat q1 q2))))) in      (isPath x0 x1)

let loop = ocanren([(1, 1)])

let result_cpd_1 = run q (fun q -> topLevelCPD q loop) id
let result_my_1 = run q (fun q -> topLevel q loop) id

let dag = ocanren([(1, 2); (2, 3)])

let result_cpd_2 = run q (fun q -> topLevelCPD q dag) id
let result_my_2 = run q (fun q -> topLevel q dag ) id

let g = ocanren([(1, 2); (2, 3); (3, 1)])

let result_cpd_3 = run q (fun q -> topLevelCPD q g) id
let result_my_3 = run q (fun q -> topLevel q g) id


let _ = 
(*   L.iter (fun c -> Printf.printf "CPD loop: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:4 result_cpd_1;
   L.iter (fun c -> Printf.printf "My loop: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:4 result_my_1;
   Printf.printf "\n";*)

   let x =  Stream.take result_cpd_2 in
   Printf.printf "Answers for CPD: %d\n" @@ L.length x;
   L.iter (fun c -> Printf.printf "CPD dag: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ x;
(*   let x =  Stream.take ~n:4 result_my_2 in
   Printf.printf "Answers for My: %d\n" @@ L.length x;
   L.iter (fun c -> Printf.printf "My dag: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ x;
   Printf.printf "\n";*)
(*
   L.iter (fun c -> Printf.printf "CPD g: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:5 result_cpd_3;*)
   L.iter (fun c -> Printf.printf "My g: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
   @@ Stream.take ~n:3 result_my_3



(*
let _ =
   let t1 = Sys.time() in
   let x = Stream.take ~n:10 result_resd in
   let t2 = Sys.time() in
   Printf.printf "%fs\n" (t2 -. t1);
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
*)

