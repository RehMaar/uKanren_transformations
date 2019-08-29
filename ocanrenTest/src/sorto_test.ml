(*
Порождённая CPD программа не комилируется. Какая-то ошибка в резидуализации.
My на тестах отработал нормально, всё завершается.
*)


module L = List

open GT
open OCanren
open Std
open Nat

(*let topLevelCPD x0 x1 =
  let rec sorto y0 y1 = fresh (q1 q2) (y0 === nil () &&& (y1 === nil ()) ||| (y1 === q1 % q2 &&& sortoSmallesto y0 q1 q2))
  and sortoSmallesto y2 y3 y5 =
    fresh (q1 q2 q3) (y5 === nil () &&& (y2 === y3 % nil ()) ||| (y5 === q1 % q2 &&& (smallestoSmallesto y2 y3 q1 q3 &&& sorto q3 q2)))
  and smallestoSmallesto y6 y7 y9 y10 =
    fresh (q1 q2 q3 q4 q5)
      (y10 === nil () &&& (y6 === q1 % (q2 % nil ())) ||| (y10 === q3 % q4 &&& (y6 === q1 % q5) &&& minmaxoSmallestoMinmaxoSmallesto y7 y9 q4 q3 q1 q5))
  and minmaxoSmallestoMinmaxoSmallesto y11 y12 y14 y15 y16 y17 =
    fresh (q1) (leoMinmaxo y11 y15 y16 q1 y12 &&& smallestoSmallesto y17 q1 y15 y14 ||| (gtoMinmaxo y11 y12 y16 q1 y15 &&& smallestoSmallesto y17 q1 y12 y14))
  and leoMinmaxo y21 y22 y23 y24 y25 =
    fresh (q1 q2) (y25 === zero &&& _____minmaxo y21 y23 y24 zero ||| (y25 === succ q1 &&& (y22 === succ q2) &&& _leoMinmaxo y21 y23 y24 q1 q2))
  and _leoMinmaxo y29 y30 y31 y32 y33 =
    fresh (q1 q2)
      ( y32 === zero
      &&& _____minmaxo y29 y30 y31 (succ zero)
      ||| (y32 === succ q1 &&& (y33 === succ q2) &&& (_______leo q1 q2 &&& _____minmaxo y29 y30 y31 (succ (succ q1)))) )
  and _____minmaxo y41 y42 y43 y44 = y41 === y42 &&& (y44 === y43) &&& _______leo y42 y43 ||| (y44 === y42 &&& (y41 === y43) &&& ______gto y42 y43)
  and gtoMinmaxo y47 y48 y49 y50 y51 =
    fresh (q1 q2 q3)
      (y51 === succ q1 &&& (y48 === zero) &&& _____minmaxo y47 y49 y50 (succ q1) ||| (y51 === succ q2 &&& (y48 === succ q3) &&& _gtoMinmaxo y47 y49 y50 q2 q3))
  and _gtoMinmaxo y64 y65 y66 y67 y68 =
    fresh (q1 q2 q3)
      ( y67 === succ q1 &&& (y68 === zero)
      &&& _____minmaxo y64 y65 y66 (succ (succ q1))
      ||| (y67 === succ q2 &&& (y68 === succ q3) &&& (______gto q2 q3 &&& _____minmaxo y64 y65 y66 (succ (succ q2)))) )
  and ______gto y83 y84 = fresh (q1 q2 q3) (y83 === succ q1 &&& (y84 === zero) ||| (y83 === succ q2 &&& (y84 === succ q3) &&& ______gto q2 q3))
  and _____minmaxo y85 y86 y87 y88 = y85 === y86 &&& (y88 === y87) &&& _______leo y86 y87 ||| (y88 === y86 &&& (y85 === y87) &&& ______gto y86 y87)
  and _______leo y89 y90 = fresh (q1 q2) (y89 === zero ||| (y89 === succ q1 &&& (y90 === succ q2) &&& _______leo q1 q2)) in
  sorto x0 x1*)


let topLevelMy x0 x1 =
  let rec sorto y0 y1 = fresh (q1 q2 q3) (y1 === q1 % q2 &&& smallesto y0 q1 q3 &&& (y1 === q1 % q2 &&& sorto q3 q2) ||| (y0 === nil () &&& (y1 === nil ())))
  and smallesto y2 y3 y4 =
    fresh (q1 q2 q3 q4 q5 q6)
      ( y3 % q1 === y3 % q1
      &&& (y4 === q2 % q3)
      &&& (y2 === q4 % q5)
      &&& (q2 === q4) &&& (y3 === q6) &&& gto q4 q6
      ||| (y3 % q1 === y3 % q1 &&& (y4 === q2 % q3) &&& (y2 === q4 % q5) &&& (y3 === q4) &&& (q2 === q6) &&& leo q4 q6)
      &&& (y4 === q2 % q3 &&& (y2 === q4 % q5) &&& smallesto q5 q6 q3)
      ||| (y2 === y3 % nil () &&& (y4 === nil ())) )
  and gto y5 y6 = fresh (q1 q2 q3) (y5 === succ q1 &&& (y6 === succ q2) &&& gto q1 q2 ||| (y5 === succ q3 &&& (y6 === zero)))
  and leo y7 y8 = fresh (q1 q2) (y7 === succ q1 &&& (y8 === succ q2) &&& leo q1 q2 ||| (y7 === zero)) in
  sorto x0 x1


(* Находит ответ, но не завершается. *)
let topLevelMy2 x0 x1 = let rec sorto y0 y1 = (fresh (q1 q2 q3) ((((y0 === nil ()) &&& (y1 === nil ())) ||| (((y1 === (q1 % q2)) &&& (sorto q3 q2)) &&& (
(y1 === (q1 % q2)) &&& (smallesto y0 q1 q3)))))) and smallesto y2 y3 y4 = (fresh (q1 q2 q3 q4 q5) ((((y2 === (y3 % nil ())) &&& (y4 === nil ())) ||| ((((y4 === (q1 % q2)) &&& (y2 === (q3 % q4))) &&& (smallesto q4 q5 q2)) &&& ((((((y4 === (q1 % q2)) &&& (y2 === (q3 % q4))) &&& (y3 === q3)) &&& (q1 === q5)) &&& (leo q3 q5)) ||| (((((y4 === (q1 % q2)) &&& (y2 === (q3 % q4))) &&& (q1 === q3)) &&& (y3 === q5)) &&& (gto q3 q5))))))) and leo y5 y6 = (fresh (q1 q2) (((y5 === zero) ||| (((y5 === succ (q1)) &&& (y6 === succ (q2))) &&& (leo q1 q2))))) and gto y7 y8 = (fresh (q1 q2 q3) ((((y7 === succ (q1)) &&& (y8 === zero)) ||| (((y7 === succ (q2)) &&& (y8 === succ (q3))) &&& (gto q2 q3))))) in     (sorto x0 x1)


let x1 = ocanren([1; 0; 0; 1])
let x2 = ocanren([1; 2; 3; 5])
let x3 = ocanren([5; 3; 2; 1])

(*let result1 = run q (fun q -> topLevelCPD x1 q) id *)
let result21 = run q (fun q -> topLevelMy2  x1 q) id
let result22 = run q (fun q -> topLevelMy2  x2 q) id
let result23 = run q (fun q -> topLevelMy2  x3 q) id

let _ =
(*   L.iter (fun c -> Printf.printf "CPD: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ result1 *)
     L.iter (fun c -> Printf.printf "My1:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
     @@ Stream.take ~n:1 result21;
     L.iter (fun c -> Printf.printf "My2:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
     @@ Stream.take ~n:1 result22;
     L.iter (fun c -> Printf.printf "My3:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
     @@ Stream.take ~n:1 result23


(*
let _ =
   let t1 = Sys.time() in
   let x = Stream.take ~n:10 result_resd in
   let t2 = Sys.time() in
   Printf.printf "%fs\n" (t2 -. t1);
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
*)
