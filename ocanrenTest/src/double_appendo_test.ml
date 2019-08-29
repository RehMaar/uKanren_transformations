module L = List

(*
Исходная цель: doubleAppendo x1 x2 x3 x4

*)

open GT
open OCanren
open Std
open Nat

let topLevelCPD x0 x1 x2 x3 =
  let rec doubleAppendo y0 y1 y2 y3 =
    fresh (q1 q2 q3) 
          (y0 === nil ()
           &&& appendo y1 y2 y3
      ||| (y0 === q1 % q2
           &&& (y3 === q1 % q3)
           &&& appendoAppendo y1 y2 q2 q3))
  and appendo y4 y5 y6 =
    fresh (q1 q2 q3)
          (y4 === nil ()
           &&& (y6 === y5)
      ||| (y4 === q1 % q2
           &&& (y6 === q1 % q3)
           &&& appendo q2 y5 q3))
  and appendoAppendo y7 y8 y9 y11 =
    fresh (q1 q2 q3) 
          (y9 === nil ()
           &&& appendo y7 y8 y11
      ||| (y9 === q1 % q2
           &&& (y11 === q1 % q3)
           &&& appendoAppendo y7 y8 q2 q3))
  in doubleAppendo x0 x1 x2 x3

(*
Находит ответ, но потом зацикливается, в отличие от CPD.
*)
let topLevel x0 x1 x2 x3    = let rec doubleAppendo y0 y1 y2 y3 = fresh (q1 q2 q3) (y0 === q1 % q2 &&& appendo (q1 % q3) y2 y3 &&& appendo q2 y1 q3 ||| (y0 === nil () &&& appendo y1 y2 y3)) and appendo y4 y5 y6 = fresh (q1 q2 q3) ( y4 === q1 % q2 &&& (y6 === q1 % q3) &&& appendo q2 y5 q3 ||| (y4 === nil () &&& (y6 === y5))) in doubleAppendo x0 x1 x2 x3

(*
А вот этот вариант не зацикливается.
*)
let topLevelMy2 x0 x1 x2 x3 = let rec doubleAppendo y0 y1 y2 y3 = (fresh (q1 q2 q3) ((((y0 === nil ()) &&& (appendo y1 y2 y3)) ||| (((y0 === (q1 % q2)) &&& (appendo q2 y1 q3)) &&& (((q1 % q3) === (q1 % q3)) &&& (((y0 === (q1 % q2)) &&& ((q1 % q3) === (q1 % q3))) &&& (appendo ((q1 % q3)) y2 y3))))))) and appendo y4 y5 y6 = (fresh (q1 q2 q3) ((((y4 === nil ()) &&& (y6 === y5)) ||| (((y4 === (q1 % q2)) &&& (y6 === (q1 % q3))) &&& (appendo q2 y5 q3))))) in   (doubleAppendo x0 x1 x2 x3)


let x1 = ocanren([1; 2])
let x2 = ocanren([3; 4])
let x3 = ocanren([5; 6])

let result1 = run q (fun q -> topLevelCPD x1 x2 x3 q) (fun c -> c)
let result2 = run q (fun q -> topLevel x1 x2 x3 q) (fun c -> c)

let _ = L.iter (fun c -> Printf.printf "CPD: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take ~n:1 result1;
        L.iter (fun c -> Printf.printf "My:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take result2;
(*
let _ =
   let t1 = Sys.time() in
   let x = Stream.take ~n:10 result_resd in
   let t2 = Sys.time() in
   Printf.printf "%fs\n" (t2 -. t1);
   L.iter (fun c -> Printf.printf "%s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify)) @@ x
*)
