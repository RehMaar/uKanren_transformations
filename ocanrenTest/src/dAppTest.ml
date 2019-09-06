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

let topLevelSU x0 x1 x2 x3 =
  let rec doubleAppendo y0 y1 y2 y3 =
    fresh (q1 q2 q3) (y0 === nil () &&& appendo y1 y2 y3 ||| (y0 === q1 % q2 &&& (appendo q2 y1 q3 &&& appendo (q1 % q3) y2 y3)))
  and appendo y4 y5 y6 = fresh (q1 q2 q3) (y4 === nil () &&& (y6 === y5) ||| (y4 === q1 % q2 &&& (y6 === q1 % q3) &&& appendo q2 y5 q3)) in
  doubleAppendo x0 x1 x2 x3

let rec eqNat a b q23 =
  fresh (q24) (q24 === (pair a b))
    (conde
       [(q24 === (pair (z ()) (z ()))) &&& (q23 === (!! true));
       fresh (q26) (q24 === (pair (s q26) (z ()))) (q23 === (!! false));
       fresh (q28) (q24 === (pair (z ()) (s q28))) (q23 === (!! false));
       fresh (x y) (q24 === (pair (s x) (s y))) (eqNat x y q23)])

let eqPair a b q14 =
  fresh (q15 a1 a2 b1 b2 q16 q17) (q15 === (pair a b)) (q15 === (pair (pair a1 a2) (pair b1 b2))) (
    eqNat a1 b1 q16) (eqNat a2 b2 q17) (conde [(q16 === (!! false)) &&& (q14 === (!! false)); (q16 === (!! true)) &&& (q14 === q17)])

let rec elem x g q9 =
  ((g === (nil ())) &&& (q9 === (!! false))) |||
    (fresh (y ys q12) (g === (y % ys)) (eqPair x y q12) (conde [(q12 === (!! true)) &&& (q9 === (!! true)); (q12 === (!! false)) &&& (elem x ys q9)]))

let rec isPath c g q0 =
  (fresh (q1) (c === (q1 % (nil ()))) (q0 === (!! true))) |||
    (fresh (x1 x2 xs q3 q4) (c === (x1 % (x2 % xs))) (elem (pair x1 x2) g q3) (
       isPath (x2 % xs) g q4) (conde [(q3 === (!! false)) &&& (q0 === (!! false)); (q3 === (!! true)) &&& (q0 === q4)]))


let x1 = ocanren([1; 2])
let x2 = ocanren([3; 4])
let x3 = ocanren([5; 6])

let result1_cpd = run q (fun q -> topLevelCPD x1 x2 x3 q) (fun c -> c)
let result1_su  = run q (fun q -> topLevelSU  x1 x2 x3 q) (fun c -> c)


let x1 = ocanren([1])
let x2 = ocanren([2])
let x3 = ocanren([3])
let result2_cpd = run q (fun q -> topLevelCPD x1 x2 x3 q) (fun c -> c)
let result2_su  = run q (fun q -> topLevelSU  x1 x2 x3 q) (fun c -> c)

let result3_cpd = run q (fun q -> topLevelCPD (nil ()) (nil ()) (nil ()) q) (fun c -> c)
let result3_su  = run q (fun q -> topLevelSU  (nil ()) (nil ()) (nil ()) q) (fun c -> c)

let _ =
        Printf.printf "> Test 1: [1, 2] ++ [3, 4] ++ [5, 6]\n";
        L.iter (fun c -> Printf.printf "CPD: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take ~n:1 result1_cpd;
        L.iter (fun c -> Printf.printf "My:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take result1_su;
        Printf.printf "\n> Test 2: [1] ++ [2] ++ [3]\n";
        L.iter (fun c -> Printf.printf "CPD: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take ~n:1 result2_cpd;
        L.iter (fun c -> Printf.printf "My:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take result2_su;
        Printf.printf "\n> Test 3: [] ++ [] ++ []\n";
        L.iter (fun c -> Printf.printf "CPD: %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take ~n:1 result3_cpd;
        L.iter (fun c -> Printf.printf "My:  %s\n" @@ show(List.logic) (show(Nat.logic)) @@ c#reify (List.reify Nat.reify))
               @@  Stream.take result3_su


let x1 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])
let x2 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])
let x3 = ocanren([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20])

let result_cpd = run q (fun q -> topLevelCPD x1 x2 x3 q) (fun c -> c)
let result_su  = run q (fun q -> topLevelSU  x1 x2 x3 q) (fun c -> c)

let _ =
   let t1 = Sys.time() in
   let x = Stream.take result_cpd in
   let t2 = Sys.time() in
   let tcpd = t2 -. t1 in
   let t1 = Sys.time() in
   let x = Stream.take result_su in
   let t2 = Sys.time() in
   let tsu = t2 -. t1  in
   Printf.printf "CPD: %fs\n%!" tcpd;
   Printf.printf "SU:  %fs\n%!" tsu;
