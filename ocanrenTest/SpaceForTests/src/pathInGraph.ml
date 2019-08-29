open GT
open OCanren
open Std

type 'a0 gnat =
  | Z 
  | S of 'a0 
let rec fmap fa0 = function | Z -> Z | S a0 -> S (fa0 a0)
module For_gnat = (Fmap)(struct let rec fmap fa0 = function | Z -> Z | S a0 -> S (fa0 a0)
                                type 'a0 t = 'a0 gnat end)
let rec z () = inj (For_gnat.distrib Z)
and s x__0 = inj (For_gnat.distrib (S x__0))





let rec eqNat a b q24 =
  fresh (q25) (q25 === (pair a b))
    (conde
       [(q25 === (pair (z ()) (z ()))) &&& (q24 === (!! true));
       fresh (q27) (q25 === (pair (s q27) (z ()))) (q24 === (!! false));
       fresh (q29) (q25 === (pair (z ()) (s q29))) (q24 === (!! false));
       fresh (x y) (q25 === (pair (s x) (s y))) (eqNat x y q24)])
let eqPair a b q15 =
  fresh (q16 a1 a2 b1 b2 q17 q18) (q16 === (pair a b)) (q16 === (pair (pair a1 a2) (pair b1 b2))) (
    eqNat a1 b1 q17) (eqNat a2 b2 q18) (conde [(q17 === (!! false)) &&& (q15 === (!! false)); (q17 === (!! true)) &&& (q15 === q18)])
let rec elem x g q10 =
  ((g === (nil ())) &&& (q10 === (!! false))) |||
    (fresh (y ys q13) (g === (y % ys)) (eqPair x y q13) (conde [(q13 === (!! true)) &&& (q10 === (!! true)); (q13 === (!! false)) &&& (elem x ys q10)]))
let rec isPath c g q0 =
  conde
    [(c === (nil ())) &&& (q0 === (!! true));
    fresh (q2) (c === (q2 % (nil ()))) (q0 === (!! true));
    fresh (x1 x2 xs q4 q5) (c === (x1 % (x2 % xs))) (elem (pair x1 x2) g q4) (
      isPath (x2 % xs) g q5) (conde [(q4 === (!! false)) &&& (q0 === (!! false)); (q4 === (!! true)) &&& (q0 === q5)])]





let topLevel x0 x1 =
 let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& elemIsPath y1 q2 q3 q4))
 and elemIsPath y2 y3 y4 y5 =
   fresh (q1 q2 q3 q4 q5)
     ( y2
     === pair (z ()) q1 % q2
     &&& (y3 === z ())
     &&& (___eqNat y4 q1 !!true &&& isPath (y4 % y5) (pair (z ()) q1 % q2))
     ||| (y2 === pair (s q3) q1 % q2 &&& (y3 === s q4) &&& (___eqNat q4 q3 !!true &&& ___eqNat y4 q1 !!true &&& isPath (y4 % y5) (pair (s q3) q1 % q2)))
     ||| (y2 === q5 % q2 &&& (__eqPairElem y4 q5 q2 &&& isPath (y4 % y5) (q5 % q2))) )
 and eqPairElem y8 = fresh (q1 q2 q3 q4 q5) (_eqNatElem q1 q2 y8 q3 &&& ___eqNat q2 q4 q5 ||| (_eqNatElem q1 q2 q2 q4 &&& ___eqNat y8 q3 !!true))
 and eqNatElem y12 y13 y14 y15 =
   fresh (q1 q2 q3 q4)
     ( y13 === s q1
     &&& (y15 === z ())
     &&& ______elem y12 y14 (s q1)
     ||| (y13 === z () &&& (y15 === s q2) &&& ______elem y12 y14 (z ()))
     ||| (y13 === s q3 &&& (y15 === s q4) &&& _eqNatElem y12 y14 q3 q4) )
 and _eqPairElem y21 =
   fresh (q1 q2 q3 q4)
     ( y21 === z ()
     &&& ______elem q1 (z ()) (z ())
     ||| (y21 === s q2 &&& ______elem q1 (s q2) (z ()))
     ||| (y21 === z () &&& ______elem q1 (z ()) (z ()))
     ||| (y21 === s q3 &&& eqNatElem q1 q3 (s q3) q4)
     ||| (y21 === s q2 &&& ______elem q1 (s q2) (z ()))
     ||| (y21 === z () &&& ______elem q1 (z ()) (z ()))
     ||| (y21 === s q3 &&& eqNatElem q1 q3 (s q3) q4) )
 and _eqNatElem y26 y27 y28 y29 =
   fresh (q1 q2 q3 q4)
     ( y28 === s q1
     &&& (y29 === z ())
     &&& ______elem y26 y27 (s (s q1))
     ||| (y28 === z () &&& (y29 === s q2) &&& ______elem y26 y27 (s (z ())))
     ||| (y28 === s q3 &&& (y29 === s q4) &&& _eqNatElem y26 y27 q3 q4) )
 and __eqPairElem y35 y36 y37 =
   fresh (q1 q2 q3 q4 q5 q6 q7)
     ( y36 === pair q1 q2
     &&& (eqNatElem y37 (s (z ())) y35 q1 &&& ___eqNat y35 q2 q3)
     ||| (y36 === pair (s (z ())) (z ()) &&& (y35 === s q4) &&& ______elem y37 (s q4) (s (z ())))
     ||| (y36 === pair (s (z ())) (s q5) &&& (y35 === z ()) &&& ______elem y37 (z ()) (s (z ())))
     ||| (y36 === pair (s (z ())) (s q6) &&& (y35 === s q7) &&& _eqNatElem y37 (s q7) q7 q6) )
 and ______elem y43 y44 y45 =
   fresh (q1 q2 q3 q4 q5)
     ( y43
     === pair (z ()) q1 % q2
     &&& (y45 === z ())
     &&& ___eqNat y44 q1 !!true
     ||| (y43 === pair (s q3) q1 % q2 &&& (y45 === s q4) &&& (___eqNat q4 q3 !!true &&& ___eqNat y44 q1 !!true))
     ||| (y43 === q5 % q2 &&& __eqPairElem y44 q5 q2) )
 and ___eqNat y46 y47 y48 =
   fresh (q1 q2 q3 q4)
     ( y46 === z ()
     &&& (y47 === z ())
     &&& (y48 === !!true)
     ||| (y46 === s q1 &&& (y47 === z ()) &&& (y48 === !!false))
     ||| (y46 === z () &&& (y47 === s q2) &&& (y48 === !!false))
     ||| (y46 === s q3 &&& (y47 === s q4) &&& ___eqNat q3 q4 y48) )
 in
 isPath x0 x1





let topLevel1 x0 x1 =
  let rec isPath y0 y1 = fresh (q1 q2 q3 q4) (y0 === nil () ||| (y0 === q1 % nil ()) ||| (y0 === q2 % (q3 % q4) &&& elemIsPath y1 q2 q3 q4))
  and elemIsPath y2 y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y2
      === pair q1 q2 % q3
      &&& (___eqNat y3 q1 !!true &&& ___eqNat y4 q2 !!true &&& isPath (y4 % y5) (pair q1 q2 % q3))
      ||| (y2 === q4 % q3 &&& (__eqPairElem y4 q4 q3 &&& isPath (y4 % y5) (q4 % q3))) )
  and eqPairElem y10 = fresh (q1 q2 q3 q4 q5) (_eqNatElem q1 q2 y10 q3 &&& ___eqNat q2 q4 q5 ||| (_eqNatElem q1 q2 q2 q4 &&& ___eqNat y10 q3 !!true))
  and eqNatElem y14 y15 y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y15 === s q1
      &&& (y17 === z ())
      &&& ____elem y14 y16 (s q1)
      ||| (y15 === z () &&& (y17 === s q2) &&& ____elem y14 y16 (z ()))
      ||| (y15 === s q3 &&& (y17 === s q4) &&& _eqNatElem y14 y16 q3 q4) )
  and _eqNatElem y26 y27 y28 y29 =
    fresh (q1 q2 q3 q4)
      ( y28 === s q1
      &&& (y29 === z ())
      &&& ____elem y26 y27 (s (s q1))
      ||| (y28 === z () &&& (y29 === s q2) &&& ____elem y26 y27 (s (z ())))
      ||| (y28 === s q3 &&& (y29 === s q4) &&& _eqNatElem y26 y27 q3 q4) )
  and __eqPairElem y35 y36 y37 =
    fresh (q1 q2 q3)
      (y36 === pair q1 q2 &&& (eqNatElem y37 (s (z ())) y35 q1 &&& ___eqNat y35 q2 q3) ||| (y36 === pair (s (z ())) q2 &&& _eqNatElem y37 y35 y35 q2))
  and ____elem y39 y40 y41 =
    fresh (q1 q2 q3 q4) (y39 === pair q1 q2 % q3 &&& (___eqNat y41 q1 !!true &&& ___eqNat y40 q2 !!true) ||| (y39 === q4 % q3 &&& __eqPairElem y40 q4 q3))
  and ___eqNat y42 y43 y44 =
    fresh (q1 q2 q3 q4)
      ( y42 === z ()
      &&& (y43 === z ())
      &&& (y44 === !!true)
      ||| (y42 === s q1 &&& (y43 === z ()) &&& (y44 === !!false))
      ||| (y42 === z () &&& (y43 === s q2) &&& (y44 === !!false))
      ||| (y42 === s q3 &&& (y43 === s q4) &&& ___eqNat q3 q4 y44) )
  in
  isPath x0 x1





let pathECCE y1 y2 y3 =
 let rec isPath z1 z2 z3 = fresh (fB fA) (z1 === fA &&& (z2 === fB) &&& (z3 === !!true) &&& isPath__1 fA fB)
 and isPath__1 z1 z2 =
   fresh (fA) (z1 === nil () &&& (z2 === fA))
   ||| fresh (fB fA) (z1 === fA % nil () &&& (z2 === fB))
   ||| fresh (fE fD fC fB fA) (z1 === fA % (fB % fC) &&& (z2 === fD % fE) &&& elem_conj__2 fA fB fD fE fC fD fE)
 and elem_conj__2 z1 z2 z3 z4 z5 z6 z7 =
   fresh (fH fG fF fE fD fC fB fA)
     ( z1 === fA &&& (z2 === fB)
     &&& (z3 === pair fC fD)
     &&& (z4 === fE) &&& (z5 === fF) &&& (z6 === fG) &&& (z7 === fH) &&& eqNat__4 fA fC &&& eqNat__4 fB fD &&& isPath__7 fB fF fG fH )
   ||| fresh (fI fH fG fF fE fD fC fB fA)
         ( z1 === fA &&& (z2 === fB)
         &&& (z3 === pair fC fD)
         &&& (z4 === fE % fF)
         &&& (z5 === fG) &&& (z6 === fH) &&& (z7 === fI) &&& eqPair_conj__3 fA fB fC fD fE fF fG fH fI )
 and eqPair_conj__3 z1 z2 z3 z4 z5 z6 z7 z8 z9 =
   fresh (fI fH fG fF fE fD fC fB fA)
     ( z1 === fA &&& (z2 === fB) &&& (z3 === fC) &&& (z4 === fD) &&& (z5 === fE) &&& (z6 === fF) &&& (z7 === fG) &&& (z8 === fH) &&& (z9 === fI)
     &&& eqNat__5 fA fC &&& eqNat__6 fB fD &&& elem_conj__2 fA fB fE fF fG fH fI )
   ||| fresh (fI fH fG fF fE fD fC fB fA)
         ( z1 === fA &&& (z2 === fB) &&& (z3 === fC) &&& (z4 === fD) &&& (z5 === fE) &&& (z6 === fF) &&& (z7 === fG) &&& (z8 === fH) &&& (z9 === fI)
         &&& eqNat__4 fA fC &&& eqNat__5 fB fD &&& elem_conj__2 fA fB fE fF fG fH fI )
 and eqNat__4 z1 z2 = z1 === z () &&& (z2 === z ()) ||| fresh (fB fA) (z1 === s fA &&& (z2 === s fB) &&& eqNat__4 fA fB)
 and eqNat__5 z1 z2 =
   fresh (fA) (z1 === s fA &&& (z2 === z ())) ||| fresh (fA) (z1 === z () &&& (z2 === s fA)) ||| fresh (fB fA) (z1 === s fA &&& (z2 === s fB) &&& eqNat__5 fA fB)
 and eqNat__6 z1 z2 =
   z1 === z ()
   &&& (z2 === z ())
   ||| fresh (fA) (z1 === s fA &&& (z2 === z ()))
   ||| fresh (fA) (z1 === z () &&& (z2 === s fA))
   ||| fresh (fB fA) (z1 === s fA &&& (z2 === s fB) &&& eqNat__6 fA fB)
 and isPath__7 z1 z2 z3 z4 =
   fresh (fC fB fA) (z1 === fA &&& (z2 === nil ()) &&& (z3 === fB) &&& (z4 === fC))
   ||| fresh (fE fD fC fB fA) (z1 === fA &&& (z2 === fB % fC) &&& (z3 === fD) &&& (z4 === fE) &&& elem_conj__2 fA fB fD fE fC fD fE)
 in
 isPath y1 y2 y3


let topLevelMy x0 x1 x2 =
  let rec isPath y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5)
      ( y0 === nil () &&& (y2 === !!true)
      ||| (y0 === q1 % nil () &&& (y2 === !!true))
      ||| ( y0
          === q2 % (q3 % q4)
          &&& (y2 === !!false)
          &&& isPath (q3 % q4) y1 q5
          &&& (y0 === q2 % (q3 % q4) &&& (!!false === !!false) &&& (y2 === !!false) &&& elem q2 q3 y1) )
      ||| (y0 === q2 % (q3 % q4) &&& isPath (q3 % q4) y1 y2 &&& (y0 === q2 % (q3 % q4) &&& (!!true === !!true) &&& (y2 === y2) &&& elem q2 q3 y1)) )
  and elem y3 y4 y5 =
    fresh (q1 q2 q3 q4)
      ( y5 === nil ()
      ||| ( y5 === q1 % q2 &&& elem y3 y4 q2
          &&& ( y5 === q1 % q2 &&& (!!false === !!false)
              &&& (q1 === pair q3 q4)
              &&& eqNatEqNat y3 q3 y4 q4
              ||| (y5 === q1 % q2 &&& (!!false === !!false) &&& (q1 === pair q3 q4) &&& _eqNatEqNat y3 q3 y4 q4) ) ) )
  and eqNatEqNat y6 y7 y8 y9 =
    fresh (q1 q2 q3 q4)
      ( y6 === s q1
      &&& (y7 === z ())
      &&& eqNat y8 y9
      ||| (y6 === z () &&& (y7 === s q2) &&& eqNat y8 y9)
      ||| (y6 === s q3 &&& (y7 === s q4) &&& eqNatEqNat q3 q4 y8 y9) )
  and eqNat y11 y12 =
    fresh (q1 q2 q3 q4)
      ( y11 === z ()
      &&& (y12 === z ())
      ||| (y11 === s q1 &&& (y12 === z ()))
      ||| (y11 === z () &&& (y12 === s q2))
      ||| (y11 === s q3 &&& (y12 === s q4) &&& eqNat q3 q4) )
  and _eqNatEqNat y14 y15 y16 y17 =
    fresh (q1 q2) (y14 === z () &&& (y15 === z ()) &&& _eqNat y16 y17 ||| (y14 === s q1 &&& (y15 === s q2) &&& _eqNatEqNat q1 q2 y16 y17))
  and _eqNat y18 y19 =
    fresh (q1 q2 q3 q4) (y18 === s q1 &&& (y19 === z ()) ||| (y18 === z () &&& (y19 === s q2)) ||| (y18 === s q3 &&& (y19 === s q4) &&& _eqNat q3 q4))
  in
  isPath x0 x1 x2
