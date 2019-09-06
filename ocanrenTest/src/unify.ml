open OCanren
open OCanren.Std
open Std

type 'a0 gnat = Z | S of 'a0

let rec fmap fa0 = function Z -> Z | S a0 -> S (fa0 a0)

module For_gnat = Fmap (struct
  let rec fmap fa0 = function Z -> Z | S a0 -> S (fa0 a0)

  type 'a0 t = 'a0 gnat
end)

let rec zero = inj (For_gnat.distrib Z)

and s x__0 = inj (For_gnat.distrib (S x__0))

type ('a1, 'a0) gterm = Var_ of 'a1 | Constr of 'a1 * 'a0

let rec fmap fa1 fa0 = function Var_ a1 -> Var_ (fa1 a1) | Constr (a1_0, a0_1) -> Constr (fa1 a1_0, fa0 a0_1)

module For_gterm = Fmap2 (struct
  let rec fmap fa1 fa0 = function Var_ a1 -> Var_ (fa1 a1) | Constr (a1_0, a0_1) -> Constr (fa1 a1_0, fa0 a0_1)

  type ('a1, 'a0) t = ('a1, 'a0) gterm
end)

let rec var_ x__0 = inj (For_gterm.distrib (Var_ x__0))

and constr x__0 x__1 = inj (For_gterm.distrib (Constr (x__0, x__1)))

let topLevel x0 x1 x2 =
  let rec check_uni y0 y1 y2 =
    fresh (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12)
      ( y1 === constr q1 q2
      &&& (y2 === constr q3 q4)
      &&& (eq_nat q1 q3 &&& forall2 y0 q2 q4)
      ||| (y1 === var_ q5 &&& (y2 === constr q6 q7) &&& get_termCheck_uni y0 q5 q6 q7)
      ||| (y1 === constr q8 q9 &&& (y2 === var_ q10) &&& _get_termCheck_uni y0 q8 q9 q10)
      ||| (y1 === var_ q11 &&& (y2 === var_ q12) &&& __get_termCheck_uni y0 q11 q12)
      ||| (y1 === var_ q11 &&& (y2 === var_ q12) &&& get_termGet_termEq_nat y0 q11 q12) )
  and eq_nat y3 y4 = fresh (q1 q2) (y3 === zero &&& (y4 === zero) ||| (y3 === s q1 &&& (y4 === s q2) &&& eq_nat q1 q2))
  and forall2 y5 y6 y7 =
    fresh (q1 q2 q3 q4) (y6 === nil () &&& (y7 === nil ()) ||| (y6 === q1 % q2 &&& (y7 === q3 % q4) &&& (check_uni y5 q1 q3 &&& forall2 y5 q2 q4)))
  and get_termCheck_uni y8 y9 y10 y11 =
    fresh (q1 q2 q3 q4)
      ( y8
      === some q1 % q2
      &&& (y9 === zero)
      &&& check_uni (some q1 % q2) q1 (constr y10 y11)
      ||| (y8 === q3 % q2 &&& (y9 === s q4) &&& (__get_term q1 q2 q4 &&& check_uni (q3 % q2) q1 (constr y10 y11))) )
  and _get_termCheck_uni y16 y17 y18 y19 =
    fresh (q1 q2 q3 q4)
      ( y16
      === some q1 % q2
      &&& (y19 === zero)
      &&& check_uni (some q1 % q2) (constr y17 y18) q1
      ||| (y16 === q3 % q2 &&& (y19 === s q4) &&& (__get_term q1 q2 q4 &&& check_uni (q3 % q2) (constr y17 y18) q1)) )
  and __get_termCheck_uni y24 y25 y26 =
    fresh (q1 q2 q3 q4)
      ( y24
      === some q1 % q2
      &&& (y25 === zero)
      &&& check_uni (some q1 % q2) q1 (var_ y26)
      ||| (y24 === q3 % q2 &&& (y25 === s q4) &&& (__get_term q1 q2 q4 &&& check_uni (q3 % q2) q1 (var_ y26))) )
  and __get_term y28 y29 y30 = fresh (q1 q2 q3) (y29 === some y28 % q1 &&& (y30 === zero) ||| (y29 === q2 % q1 &&& (y30 === s q3) &&& __get_term y28 q1 q3))
  and get_termGet_termEq_nat y31 y32 y33 =
    fresh (q1 q2 q3 q4)
      ( y31 === nil () &&& eq_nat y32 y33
      ||| (y31 === none () % q1 &&& (y32 === zero) &&& (y33 === zero))
      ||| (y31 === q2 % q1 &&& (y32 === s q3) &&& (y33 === s q4) &&& get_termGet_termEq_nat q1 q3 q4) )
  in
  check_uni x0 x1 x2

let topLevelSU x0 x1 x2 =
  let rec check_uni y0 y1 y2 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25)
      ( y1 === constr q1 q2
      &&& (y2 === constr q3 q4)
      &&& eq_natForall2 q1 q3 y0 q2 q4
      ||| ( y1 === var_ q5
          &&& (y2 === constr q6 q7)
          &&& (check_uni y0 q8 (constr q6 q7) &&& get_term q5 y0 q8)
          ||| ( y1 === constr q9 q10
              &&& (y2 === var_ q11)
              &&& (check_uni y0 (constr q9 q10) q12 &&& get_term q11 y0 q12)
              ||| ( y1 === var_ q13
                  &&& (y2 === var_ q14)
                  &&& (check_uni y0 q15 (var_ q14) &&& get_term q13 y0 q15)
                  ||| ( y1 === var_ q13
                      &&& (y2 === var_ q14)
                      &&& ( y0 === nil ()
                          &&& (q13 === zero &&& (q14 === zero) ||| (q13 === s q16 &&& (q14 === s q17) &&& eq_nat q16 q17))
                          ||| ( y0
                              === none () % q18
                              &&& (q13 === zero) &&& (q14 === zero)
                              ||| ( y0 === q19 % q20
                                  &&& (q13 === s q21)
                                  &&& ( _get_term q21 q20
                                      &&& ( q19 % q20 === nil ()
                                          &&& eq_nat (s q21) q14
                                          ||| ( q19 % q20
                                              === none () % q22
                                              &&& (q14 === zero)
                                              &&& (s q21 === zero)
                                              ||| (q19 % q20 === q23 % q24 &&& (q14 === s q25) &&& (_get_term q25 q24 &&& eq_nat (s q21) (s q25))) ) ) ) ) ) )
                      ) ) ) ) )
  and eq_natForall2 y3 y4 y5 y6 y7 =
    fresh (q1 q2) (y3 === zero &&& (y4 === zero) &&& forall2 y5 y6 y7 ||| (y3 === s q1 &&& (y4 === s q2) &&& eq_natForall2 q1 q2 y5 y6 y7))
  and forall2 y8 y9 y10 =
    fresh (q1 q2 q3 q4) (y9 === nil () &&& (y10 === nil ()) ||| (y9 === q1 % q2 &&& (y10 === q3 % q4) &&& (check_uni y8 q1 q3 &&& forall2 y8 q2 q4)))
  and get_term y11 y12 y13 = fresh (q1 q2 q3) (y12 === some y13 % q1 &&& (y11 === zero) ||| (y12 === q2 % q1 &&& (y11 === s q3) &&& get_term q3 q1 y13))
  and eq_nat y14 y15 = fresh (q1 q2) (y14 === zero &&& (y15 === zero) ||| (y14 === s q1 &&& (y15 === s q2) &&& eq_nat q1 q2))
  and _get_term y16 y17 =
    fresh (q1 q2 q3) (y17 === nil () ||| (y17 === none () % q1 &&& (y16 === zero) ||| (y17 === q2 % q1 &&& (y16 === s q3) &&& _get_term q3 q1)))
  in
  check_uni x0 x1 x2

let topLevelRU x0 x1 x2 =
  let rec check_uni y0 y1 y2 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22)
      ( y1 === constr q1 q2
      &&& (y2 === constr q3 q4)
      &&& eq_natForall2 q1 q3 y0 q2 q4
      ||| ( y1 === var_ q5
          &&& (y2 === constr q6 q7)
          &&& (check_uni y0 q8 (constr q6 q7) &&& get_term q5 y0 q8)
          ||| ( y1 === constr q9 q10
              &&& (y2 === var_ q11)
              &&& (check_uni y0 (constr q9 q10) q12 &&& get_term q11 y0 q12)
              ||| ( y1 === var_ q13
                  &&& (y2 === var_ q14)
                  &&& (check_uni y0 q15 (var_ q14) &&& get_term q13 y0 q15)
                  ||| ( y1 === var_ q13
                      &&& (y2 === var_ q14)
                      &&& ( y0 === nil () &&& eq_nat q13 q14
                          ||| ( y0
                              === none () % q16
                              &&& (q14 === zero) &&& (q13 === zero)
                              ||| ( y0 === q17 % q18
                                  &&& (q14 === s q19)
                                  &&& ( q13 === zero
                                      &&& (s q19 === zero)
                                      &&& (q17 % q18 === nil () ||| (q17 % q18 === none () % q20))
                                      ||| (q13 === s q21 &&& (s q19 === s q22) &&& (_get_term (s q21) (q17 % q18) &&& eq_nat q21 q22))
                                      &&& _get_term q19 q18 ) ) ) ) ) ) ) ) )
  and eq_natForall2 y3 y4 y5 y6 y7 =
    fresh (q1 q2) (y3 === zero &&& (y4 === zero) &&& forall2 y5 y6 y7 ||| (y3 === s q1 &&& (y4 === s q2) &&& eq_natForall2 q1 q2 y5 y6 y7))
  and forall2 y8 y9 y10 =
    fresh (q1 q2 q3 q4) (y9 === nil () &&& (y10 === nil ()) ||| (y9 === q1 % q2 &&& (y10 === q3 % q4) &&& (check_uni y8 q1 q3 &&& forall2 y8 q2 q4)))
  and get_term y11 y12 y13 = fresh (q1 q2 q3) (y12 === some y13 % q1 &&& (y11 === zero) ||| (y12 === q2 % q1 &&& (y11 === s q3) &&& get_term q3 q1 y13))
  and eq_nat y14 y15 = fresh (q1 q2) (y14 === zero &&& (y15 === zero) ||| (y14 === s q1 &&& (y15 === s q2) &&& eq_nat q1 q2))
  and _get_term y16 y17 =
    fresh (q1 q2 q3) (y17 === nil () ||| (y17 === none () % q1 &&& (y16 === zero) ||| (y17 === q2 % q1 &&& (y16 === s q3) &&& _get_term q3 q1)))
  in
  check_uni x0 x1 x2
