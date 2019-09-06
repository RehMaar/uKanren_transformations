open OCanren
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

let topLevelMy x0 x1 x2 =
  let rec check_uni y0 y1 y2 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21)
      ( pair y1 y2 === pair y1 y2
      &&& (y1 === var_ (s q1))
      &&& (y2 === var_ q2)
      &&& (y0 === q3 % q4)
      &&& (s q1 === s q1)
      &&& (q3 % q4 === q5 % q6)
      &&& (q2 === s q7)
      &&& eq_nat (s q1) (s q7)
      &&& ( s q7 === s q7
          &&& ( pair y1 y2 === pair y1 y2
              &&& (y1 === var_ (s q1))
              &&& (y2 === var_ q2)
              &&& (y0 === q3 % q4)
              &&& (s q1 === s q1)
              &&& (q3 % q4 === q5 % q6)
              &&& (q2 === s q7)
              &&& get_term q7 q6 ) )
      ||| ( pair y1 y2 === pair y1 y2
          &&& (y1 === var_ (s q1))
          &&& (y2 === var_ q2)
          &&& (y0 === q3 % q4)
          &&& (s q1 === s q1)
          &&& (q3 % q4 === none () % q8)
          &&& (q2 === zero)
          &&& (s q1 === zero)
          ||| ( pair y1 y2 === pair y1 y2
              &&& (y1 === var_ (s q1))
              &&& (y2 === var_ q2)
              &&& (y0 === q3 % q4)
              &&& (s q1 === s q1)
              &&& (q3 % q4 === nil ())
              &&& eq_nat (s q1) q2 ) )
      &&& (q3 % q4 === q3 % q4 &&& (s q1 === s q1) &&& (y1 === var_ (s q1) &&& (y2 === var_ q2) &&& (y0 === q3 % q4) &&& get_term q1 q4))
      ||| ( y1 === var_ zero
          &&& (y2 === var_ zero)
          &&& (y0 === none () % q9)
          ||| ( y1
              === var_ (s q10)
              &&& (y2 === var_ (s q7))
              &&& (y0 === nil ())
              &&& eq_nat q10 q7
              &&& ( s q7 === s q7
                  &&& ( pair y1 y2 === pair y1 y2
                      &&& (y1 === var_ (s q10))
                      &&& (y2 === var_ (s q7))
                      &&& (y0 === nil ())
                      &&& (pair (s q10) (s q7) === pair (s q10) (s q7))
                      &&& (s q10 === s q10)
                      &&& (s q7 === s q7) ) )
              ||| (y1 === var_ zero &&& (y2 === var_ zero) &&& (y0 === nil ())) ) )
      ||| ( y1 === var_ q11
          &&& (y2 === var_ q2)
          &&& _get_term q11 y0 q3
          &&& ((y1 === var_ q11) &&& (y2 === var_ q2) &&& check_uni y0 q3 (var_ q2))
          ||| ( y1 === constr q12 q13
              &&& (y2 === var_ q14)
              &&& _get_term q14 y0 q9
              &&& (pair y1 y2 === pair y1 y2 &&& (y1 === constr q12 q13) &&& (y2 === var_ q14) &&& (some q9 === some q9) &&& check_uni y0 (constr q12 q13) q9)
              ||| ( y1 === var_ q15
                  &&& (y2 === constr q16 q17)
                  &&& _get_term q15 y0 q3
                  &&& ( pair y1 y2 === pair y1 y2
                      &&& (y1 === var_ q15)
                      &&& (y2 === constr q16 q17)
                      &&& (some q3 === some q3)
                      &&& check_uni y0 q3 (constr q16 q17) )
                  ||| (y1 === constr q18 q19 &&& (y2 === constr q20 q21) &&& eq_natForall2 q18 q20 y0 q19 q21) ) ) ) )
  and get_term y3 y4 = fresh (q1 q2 q3) (y4 === q1 % q2 &&& (y3 === s q3) &&& get_term q3 q2 ||| (y4 === none () % q2 &&& (y3 === zero) ||| (y4 === nil ())))
  and eq_nat y5 y6 = fresh (q1 q2) (y5 === s q1 &&& (y6 === s q2) &&& eq_nat q1 q2 ||| (y5 === zero &&& (y6 === zero)))
  and _get_term y7 y8 y9 = fresh (q1 q2 q3) (y8 === q1 % q2 &&& (y7 === s q3) &&& _get_term q3 q2 y9 ||| (y8 === some y9 % q2 &&& (y7 === zero)))
  and eq_natForall2 y10 y11 y12 y13 y14 =
    fresh (q1 q2) (y10 === s q1 &&& (y11 === s q2) &&& eq_natForall2 q1 q2 y12 y13 y14 ||| (y10 === zero &&& (y11 === zero) &&& forall2 y12 y13 y14))
  and forall2 y15 y16 y17 =
    fresh (q1 q2 q3 q4)
      ( y16 === q1 % q2
      &&& (y17 === q3 % q4)
      &&& forall2 y15 q2 q4
      &&& ( pair (constr zero y16) (constr zero y17)
          === pair (constr zero y16) (constr zero y17)
          &&& (constr zero y16 === constr zero y16)
          &&& (constr zero y17 === constr zero y17)
          &&& (!!true === !!true) &&& (!!true === !!true)
          &&& (pair zero zero === pair zero zero)
          &&& (zero === zero) &&& (zero === zero)
          &&& (pair y16 y17 === pair y16 y17)
          &&& (y16 === q1 % q2)
          &&& (y17 === q3 % q4)
          &&& (!!true === !!true) &&& (!!true === !!true) &&& check_uni y15 q1 q3 )
      ||| (y16 === nil () &&& (y17 === nil ())) )
  in
  check_uni x0 x1 x2
