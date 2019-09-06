module L = List

open GT
open OCanren
open OCanren.Std
open Std
open Nat

type bottle =
  | Fst 
  | Snd 

let fst  = !! Fst
let snd  = !! Snd

type stepType =
  | Fill 
  | Empty 
  | Pour 

let fill = !! Fill
let empty = !! Empty
let pour = !! Pour

type 'a0 gnat =
  | O 
  | S of 'a0 


let topLevelRU x0 x1 x2 =
  let rec checkAnswer y0 y1 y2 = checkAnswer' y0 y1 y2
  and checkAnswer' y3 y4 y5 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23)
      ( y3 === nil ()
      &&& (y5 === o)
      ||| ( y3 === q1 % q2
          &&& ( q1 === pair fill fst
              &&& ( q2 === nil ()
                  &&& ( y4 === pair q3 q4
                      &&& (q3 === o &&& (y5 === o) ||| (q3 === s q5 &&& (y5 === s q6) &&& (_a12461124 q5 q6 &&& (s q6 === o ||| (s q6 === s q7)))))
                      ||| ( y4 === pair q3 q8
                          &&& (q3 === s q9 &&& (y5 === o) &&& a12461124 ||| (q3 === s q10 &&& (y5 === s q11) &&& (__a12461124 q10 q11 &&& (s q11 === o))))
                          ) )
                  ||| (q2 === q12 % q13 &&& checkStepDoStep q12 y4) )
              ||| ( q1 === pair fill snd
                  &&& ( q2 === nil ()
                      &&& ( y4 === pair q14 q15
                          &&& (y5 === o &&& (q15 === o ||| (q15 === s q16)))
                          ||| (y4 === pair q17 (s q18) &&& (y5 === s q19 &&& _a12461124 q18 q19)) )
                      ||| (q2 === q20 % q21 &&& checkStepDoStep q20 y4) )
                  ||| ( q1 === pair empty fst
                      &&& (checkAnswer' q2 y4 y5 &&& (y4 === pair (o) q22))
                      ||| (q1 === pair empty snd &&& (checkAnswer' q2 y4 y5 &&& (y4 === pair q23 (o)))) ) ) ) ) )
  and a12461124 = success
  and _a12461124 y6 y7 = fresh (q1 q2) (y6 === o &&& (y7 === o) ||| (y6 === s q1 &&& (y7 === s q2) &&& _a12461124 q1 q2))
  and __a12461124 y8 y9 =
    fresh (q1 q2 q3) (y8 === o &&& (y9 === s q1) ||| (y8 === s q2 &&& (y9 === o) ||| (y8 === s q2 &&& (y9 === s q3) &&& __a12461124 q2 q3)))
  and checkStepDoStep y11 y12 =
    fresh
      (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 q32 q33 q34 q35 q36 q37 q38 q39 q40
         q41 q42 q43 q44 q45 q46 q47 q48 q49 q50 q51 q52 q53 q54 q55 q56 q57 q58 q59 q60 q61 q62 q63 q64 q65 q66 q67 q68 q69 q70 q71 q72 q73 q74 q75 q76 q77
         q78 q79 q80 q81 q82 q83 q84 q85 q86 q87 q88 q89 q90 q91 q92 q93 q94 q95 q96 q97 q98 q99 q100 q101 q102 q103 q104 q105 q106 q107 q108 q109 q110 q111
         q112 q113 q114 q115 q116 q117 q118 q119 q120 q121 q122 q123 q124 q125 q126 q127 q128 q129 q130 q131 q132 q133 q134 q135 q136 q137 q138 q139 q140 q141
         q142 q143 q144 q145 q146 q147 q148 q149 q150 q151 q152 q153 q154 q155 q156 q157 q158 q159 q160 q161 q162 q163 q164 q165 q166 q167 q168 q169 q170 q171
         q172 q173 q174 q175 q176 q177 q178 q179 q180 q181 q182 q183 q184)
      ( y11 === pair fill fst
      &&& (y12 === pair q1 q2)
      ||| ( y11 === pair fill snd
          &&& (y12 === pair q3 q4)
          ||| ( y11 === pair empty fst
              &&& (y12 === pair q5 q6 &&& a12461124CreateState q5)
              ||| ( y11 === pair empty snd
                  &&& (y12 === pair q7 q8 &&& _a12461124CreateState q8)
                  ||| ( y11 === pair pour fst
                      &&& ( y12
                          === pair (o) q9
                          &&& ( a12461124AddGreaterAddCreateState q10 q11 q9
                              &&& ( q10 === o
                                  &&& (q9 === s q12)
                                  &&& fst' q12 q11
                                  ||| ( q10 === s q13
                                      &&& (q9 === o)
                                      &&& (q11 === o)
                                      ||| (q10 === s q14 &&& (q9 === s q15) &&& (__a12461124 q14 q15 &&& _fst' (s q15) q11)) ) ) )
                          ||| ( y12
                              === pair (o) q16
                              &&& ( a12461124AddGreaterAddCreateState q10 q11 q16
                                  &&& ( q10 === o
                                      &&& (q16 === s q17)
                                      &&& snd' q17 q11
                                      ||| ( q10 === s q18
                                          &&& (q16 === o)
                                          &&& (q11 === o)
                                          ||| (q10 === s q19 &&& (q16 === s q20) &&& (__a12461124 q19 q20 &&& (s q20 === q11))) )
                                      &&& anotherBottle ) ) )
                          ||| ( y12
                              === pair q21 (o)
                              &&& ( a12461124AddGreaterAddCreateState q10 q21 (o)
                                  &&& (q10 === s q22 &&& _snd' q21 ||| (q10 === s q23 &&& (__snd' q21 (s q24) &&& __a12461124 q23 q24)) &&& anotherBottle) )
                              ||| ( y12
                                  === pair q25 (o)
                                  &&& ( a12461124AddGreaterAddCreateState q10 q11 q26
                                      &&& ( q10 === s q27
                                          &&& (q26 === o &&& (q11 === o &&& _snd' q25))
                                          ||| (q10 === s q28 &&& (q26 === o &&& (s q29 === o &&& __snd' q25 q11) &&& __a12461124 q28 q29))
                                          &&& (anotherBottle &&& anotherBottle) ) ) ) )
                          ||| ( y12
                              === pair (s q30) q31
                              &&& ( a12461124AddGreaterAdd q10 (s q30)
                                  &&& ( q10 === o &&& ___snd' q30 q31
                                      ||| (q10 === s q32 &&& ____snd' q30 q31 ||| (q10 === s q33 &&& (_____snd' q30 q31 (s q34) &&& __a12461124 q33 q34))) ) )
                              ||| ( y12
                                  === pair (s q30) q35
                                  &&& ( a12461124AddGreaterAdd q10 q35
                                      &&& ( q10 === o &&& ___snd' q30 q35
                                          ||| (q10 === s q36 &&& ____snd' q30 q35 ||| (q10 === s q37 &&& (_____snd' q30 q35 (s q38) &&& __a12461124 q37 q38)))
                                          &&& anotherBottle ) ) )
                              ||| ( y12
                                  === pair q39 (s q30)
                                  &&& ( a12461124AddGreaterAdd q10 q11
                                      &&& ( q10 === o &&& fst'Snd' q39 q30 q11 q26
                                          ||| ( q10 === s q40
                                              &&& ( q40 === o
                                                  &&& (q30 === s q41)
                                                  &&& (q39 === q11)
                                                  ||| ( q40 === s q42
                                                      &&& (q30 === o)
                                                      &&& (q39 === q11)
                                                      ||| ( q40 === s q43
                                                          &&& (q30 === s q44)
                                                          &&& (__a12461124 q43 q44 &&& (q39 === q11 &&& ______snd' q11 (s q44) q26)) ) ) ) )
                                          &&& anotherBottle ) )
                                  ||| ( y12
                                      === pair q45 (s q30)
                                      &&& ( a12461124AddGreaterAdd q10 q11
                                          &&& ( q10 === o
                                              &&& (q11 === s q30 &&& get_capacity q45 q30)
                                              ||| (q10 === s q46 &&& (snd'Snd' q45 q30 (s q47) q11 &&& __a12461124 q46 q47))
                                              &&& (anotherBottle &&& anotherBottle) ) ) ) )
                              ||| ( q11 === o
                                  &&& ( q30 === o
                                      &&& (_______add q48 ||| (_add q49 (s q10) q50 &&& ________add (s q49) q10 q48))
                                      ||| ( q30 === s q51
                                          &&& (q10 === o ||| (__add q52 (s q10) q50 &&& (s q52 === q53 &&& _________add q53 q10) &&& createState q26))
                                          ||| ( q30 === s q54
                                              &&& (_______add (s q55) ||| (_add q56 (s q10) q50 &&& ________add (s q56) q10 (s q55)) &&& sub q55 q54) ) ) )
                                  ||| ( q11 === s q57
                                      &&& ( q10 === s q58
                                          &&& (q30 === s q59 &&& (s q58 === s (s q60) &&& sub q60 q59))
                                          ||| (_____a12461124 (s q61) &&& (__________add q61 (s q10) (s q58) &&& addSub (s q61) q10 q30))
                                          &&& greater q58 q57 ) )
                                  &&& ( q10 === o
                                      &&& ( y12
                                          === pair q62 (s q63)
                                          &&& ( q64 === fst
                                              &&& ( q65 === fst
                                                  &&& (q62 === q11 &&& get_capacityFst' q11 q63 q66 q30 q26)
                                                  ||| (q65 === snd &&& (q62 === q11 &&& get_capacitySnd' q11 q63 q66 q30 q26)) )
                                              ||| ( q64 === snd
                                                  &&& ( q65 === fst
                                                      &&& (q11 === s q63 &&& get_capacityFst' q62 q63 q66 q30 q26)
                                                      ||| (q65 === snd &&& (q11 === s q63 &&& get_capacitySnd' q62 q63 q66 q30 q26)) ) ) ) )
                                      ||| ( q10 === s q67
                                          &&& ( y12
                                              === pair q68 (o)
                                              &&& ( q64 === fst
                                                  &&& ( q65 === fst
                                                      &&& (q68 === q11 &&& _get_capacityFst' q11 q66 q30 q26)
                                                      ||| (q65 === snd &&& (q68 === q11 &&& _get_capacitySnd' q11 q66 q30 q26)) )
                                                  ||| ( q64 === snd
                                                      &&& ( q65 === fst
                                                          &&& (q11 === o &&& _get_capacityFst' q68 q66 q30 q26)
                                                          ||| (q65 === snd &&& (q11 === o &&& _get_capacitySnd' q68 q66 q30 q26)) ) ) ) )
                                          ||| ( q10 === s q69
                                              &&& ( q66 === fst
                                                  &&& ( y12
                                                      === pair (s q30) (s q70)
                                                      &&& ( q65 === fst
                                                          &&& ( q64 === fst
                                                              &&& (s q70 === q71 &&& (q11 === s q30) &&& _____fst' q30 q71 q26)
                                                              ||| (q64 === snd &&& (s q70 === q11 &&& _____fst' q30 q11 q26)) )
                                                          ||| ( q65 === snd
                                                              &&& ( q64 === fst
                                                                  &&& (s q70 === q72 &&& (q11 === s q30) &&& _____snd' q30 q72 q26)
                                                                  ||| (q64 === snd &&& (s q70 === q11 &&& _____snd' q30 q11 q26)) ) ) ) )
                                                  ||| ( q66 === snd
                                                      &&& ( y12
                                                          === pair q73 (s q30)
                                                          &&& ( s q70 === s q30
                                                              &&& ( q65 === fst
                                                                  &&& ( q64 === fst
                                                                      &&& (q73 === q11 &&& __fst' q11 q30 q26)
                                                                      ||| (q64 === snd &&& (q11 === s q30 &&& __fst' q73 q30 q26)) )
                                                                  ||| ( q65 === snd
                                                                      &&& ( q64 === fst &&& fst'Snd' q73 q30 q11 q26
                                                                          ||| (q64 === snd &&& snd'Snd' q73 q30 q11 q26) ) ) ) ) ) )
                                                  &&& __a12461124 q69 q70 ) ) )
                                      &&& (_anotherBottle q64 &&& (_anotherBottle q66 &&& _anotherBottle q65)) ) ) )
                          ||| ( y12 === pair q74 q75
                              &&& ( _____add q76 (s q10)
                                  &&& (s q76 === q77 &&& addCreateState q10)
                                  &&& ( q10 === o
                                      &&& (q75 === s q78)
                                      ||| (q10 === s q79 &&& (q75 === o) ||| (q10 === s q80 &&& (q75 === s q81 &&& __a12461124 q80 q81))) ) )
                              ||| ( q10 === o
                                  ||| (___________add q82 (s q10) &&& (s q82 === q83 &&& ___add q83 q10 q84))
                                  ||| ( q85 === s q86
                                      &&& ( _____a12461124 (s q87)
                                          &&& (____________add (s q87) q10 (s q88) &&& __________add q87 (s q10) q84)
                                          &&& _greater q88 q86 ) )
                                  &&& ( q10 === o
                                      &&& (y12 === pair q89 (s q85) &&& get_capacity q89 q85)
                                      ||| (q10 === s q90 &&& (y12 === pair q91 (s q85) &&& ______snd' q91 q85 (s q92) &&& __a12461124 q90 q92)) ) ) ) )
                      ||| ( y11 === pair pour snd
                          &&& ( y12
                              === pair (o) q93
                              &&& ( __anotherBottle
                                  ||| ( _a12461124AddGreaterAddCreateState q94 q95 q96
                                      &&& (q96 === o &&& _fst' q93 q95 ||| (q94 === s q97 &&& __a12461124 q97 q98) &&& (__anotherBottle &&& __anotherBottle))
                                      ) )
                              ||| ( y12
                                  === pair (o) q99
                                  &&& ( _a12461124AddGreaterAddCreateState q100 q95 q96
                                      &&& (q96 === o &&& (q99 === q95) ||| (q100 === s q101 &&& __a12461124 q101 q102) &&& __anotherBottle) ) )
                              ||| ( y12
                                  === pair q103 (o)
                                  &&& ( q103
                                      === s (s q104)
                                      &&& greater q105 q104
                                      ||| (_a12461124AddGreaterAddCreateState q106 q103 q103 &&& (______a12461124 q106 q103 &&& __anotherBottle)) )
                                  ||| ( y12
                                      === pair q107 (o)
                                      &&& ( _a12461124AddGreaterAddCreateState q108 (o) q107
                                          &&& ( q107 === o
                                              ||| ( q108 === o &&& ______fst' q107 q109
                                                  ||| ( q108 === s q110
                                                      &&& (q107 === s (o))
                                                      ||| ( q108 === s q110
                                                          &&& ( __anotherBottle
                                                              &&& ( q110 === o
                                                                  &&& (q107 === s (s (s q111)))
                                                                  ||| ( q110 === s q112
                                                                      &&& (q107 === s (s (o)))
                                                                      ||| (q110 === s q113 &&& (______fst' q107 (s q114) &&& __a12461124 q113 q114)) ) ) ) ) )
                                                  ) ) ) ) )
                              ||| ( y12
                                  === pair (s q115) q116
                                  &&& (_a12461124AddGreaterAdd q117 (s q115) &&& (__a12461124 q117 q115 &&& (__anotherBottle &&& __anotherBottle)))
                                  ||| ( y12
                                      === pair (s q115) q118
                                      &&& ( _a12461124AddGreaterAdd q119 q118
                                          &&& ( q119 === o
                                              &&& (q115 === s q120)
                                              &&& _______fst' q120 q118
                                              ||| ( q119 === s q121
                                                  &&& (q115 === o)
                                                  &&& ________fst' q118
                                                  ||| (q119 === s q122 &&& (q115 === s q123) &&& (__a12461124 q122 q123 &&& _____fst' (s q123) q118 q96)) )
                                              &&& __anotherBottle ) ) )
                                  ||| ( y12
                                      === pair q124 (s q115)
                                      &&& (_a12461124AddGreaterAdd q125 q124 &&& (______a12461124 q125 q124 &&& __anotherBottle))
                                      ||| ( y12
                                          === pair q126 (s q115)
                                          &&& ( _a12461124AddGreaterAdd q127 q95
                                              &&& ( q95 === s q115
                                                  &&& (q126 === o)
                                                  ||| ( q126 === s q128
                                                      &&& ( q127 === o
                                                          &&& (q128 === s q129)
                                                          &&& (q95 === s q115)
                                                          ||| ( q127 === s q130
                                                              &&& (q128 === o)
                                                              &&& (q95 === s q115)
                                                              ||| ( q127 === s q131
                                                                  &&& (q128 === s q132)
                                                                  &&& (__a12461124 q131 q132 &&& ________snd' (s q132) q115 q95) ) ) ) ) ) ) ) )
                                  ||| ( q133 === o
                                      &&& ( q95 === o
                                          &&& ( q115 === o &&& add q134 q135
                                              ||| (q115 === s q136 ||| (q115 === s q137 &&& (add (s q138) q135 &&& sub q138 q137))) )
                                          ||| (q95 === s q139 &&& (s q140 === s q134 &&& sub q134 q115 &&& greater q140 q139)) )
                                      ||| (q133 === s q141 &&& (addGreater (s q141) q142 q95 &&& addSub q141 (s (s q142)) q115))
                                      &&& ( q143 === fst
                                          &&& ( q144 === fst
                                              &&& ( y12
                                                  === pair (s q115) q145
                                                  &&& ( q133 === o
                                                      &&& (q95 === s q115 &&& _get_capacity q115 q145 q146)
                                                      ||| ( q133 === s q147
                                                          &&& ( q147 === o
                                                              &&& (q115 === s q148)
                                                              &&& ( q146 === fst
                                                                  &&& (q95 === s (s q148) &&& _______fst' q148 q145)
                                                                  ||| (q146 === snd &&& (q95 === s (s q148) &&& _________snd' q148 q145)) )
                                                              ||| ( q147 === s q149
                                                                  &&& (q115 === o)
                                                                  &&& ( q146 === fst
                                                                      &&& (q95 === s (o) &&& ________fst' q145)
                                                                      ||| (q146 === snd &&& (q95 === s (o) &&& __________snd' q145)) )
                                                                  ||| ( q147 === s q150
                                                                      &&& (q115 === s q151)
                                                                      &&& (__a12461124 q150 q151 &&& (q95 === s (s q151) &&& _get_capacity (s q151) q145 q146))
                                                                      ) ) ) ) ) )
                                              ||| ( q144 === snd
                                                  &&& ( y12
                                                      === pair q152 (s q115)
                                                      &&& ( q133 === o
                                                          &&& (q152 === s q153)
                                                          &&& (q95 === s q153 &&& __get_capacity q153 q115 q146)
                                                          ||| ( q133 === s q154
                                                              &&& (q152 === o)
                                                              &&& (q95 === o &&& ___get_capacity q115 q146)
                                                              ||| ( q133 === s q155
                                                                  &&& (q152 === s q156)
                                                                  &&& ( __a12461124 q155 q156
                                                                      &&& ( s q156 === q95
                                                                          &&& ( q146 === fst
                                                                              &&& __fst' (s q156) q115 q96
                                                                              ||| (q146 === snd &&& ______snd' (s q156) q115 q96) ) ) ) ) ) ) ) ) )
                                          ||| ( q143 === snd
                                              &&& ( q144 === fst
                                                  &&& ( y12
                                                      === pair (s q115) q157
                                                      &&& ( q133 === o
                                                          &&& (q157 === q95 &&& _get_capacity q115 q95 q146)
                                                          ||| ( q133 === s q158
                                                              &&& ( q158 === o
                                                                  &&& (q115 === s q159)
                                                                  &&& ( q146 === fst
                                                                      &&& (q157 === q95 &&& _______fst' q159 q95)
                                                                      ||| (q146 === snd &&& (q157 === q95 &&& _________snd' q159 q95)) )
                                                                  ||| ( q158 === s q160
                                                                      &&& (q115 === o)
                                                                      &&& ( q146 === fst
                                                                          &&& (q157 === q95 &&& ________fst' q95)
                                                                          ||| (q146 === snd &&& (q157 === q95 &&& __________snd' q95)) )
                                                                      ||| ( q158 === s q161
                                                                          &&& (q115 === s q162)
                                                                          &&& ( __a12461124 q161 q162
                                                                              &&& ( q146 === fst
                                                                                  &&& (q157 === q95 &&& _____fst' (s q162) q95 q96)
                                                                                  ||| (q146 === snd &&& (q157 === q95 &&& _____snd' (s q162) q95 q96)) ) ) ) )
                                                                  ) ) ) )
                                                  ||| ( q144 === snd
                                                      &&& ( y12
                                                          === pair q163 (s q115)
                                                          &&& ( q133 === o
                                                              &&& (q163 === s q164)
                                                              &&& (q95 === s q115 &&& __get_capacity q164 q115 q146)
                                                              ||| ( q133 === s q165
                                                                  &&& (q163 === o)
                                                                  &&& (q95 === s q115 &&& ___get_capacity q115 q146)
                                                                  ||| ( q133 === s q166
                                                                      &&& (q163 === s q167)
                                                                      &&& ( __a12461124 q166 q167
                                                                          &&& ( q146 === fst
                                                                              &&& (s q167 === q168 &&& (q95 === s q115) &&& __fst' (s q167) q115 q96)
                                                                              ||| ( q146 === snd
                                                                                  &&& (s q167 === q169 &&& (q95 === s q115) &&& ______snd' (s q167) q115 q96)
                                                                                  ) ) ) ) ) ) ) ) ) )
                                          &&& (___anotherBottle q143 &&& (___anotherBottle q144 &&& ___anotherBottle q146)) ) ) )
                              ||| ( y12 === pair q170 q171
                                  &&& (______add q172 (s q173) &&& ____add (s q172) q173 q174 &&& ______a12461124 (s q172) q170)
                                  ||| ( q133 === o &&& ___a12461124
                                      ||| (q133 === s q175 &&& (___________add (s q175) q176 &&& __addCreateState q175 (s (s q176))))
                                      ||| ( q177 === s q178
                                          &&& ( q133 === o
                                              &&& (s q179 === q180)
                                              ||| ( q133 === s q181
                                                  &&& ( s q181 === o &&& _____a12461124 q10
                                                      ||| (s q181 === s q182 &&& (_____a12461124 q10 &&& __________add q182 (s q10) q174))
                                                      &&& ____________add q181 (s q10) (s q179) ) )
                                              &&& _greater q179 q178 ) )
                                      &&& (y12 === pair (s q177) q183 &&& (q133 === o ||| (q133 === s q184 &&& __a12461124 q184 q177))) ) ) ) ) ) ) ) ) )
  and a12461124CreateState y15 = fresh (q1 q2) (y15 === o &&& createState q1 ||| (y15 === s q2 &&& a12461124CreateState q2))
  and createState y18 = success
  and _a12461124CreateState y21 = fresh (q1 q2) (y21 === o &&& _createState q1 ||| (y21 === s q2 &&& _a12461124CreateState q2))
  and _createState y24 = success
  and a12461124AddGreaterAddCreateState y27 y29 y31 =
    fresh (q1 q2 q3 q4 q5 q6 q7)
      ( y29 === o
      &&& (add y27 q1 ||| (_add (s q2) y27 q1 &&& ___add q2 (s y27) q3))
      ||| ( y29 === s q4
          &&& ( s q5 === s y27 &&& ___a12461124
              ||| ( ____a12461124 (s q6)
                  &&& ( q6 === o
                      &&& (s q5 === s (s y27))
                      &&& ___add q6 (s y27) q3
                      ||| (q6 === s q7 &&& (___add q7 (s (s y27)) (s q5) &&& ___add q6 (s y27) q3)) ) )
              &&& greater q5 q4 ) ) )
  and add y33 y34 = y33 === y34
  and _add y35 y36 y37 = fresh (q1) (y35 === o &&& (y36 === y37) ||| __add q1 y36 y37)
  and __add y38 y39 y40 = _add y38 (s y39) y40
  and ___add y41 y42 y43 = fresh (q1) (y41 === o &&& (y43 === s y42) ||| ____add q1 y42 y43)
  and ____add y44 y45 y46 = ___add y44 (s y45) y46
  and ____a12461124 y47 = success
  and greater y48 y49 = fresh (q1 q2) (y48 === s q1 &&& (y49 === o) ||| (y48 === s q1 &&& (y49 === s q2) &&& greater q1 q2))
  and fst' y50 y51 = y51 === o
  and _fst' y52 y53 = y53 === o
  and snd' y54 y55 = y55 === s y54
  and _snd' y56 = success
  and __snd' y57 y58 = y58 === o
  and a12461124AddGreaterAdd y60 y62 = fresh (q1 q2) (____a12461124 (s q1) &&& (s q1 === q2 &&& addGreater q2 y60 y62 &&& _____add q1 (s y60)))
  and addGreater y63 y64 y66 =
    fresh (q1 q2) (y63 === o &&& (y66 === o ||| (y66 === s q1 &&& greater y64 q1)) ||| (y63 === s q2 &&& addGreater q2 (s y64) y66))
  and _____add y67 y68 = fresh (q1) (______add q1 y68)
  and ______add y69 y70 = _____add y69 (s y70)
  and ___snd' y71 y72 = fresh (q1) (y72 === s q1)
  and ____snd' y74 y75 = y75 === o
  and _____snd' y76 y77 y78 = y77 === y78
  and fst'Snd' y79 y80 y81 y82 = y82 === s y80 &&& __fst' y79 y80 y81
  and __fst' y83 y84 y85 = y83 === y85
  and ______snd' y86 y87 y88 = y88 === s y87
  and get_capacity y89 y90 = fresh (q1) (_______snd' y89 y90 q1)
  and _______snd' y92 y93 y94 = y93 === y94
  and snd'Snd' y95 y96 y97 y98 = y97 === s y96 &&& ______snd' y95 y96 y98
  and _______add y100 = fresh (q1) (add q1 y100)
  and ________add y101 y102 y103 = _add y101 y102 y103
  and _________add y104 y105 = fresh (q1) (y104 === s q1 &&& _________add q1 (s y105))
  and sub y106 y107 = fresh (q1 q2) (y107 === o ||| (y107 === s q1 &&& (y106 === o) ||| (y107 === s q1 &&& (y106 === s q2) &&& sub q2 q1)))
  and _____a12461124 y109 = fresh (q1) (y109 === s q1)
  and __________add y110 y111 y112 = fresh (q1) (y110 === o &&& (y111 === y112) ||| (y110 === s q1 &&& ___add q1 y111 y112))
  and addSub y113 y114 y116 = fresh (q1 q2) (y113 === o &&& (y114 === s q1) &&& sub q1 y116 ||| (y113 === s q2 &&& addSub q2 (s y114) y116))
  and get_capacityFst' y118 y119 y120 y121 y122 =
    y120 === fst &&& (y118 === y122 &&& ___fst' y122 y119 y121) ||| (y120 === snd &&& (y118 === y122 &&& _______snd' y122 y119 y121))
  and ___fst' y123 y124 y125 = y123 === s y125
  and get_capacitySnd' y126 y127 y128 y129 y130 =
    y128 === fst &&& (y130 === s y127 &&& ___fst' y126 y127 y129) ||| (y128 === snd &&& (y130 === s y127 &&& _______snd' y126 y127 y129))
  and _get_capacityFst' y131 y132 y133 y134 = y132 === fst &&& (y131 === y134 &&& ____fst' y134 y133)
  and ____fst' y135 y136 = y135 === s y136
  and _get_capacitySnd' y137 y138 y139 y140 = y138 === fst &&& (y140 === o &&& ____fst' y137 y139)
  and _____fst' y141 y142 y143 = y143 === s y141
  and _anotherBottle y144 = y144 === snd
  and addCreateState y146 = addCreateState (s y146)
  and ___________add y149 y150 = fresh (q1) (y149 === o &&& (y150 === o) ||| (y149 === s q1 &&& _________add q1 y150))
  and ____________add y151 y152 y153 = fresh (q1) (y151 === o &&& (y152 === s y153) ||| (y151 === s q1 &&& _add q1 y152 y153))
  and _greater y154 y155 = fresh (q1 q2) (y154 === o ||| (y154 === s q1 &&& (y155 === s q2) &&& _greater q1 q2))
  and _a12461124AddGreaterAddCreateState y157 y159 y161 =
    fresh (q1 q2 q3 q4 q5 q6 q7)
      ( y159 === o
      &&& (y157 === o &&& __createState q1 y161 ||| (y157 === s q2 &&& (__add q2 (s q1) q3 &&& _addCreateState (s q2) q1 y161)))
      ||| ( y159 === s q4
          &&& (y157 === o &&& (s q5 === s (s q1)) ||| (y157 === s q6 &&& (____add (s q6) q1 (s q5) &&& ____add q6 (s q1) q7)) &&& greater q5 q4) ) )
  and __createState y163 y164 = success
  and _addCreateState y166 y167 y169 = fresh (q1) (y166 === o &&& __createState y167 y169 ||| (y166 === s q1 &&& _addCreateState q1 (s y167) y169))
  and ______a12461124 y171 y172 = fresh (q1) (y172 === o ||| (y172 === s q1 &&& __a12461124 y171 q1))
  and ______fst' y173 y174 = y173 === s (s y174)
  and _a12461124AddGreaterAdd y176 y178 =
    fresh (q1 q2 q3 q4 q5 q6 q7)
      ( y178 === o
      &&& (y176 === s q1 &&& (__add (s q1) q2 q3 &&& ______add q1 (s q2)))
      ||| (y178 === s q4 &&& (y176 === s q5 &&& (s q5 === q6 &&& ____add q6 q2 (s q7) &&& ______add q5 (s q2)) &&& greater q7 q4)) )
  and _______fst' y179 y180 = success
  and ________fst' y182 = success
  and ________snd' y184 y185 y186 = y186 === s y185
  and _get_capacity y187 y188 y189 = fresh (q1) (y189 === fst &&& _____fst' y187 y188 q1 ||| (y189 === snd &&& _____snd' y187 y188 q1))
  and _________snd' y191 y192 = success
  and __________snd' y194 = success
  and __get_capacity y196 y197 y198 = fresh (q1) (y198 === fst ||| (y198 === snd &&& ________snd' y196 y197 q1))
  and ___get_capacity y200 y201 = fresh (q1) (y201 === fst &&& fst' y200 q1 ||| (y201 === snd &&& snd' y200 q1))
  and ___anotherBottle y203 = y203 === fst
  and __addCreateState y204 y205 = fresh (q1) (y204 === o &&& _createState y205 ||| (y204 === s q1 &&& __addCreateState q1 (s y205)))
  and __anotherBottle = success
  and ___a12461124 = success
  and anotherBottle = success in
  checkAnswer x0 x1 x2

let res = run qrs (fun q p r -> topLevelRU q p r) (fun q p r -> (q, p, r))

let _ =
   let x = Stream.take ~n:2 res in
   ignore x
