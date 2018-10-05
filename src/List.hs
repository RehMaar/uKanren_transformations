module List where

import Syntax
import Stream
import Num
import Prelude hiding (succ)
import Text.Printf

-- Tests
infixr 9 %

nil   = C "Nil"  []
x % y = C "Cons" [x, y]
lit x = C x      []

a = lit "a"
b = lit "b"
c = lit "c"
d = lit "d"

list (V n) = printf "._%s" (show n)
list (C "Cons" [h, t]) = printf "%s %% %s" (list h) (list t)
list (C "Nil"  _     ) = "nil"
list (C s []) = s
list x = show x

nilo g =
  let l = V "l" in
  Let ( def "nilo" ["l"] ( l === nil ) ) g

singletono g =
  let l = V "l" in
  let x = V "x" in
  Let ( def "singletono" ["l", "x"] ( l === x % nil ) ) g

lengtho g =
  let x = V "x" in
  let l = V "l" in
  let h = V "h" in
  let t = V "t" in
  let z = V "z" in
  Let (def "lengtho" ["x", "l"]
        (
          (x === nil &&& l === zero) |||
          (fresh ["h", "t", "z"]
            (
              x === h % t &&&
              l === succ z &&&
              call "lengtho" [t, z]
            )
          )
        )
      ) g

appendo g =
  let x  = V "x"  in
  let y  = V "y"  in
  let xy = V "xy" in
  let h  = V "h"  in
  let t  = V "t"  in
  let ty = V "ty" in
  Let
    (def "appendo" ["x", "y", "xy"]
         ((x === nil &&& xy === y) |||
          (fresh ["h", "t", "ty"]
             (x  === h % t  &&&
              xy === h % ty &&&
              call "appendo" [t, y, ty]
             )
          )
         )
    ) g

appendo' g =
  let x  = V "x"  in
  let y  = V "y"  in
  let xy = V "xy" in
  let h  = V "h"  in
  let t  = V "t"  in
  let ty = V "ty" in
  Let
    (def "appendo'" ["x", "y", "xy"]
           ((x === nil ||| xy === y) |||
            (fresh ["h", "t", "ty"]
               (x  === h % t  |||
                xy === h % ty |||
                call "appendo'" [t, y, ty]
               )
            )
           )
    ) g

reverso g =
  let x  = V "x"  in
  let y  = V "y"  in
  let h  = V "h"  in
  let t  = V "t"  in
  let rt = V "rt" in
  Let
    (def "reverso" ["x", "y"]
           ((x === nil &&& y === nil) |||
            (fresh ["h", "t", "rt"]
               (x === h % t &&&
                call "reverso" [t, rt] &&&
                call "appendo" [rt, h % nil, y] -- &&&
               )
            )
           )
    ) $ appendo g

revAcco g =
  let xs = V "xs"
      acc = V "acc"
      sx = V "sx"
      h = V "h"
      t = V "t"
  in
  Let
    (def "revacco" ["xs", "acc", "sx"]
       (
         (xs === nil &&& sx === acc) |||
         (fresh ["h", "t"]
           (xs === h % t) &&&
           call "revacco" [t, h % acc, sx]
         )
       )
    ) g
