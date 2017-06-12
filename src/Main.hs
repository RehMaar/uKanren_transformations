module Main where
import MuKanren
import Driver
import Residualization
import Debug.Trace
import Programs
import Control.Monad.State
import Data.Maybe (fromJust)

run k a =
  let
      take k (Immature s) | k > 0 = take k s
      take k (Mature h t) | k > 0 = Mature h $ take (k-1) t
      take k _ = Empty
  in take k $ eval a emptyState

main =
  do
--    print $ getRenaming (call (fun "blah" $ Uni Nil Nil ) [Var 1, Var 2, Var 4])
--                        (call (fun "blah" $ Uni Nil Nil ) [Var 2, Var 4, Var 6])
--     print $ getSubst (makeSubst [(1::Int,Var 2), (2, Var 13)]) 1

--    let x = callFresh (\x -> callFresh (\y -> callFresh (\z -> (x === y) &&& (y === z) ) ) )
--    print $ run 10 x

--    let x = callFresh (\x -> callFresh (\y -> callFresh (\z -> (x === pair y z) &&& (z === Nil) ||| (z === x) ) ) )
--    print $ drive x
--    print $ run 10 (fromJust $ residualize $ drive x)
--    print $ run 10 x

--    let red = residualize (Success ([(2, pair (var 3) (var 5)), (0, pair (var 3) (var 4))], 0))
--    print $ case red of {Just r -> show $ eval r emptyState; Nothing -> "smth wrong"}
--
--    let red = residualize (Success ([(1, var 2), (2, pair (var 3) (var 4)), (5, pair (var 3) (var 6)), (6, nil)], 0))
--    print $ case red of {Just r -> show $ eval r emptyState; Nothing -> "smth wrong"}

--    print $ reify' (var 0) (Mature ([((1::Var),pair (var 2) nil), (4, nil), (3, pair (var 5) (var 6)), (0, pair (var 2) (var 3))], 10) Empty)

--    print $ residualize'( drive (callFresh (\xs -> callFresh (\ys -> callFresh (\zs -> call (appendo xs ys zs) [xs, ys, zs])))))
--
--    print $ residualize'(
--            drive (callFresh (\x ->
--                    callFresh (\y ->
--                    callFresh (\i ->
--                    callFresh (\z ->
--                    callFresh (\r ->
--                    call (appendo x y i) [x, y, i] &&& call (appendo i z r) [i,z,r]))))))
--                    )

    print $ drive (callFresh (\xs -> callFresh (\ys -> callFresh (\zs -> call (appendo xs ys zs) [xs, ys, zs]))))
--
--    print $
--            drive (callFresh (\x ->
--                    callFresh (\y ->
--                    callFresh (\i ->
--                    callFresh (\z ->
--                    callFresh (\r ->
--                    call (appendo x y i) [x, y, i] &&& call (appendo i z r) [i,z,r]))))))
--
--
--    print $ drive (callFresh (\xs -> callFresh (\sx -> call (reverso xs sx) [xs, sx])))
--
--    print $ drive (callFresh (\xs -> callFresh (\sx -> call (revAcco xs nil sx) [xs, nil, sx])))


--    print $ unfoldDet (call (appendo (Var 0) (Var 1) (Var 2)) [Var 0, Var 1, Var 2] )
--                      ([], 3)
--
--    print $ unfold (call (appendo (Var 0) (Var 1) (Var 2)) [Var 0, Var 1, Var 2] )
--                   ([], 3)

