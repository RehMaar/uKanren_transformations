module UnfoldTest where

import Syntax
import DotPrinter
import SldTreePrinter
import GlobalTreePrinter

import System.Process (system)
import System.Exit (ExitCode)
import Data.List
import Text.Printf
import Data.Maybe
import qualified Data.Set as Set

import qualified SeqUnfold as SU
import qualified FullUnfold as FU
import qualified DTree as DT
import qualified Unfold as U
import qualified CPD
import qualified GlobalControl as GC

import qualified DTResidualize as DTR

import qualified List as Progs
import qualified Programs as Progs
import qualified Sort as Progs
import qualified Num as Progs
import qualified Bool as Progs
import qualified Bottles as ProgsB
import qualified Desert as ProgsD
import qualified Path as ProgsP

import qualified CpdResidualization as CR
import qualified Purification as P
import qualified OCanrenize as OC
import qualified Residualize as R


import Miscellaneous

vident = ('x' :) . show

ocanren' filename goal = do
    let (tree, logicGoal, names) = GC.topLevel goal
    -- let f = residualizeGlobalTree tree
    -- let pur = purification (f $ vident <$> logicGoal, vident <$> reverse names)
    let f = CR.residualizationTopLevel tree
    let pur = P.purification (f, vident <$> reverse names)
    OC.topLevel (printf "%s.ml" filename) "topLevel" Nothing pur

open goal = openInPdf $ fst3 $ SU.topLevel goal

res goal = let
    (tree, logicGoal, names) = SU.topLevel goal
    -- let f = residualizeGlobalTree tree
    -- let pur = purification (f $ vident <$> logicGoal, vident <$> reverse names)
  in DTR.topLevel tree

pur goal = let
    (tree, logicGoal, names) = SU.topLevel goal
    f = DTR.topLevel tree
  in P.purification (f, vident <$> reverse names)

ocanren filename goal = do
    let p = pur goal
    OC.topLevel (printf "%s.ml" filename) "topLevel" Nothing p

{-
toProgram :: (G X -> (DT.DTree, G S, [S])) ->  G X -> G S
toProgram tl g = let
    (t, g, ns) = tl g
  in P.purification (DTR.residualize t g ns)
-}

toProgram goal = let
    (t, g, ns) = FU.topLevel goal
    (t1, ts) = DTR.residualize t g ns
  in if isJust t1 then Just $ P.purification (fromJust t1, ts) else Nothing

--
-- Save a tree into pdf file.
--
printToPdf :: DotPrinter a => String -> a -> IO ExitCode
printToPdf name t = do
    let dotfilename = name ++ ".dot"
    let pdffilename = name ++ ".pdf"
    printTree dotfilename t
    system $ "dot -Tpdf '" ++ dotfilename ++ "' > '" ++ pdffilename ++ "'"

--
-- Open pdf file of a tree (using `zathura` pdf viewer).
--
openInPdf :: DotPrinter a => a -> IO ExitCode
openInPdf t = do
    let name = "/tmp/ukanrentesttree"
    openInPdfWithName name t

openInPdfWithName :: DotPrinter a => String -> a -> IO ExitCode
openInPdfWithName name t = do
    let dotfilename = name ++ ".dot"
    let pdffilename = name ++ ".pdf"
    printTree dotfilename t
    -- dot -Tpdf '$dot' > '$tmp_pdf_file'
    system $ "dot -Tpdf '" ++ dotfilename ++ "' > '" ++ pdffilename ++ "'"
    -- zathura '$pdf'
    system $ "zathura '" ++ pdffilename ++ "'"
    -- rm '$pdf' '$dot'
    system $ "rm '" ++ pdffilename ++ "' '" ++ dotfilename ++ "'"

--
-- Tree statistic
--
statTree :: DT.DTree -> IO ()
statTree t = do
  let d = DT.countDepth t
  let (l, p) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l {- ++  " (Pruned: " ++ show p ++ ")" -} ++ " Nodes: " ++ show n

stats _ [] = return ()
stats f ((name, call):cs) = do
  putStr $ name ++ " -- "
  statTree $ fst3 $ f call
  stats f cs

runTests = all id [testFlatConj
                  , testGetVarFromTerm
                  , testGenLetArgs
                  , testGenLetSig
                  ]

--
-- Tests
--

testFlatConj = all id [testFlatConjOfDNF1, testFlatConjOfDNF2, testFlatConjOfDNF3]
  where
    t1 :: [[[String]]]
    t1 = []
    t1r = []
    t2 :: [[[String]]]
    t2 = [[["a", "b"], ["c", "d"]]]
    t2r = [["a", "b"], ["c", "d"]]
    t3 = [[["a", "b"], ["c", "d"]], [["e", "f"], ["g", "h"]]]
    t3r = [["a", "b", "e", "f"], ["c", "d", "e", "f"], ["a", "b", "g", "h"], ["c", "d", "g", "h"]]
    t4 = [[["a", "b"], ["c", "d", "e"]], [["f", "g", "h"], ["i", "j", "k"], ["l", "m"]], [["n", "o", "p"]]]

    testFlatConjOfDNF1 = U.conjOfDNFtoDNF t1 == t1r
    testFlatConjOfDNF2 = U.conjOfDNFtoDNF t2 == t2r
    testFlatConjOfDNF3 = (sort $ sort <$> U.conjOfDNFtoDNF t3) == (sort $ sort <$> t3r)
    -- testFlatConjOfDNF4 = (sort $ sort <$> DT.conjOfDNFtoDNF t4) -- == (sort $ sort <$> t4r)


testGetVarFromTerm = all id [test1, test2, test3, test4, test5]
  where
    test1 = DTR.getVarFromTerm (V 0) == [V 0]
    test2 = null $ DTR.getVarFromTerm (C "_" [])
    test3 = null $ DTR.getVarFromTerm (Progs.peanify 10)
    test4 = DTR.getVarFromTerm (C "S" [C "S" [V 0]]) == [V 0]
    test5 = DTR.getVarFromTerm (C "_" [V 0, V 1, C "_" [V 2, V 3]]) == [V 0, V 1, V 2, V 3]

testGenLetArgs = all id [test1, test2, test3]
  where
    test1 = DTR.genLetArgs [Invoke "test" [V 0, V 1]] == [V 0, V 1]
    test2 = null (DTR.genLetArgs [Invoke "test" [C "S" [C "O" []]]] :: [Term X])
    test3 = DTR.genLetArgs [Invoke "test" [V 0, C "S" [C "O" []], V 2]] == [V 0, V 2]


testGenLetSig = all id [test1, test2, test3]
  where
    test1 = DTR.genLetSig [Invoke "test" [V 0, V 1]] == ("test", [V 0, V 1])
    test2 = DTR.genLetSig [Invoke "test" [C "S" [C "O" []]]] == ("test", [] :: [Term X])
    test3 = DTR.genLetSig [Invoke "test" [V 0, C "S" [C "O" []], V 2]] == ("test", [V 0, V 2])

t1 = fst3 $ U.goalXtoGoalS $ Progs.sqro $ fresh ["r"] $ call "sqro" [Progs.peanify 2, V "r"]

t2 = [fst3 $ U.goalXtoGoalS $ test1Call']

t2R = Invoke "doubleAppendo" [V 0, V 2, V 3]

testBody = Invoke "test" []


--
-- Derivation tests
--

tests = [
  ("doubleAppendo a b c d", test1Call)
  , ("reverso a b", test2Call)
  , ("reverso [1, 2, 3] b", test2Call')
  , ("revacco a acc b", test3Call)
  , ("revacco a [] b", test4Call)
  , ("maxLengtho x m l", testH1)
  , ("sorto xs ys", testH2)]

statTestCallsSU = stats SU.topLevel tests
statTestCallsFU = stats FU.topLevel tests


--
--
--
--


-- Test double appendo
test1Call = Progs.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "a", V "b", V "c", V "d"])


-- Test double appendo
test1Call' = Progs.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "a", V "a", V "c", V "d"])


-- Test double appendo
test1Call'' = Progs.doubleAppendo $ fresh ["a", "b", "c"]
              (call "doubleAppendo" [V "a", V "b", V "c", V "c"])

-- Test reverse without acc
test2Call = Progs.reverso $ fresh ["a", "b"]
              (call "reverso" [V "a", V "b"])

-- Test reverse without acc'
test2Call' = Progs.reverso $ fresh ["a", "b"]
              (call "reverso" [Progs.peanify 1 Progs.% Progs.peanify 2 Progs.% Progs.peanify 3 Progs.% Progs.nil, V "b"])

-- Test reverse with acc
test3Call = Progs.revAcco $ fresh ["a", "b", "acc"]
              (call "revacco" [V "a", V "acc", V "b"])

-- Test reverse with acc (nil acc)
test4Call = Progs.revAcco $ fresh ["a", "b"]
              (call "revacco" [V "a", Progs.nil, V "b"])

testH1 = Progs.maxLengtho $ fresh ["x", "m", "l"]
           (call "maxLengtho" [V "x", V "m", V "l"])

testH2 = Progs.sorto $ fresh ["xs", "ys"]
           (call "sorto" [V "xs", V "ys"])

testCall = outter $ fresh ["x"] $ call "outter" [V "x"]

testCall' = gfun $ ffun $ fresh ["x"] $ call "g" [V "x"] &&& call "f" [V "x"]

testCall'' = outter' $ fresh ["x"] $ call "outter'" [V "x"]

testCallML = Progs.maxo $ Progs.lengtho $ fresh ["a", "b", "c", "d"] $
               call "maxo" [V "a", V "b"] &&& call "lengtho" [V "c", V "d"]


l = call "maxo" [V "a", V "b"] &&& call "lengtho" [V "c", V "d"]

outter :: G a -> G a
outter g =
  Let (def "outter" ["x"] (call "g" [V "x"] &&& call "f" [V "x"])) $ gfun $ ffun g

outter' :: G a -> G a
outter' g =
  Let (def "outter'" ["x"] (call "g" [V "x"] &&& call "m" [V "x"])) $ gfun $ mfun g

gfun :: G a -> G a
gfun g =
  Let (def "g" ["x"] (V "x" === Progs.nil ||| call "h" [V "x"] ||| call "m" [V "x"])) $ hfun $ mfun g

mfun :: G a -> G a
mfun g = Let (def "m" ["x"] $ (call "f" [V "x"]) ||| V "x" === Progs.nil) $ ffun $ hfun g

ffun :: G a -> G a
ffun g = Let (def "f" ["x"] (call "listo" [V "x"])) $ Progs.listo g

hfun :: G a -> G a
hfun g = Let (def "h" ["x"] (call "nilo" [V "x"])) $ Progs.nilo g

testNum1  = Progs.sqro $ fresh ["r"] $ call "sqro" [Progs.peanify 2, V "r"]
testNum1S = Progs.sqro $ call "sqro" [Progs.peanify 2, Progs.peanify 4]
testNum1F = Progs.sqro $ call "sqro" [Progs.peanify 2, Progs.peanify 3]
testBoolS1 = Progs.eveno $ call "eveno" [Progs.peanify 2]
testBoolF1 = Progs.eveno $ call "eveno" [Progs.peanify 3]
testBoolS2 = Progs.eveno $ call "eveno" [Progs.zero]

testNum2Query = Let (def "q1" ["x", "r"]
    (call "sqro" [V "x", V "r"] &&& call "eveno" [V "r"])
  ) . Progs.sqro . Progs.eveno

testNum2 = testNum2Query $ fresh ["x", "r"] $ call "q1" [V "x", V "r"]

t = fst3 $ FU.topLevel test2Call
DT.Or [_, tt2] subst1 (CPD.Descend goal1 ancs1) = t
DT.Or _ subst2 (CPD.Descend goal2 ancs2) = tt2


mygoal = [Invoke "addo" [V (3 :: Int),V 2,V 4],Invoke "addo" [C "S" [C "S" [C "O" []]],V 7,V 2],Invoke "mulo" [V 5,C "S" [C "S" [C "O" []]],V 7]]
ancs = Set.fromList  [[Invoke "addo" [V (3 :: Int),V 2,V 4],Invoke "mulo" [V 0,C "S" [C "S" [C "O" []]],V 2]],[Invoke "addo" [C "S" [C "S" [C "O" []]],V 2,C "S" [C "S" [C "S" [C "O" []]]]],Invoke "mulo" [V 0,C "S" [C "S" [C "O" []]],V 2]],[Invoke "mulo" [C "S" [C "S" [C "O" []]],C "S" [C "S" [C "O" []]],C "S" [C "S" [C "S" [C "O" []]]]]],[Invoke "sqro" [C "S" [C "S" [C "O" []]],C "S" [C "S" [C "S" [C "O" []]]]]]]

testSimple = Progs.appendo $ fresh ["x", "y", "r"] $ call "appendo" [V "x", V "y", V "r"]
