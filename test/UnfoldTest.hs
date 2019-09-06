module UnfoldTest where

import Syntax
import DotPrinter
import SldTreePrinter
import GlobalTreePrinter

import Control.Monad
import System.Process (system)
import System.Exit (ExitCode)
import Data.List
import Text.Printf
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set


import qualified Driving as D
import qualified Unfold as U
import qualified CPD
import qualified GlobalControl as GC


import qualified SeqUnfold as SU
import qualified FullUnfold as FU
import qualified RandUnfold as RU

import qualified DTree as DT
import qualified DTResidualize as DTR

import qualified List as Progs
import qualified Programs as Progs
import qualified Sort as Progs
import qualified Num as Progs
import qualified Bool as Progs
import qualified Bottles as ProgsB
import qualified Desert as ProgsD
import qualified Path as ProgsP
import qualified Unify as ProgsU
import qualified Sudoku4x4 as ProgsS

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
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevelCPD" Nothing pur
--    system ("cp " ++ name ++ " ocanrenTest/src/" ++ name)

open goal = openInPdf $ fst3 $ SU.topLevel goal

openM goal = openInPdf $ DTR.makeMarkedTree $ fst3 $ SU.topLevel goal

res goal = let
    (tree, logicGoal, names) = SU.topLevel goal
    -- let f = residualizeGlobalTree tree
    -- let pur = purification (f $ vident <$> logicGoal, vident <$> reverse names)
  in DTR.topLevel tree

pur goal = let
    (tree, logicGoal, names) = SU.topLevel goal
    f = DTR.topLevel tree
    (goal', names', defs) = P.purification (f, vident <$> reverse names)
  in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

purFU goal = let
    (tree, logicGoal, names) = FU.topLevel goal
    f = DTR.topLevel tree
  in P.purification (f, vident <$> reverse names)

purRU seed goal = let
    (tree, logicGoal, names) = RU.topLevel seed goal
    f = DTR.topLevel tree
  in P.purification (f, vident <$> reverse names)

purId goal = let
    (tree, logicGoal, names) = SU.topLevel goal
    f = DTR.topLevel tree
    (goal', names', defs) = P.identity (f, vident <$> reverse names)
  in (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)

ocanrenId filename goal = do
    let p = purId goal
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevelSU" Nothing p

ocanren filename goal = do
    let p = pur goal
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevelSU" Nothing p

ocanrenGen pur filename goal = do
    let p = pur goal
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevelMy" Nothing p

ocanrenSimple filename goal = do
    let (_, _, names) = U.goalXtoGoalS goal
    let p = P.purification (goal, vident <$> reverse names)
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevel" Nothing p

ocanrenPrint goal = do
    let p = pur goal
    putStrLn $ OC.ocanrenize' "topLevel" p

ocanren'' goal = do
    let (tree, logicGoal, names) = SU.topLevel goal
    let as = vident <$> reverse names
    let f = DTR.topLevel tree
    let (goal', names', defs) = P.purification (f, as)
    let p = (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
    -- putStrLn $ OC.ocanrenize' "topLevel" p
    OC.topLevel "a.ml" "topLevelSU" Nothing p

ocanrenRU'' seed goal = do
    let (tree, logicGoal, names) = RU.topLevel seed goal
    let as = vident <$> reverse names
    let f = DTR.topLevel tree
    let (goal', names', defs) = P.purification (f, as)
    let p = (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
    -- putStrLn $ OC.ocanrenize' "topLevel" p
    OC.topLevel "a.ml" "topLevelRU" Nothing p



{-ocanrenP filename goal = do
    let (tree, logicGoal, names) = SU.topLevel goal
    let f = DTR.topLevel' [] tree
    let (goal', names', defs) = P.purification (f, vident <$> reverse names)
    let p = (goal', names', (\(n1, n2, n3) -> (n1, n2, fromJust $ DTR.simplify n3)) <$> defs)
    let name = (printf "%s.ml" filename)
    OC.topLevel name "topLevel" Nothing p-}

returnSubtreeWithNode :: DT.DTree -> DT.DGoal -> Maybe DT.DTree
returnSubtreeWithNode t@(DT.Or ts _ (CPD.Descend dg _)) goal
  | dg == goal
  = Just t
  | otherwise
  = DT.findFirst (flip returnSubtreeWithNode goal) ts
returnSubtreeWithNode t@(DT.And ts _ (CPD.Descend dg _)) goal
  | dg == goal
  = Just t
  | otherwise
  = DT.findFirst (flip returnSubtreeWithNode goal) ts
returnSubtreeWithNode (DT.Gen t _) goal = returnSubtreeWithNode t goal
returnSubtreeWithNode _ _ = Nothing

returnSubtreeWithNodeM :: DTR.MarkedTree -> DT.DGoal -> Maybe DTR.MarkedTree
returnSubtreeWithNodeM t@(DTR.Or ts _ dg _) goal
  | dg == goal
  = Just t
  | otherwise
  = DT.findFirst (flip returnSubtreeWithNodeM goal) ts
returnSubtreeWithNodeM t@(DTR.And ts _ dg _) goal
  | dg == goal
  = Just t
  | otherwise
  = DT.findFirst (flip returnSubtreeWithNodeM goal) ts
returnSubtreeWithNodeM (DTR.Gen t _) goal = returnSubtreeWithNodeM t goal
returnSubtreeWithNodeM t@(DTR.Leaf goal _) goal2
  | goal == goal2
  = Just t
returnSubtreeWithNodeM _ _ = Nothing

collectOrAndNodes :: DT.DTree -> [DT.DGoal]
collectOrAndNodes (DT.Or ts _ dg) = CPD.getCurr dg : concatMap collectOrAndNodes ts
collectOrAndNodes (DT.And ts _ dg) = CPD.getCurr dg : concatMap collectOrAndNodes ts
collectOrAndNodes (DT.Gen t _) = collectOrAndNodes t
collectOrAndNodes _ = []

collectOrNodeMT :: DTR.MarkedTree -> [(DT.DGoal, Bool)]
collectOrNodeMT (DTR.Or ts _ dg flag) = (dg, flag) : concatMap collectOrNodeMT ts
collectOrNodeMT (DTR.And ts _ dg flag) = concatMap collectOrNodeMT ts
collectOrNodeMT (DTR.Gen t _) = collectOrNodeMT t
collectOrNodeMT _ = []

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
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++  " (Pruned: " ++ show p ++ ")" ++ " Nodes: " ++ show n

statMTree :: DTR.MarkedTree -> IO ()
statMTree t = do
  let d = DTR.countDepth t
  let (l, f, s) = DTR.countLeafs t
  let (n, fn) = DTR.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " Fail: " ++ show f ++ " Success: " ++ show s ++ " Nodes: " ++ show n ++ " FunCallNodes: " ++ show fn


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

testGenLetArgs = True --all id [test1, test2, test3]
--   where
--     test1 = DTR.genLetArgs [Invoke "test" [V 0, V 1]] == [V 0, V 1]
--     test2 = null (DTR.genLetArgs [Invoke "test" [C "S" [C "O" []]]] :: [Term X])
--     test3 = DTR.genLetArgs [Invoke "test" [V 0, C "S" [C "O" []], V 2]] == [V 0, V 2]


testGenLetSig = all id [test1, test2, test3]
  where
    test1 = DTR.genLetSig [Invoke "test" [V 0, V 1]] == ("test", [V 0, V 1])
    test2 = DTR.genLetSig [Invoke "test" [C "S" [C "O" []]]] == ("test", [] :: [Term X])
    test3 = DTR.genLetSig [Invoke "test" [V 0, C "S" [C "O" []], V 2]] == ("test", [V 0, V 2])

testMWL = DTR.mapTwoLists [1, 2, 2] [1, 2, 3] == Nothing
       && DTR.mapTwoLists [] [] == Just ([] :: [(S, S)])
       && DTR.mapTwoLists [1] [1] == Just [(1, 1)]
       && DTR.mapTwoLists [1] [2] == Just [(1, 2)]
       && DTR.mapTwoLists [1, 2] [2, 5] == Just [(1, 2), (2, 5)]


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

tests' = [test1Call
         , test1Call'
         , test1Call''
         , test1Call'''
         , test2Call
--         , test2Call'
       , test3Call
       , test4Call
       , testH1
         , testH2]

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


test1Call''' = Progs.doubleAppendo $ fresh ["a", "b", "c", "d"]
              (call "doubleAppendo" [V "d", V "b", V "d", V "c"])

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
testML = testH1

testH1' = Progs.maxo $ fresh ["a", "r"]
           (call "maxo" [V "a", V "r"])

testH2 = Progs.sorto $ fresh ["xs", "ys"]
           (call "sorto" [V "xs", V "ys"])
testSort = testH2

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

mygoal = [Invoke "addo" [V (3 :: Int),V 2,V 4],Invoke "addo" [C "S" [C "S" [C "O" []]],V 7,V 2],Invoke "mulo" [V 5,C "S" [C "S" [C "O" []]],V 7]]
ancs = Set.fromList  [[Invoke "addo" [V (3 :: Int),V 2,V 4],Invoke "mulo" [V 0,C "S" [C "S" [C "O" []]],V 2]],[Invoke "addo" [C "S" [C "S" [C "O" []]],V 2,C "S" [C "S" [C "S" [C "O" []]]]],Invoke "mulo" [V 0,C "S" [C "S" [C "O" []]],V 2]],[Invoke "mulo" [C "S" [C "S" [C "O" []]],C "S" [C "S" [C "O" []]],C "S" [C "S" [C "S" [C "O" []]]]]],[Invoke "sqro" [C "S" [C "S" [C "O" []]],C "S" [C "S" [C "S" [C "O" []]]]]]]

testSimple = Progs.appendo $ fresh ["x", "y", "r"] $ call "appendo" [V "x", V "y", V "r"]

---

cmpWithRand seed goal = do
    statTree $ fst3 $ SU.topLevel goal
    -- statTree $ fst3 $ RU.topLevel seed goal

findGoal :: DT.DGoal -> DT.DTree -> Maybe DT.DTree
findGoal g t@(DT.Or ts _ g')
  | CPD.isVariant g (CPD.getCurr g') = Just t -- (CPD.getCurr g')
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g t@(DT.And ts _ g')
  | CPD.isVariant g (CPD.getCurr g')  = Just t --(CPD.getCurr g')
  | otherwise = getFirst $ mconcat $ (First . findGoal g) <$> ts
findGoal g (DT.Gen t _) = findGoal g t
findGoal g t@(DT.Leaf g' _ _)
  | CPD.isVariant g (CPD.getCurr g') = Just t -- (CPD.getCurr g')
findGoal _ _ = Nothing

goal = ProgsP.query1

-- t = fst3 $ RU.topLevel 44 ProgsB.query
-- mt = DTR.makeMarkedTree t
-- cmt = DTR.cutFailedDerivations mt
-- 
-- g =  [Invoke "add" [C "s" [C "o" []], C "s" [C "s" [V (73 :: Int)]], C "o" []]]


gl = Let def goal
  where
    def = ("test", ["x1", "x2"], body)
    goal = Invoke "test" [C "S" [C "O" []], C "O" []]
    body = Fresh "q1" $ Fresh "q2" $
             (Fresh "q3" $ V "q3" === V "q1" &&& V "q1" === V "x2") ||| (Fresh "q4" $ V "q3" === V "q2" &&& V "q1" === V "x2")
