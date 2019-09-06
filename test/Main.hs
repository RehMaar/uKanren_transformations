module Main where

import Data.Char
import System.Environment
import System.Process (system)
import System.Exit (ExitCode)
import DotPrinter
import qualified SeqUnfold as SU
import qualified RandUnfold as RU
import qualified Desert as ProgsD
import qualified Bottles as ProgsB
import qualified Path as ProgsP
import qualified Unify as ProgsU
import qualified DTree as DT
import qualified DTResidualize as DTR

fst3 (a, _, _) = a

statTree :: DT.DTree -> IO ()
statTree t = do
  let d = DT.countDepth t
  let (l, p) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " Nodes: " ++ show n

statMTree :: DTR.MarkedTree -> IO ()
statMTree t = do
  let d = DTR.countDepth t
  let (l, f, s) = DTR.countLeafs t
  let (n, fn) = DTR.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " Fail: " ++ show f ++ " Success: " ++ show s ++ " Nodes: " ++ show n ++ " FunCall: " ++ show fn

targetGoal = ProgsB.query

main = do
  args <- getArgs
  let seed = case args of
            [x] | all isNumber x -> read x :: Int
            _   -> error "Expected seed is a number, but something else was given."
  let t = fst3 $ RU.topLevel seed targetGoal
  putStr "Original -> "
  statTree t
  let mt = DTR.makeMarkedTree t
  putStr "Marked   -> "
  statMTree mt
  let cmt = DTR.cutFailedDerivations mt
  putStr "Cut      -> "
  statMTree cmt
  putStrLn $ "^ seed: " ++ show seed ++ "\n"
