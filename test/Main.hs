module Main where

import qualified SeqUnfold as SU
import qualified Desert as ProgsD
import qualified DTree as DT

fst3 (a, _, _) = a

statTree :: DT.DTree -> IO ()
statTree t = do
  let d = DT.countDepth t
  let (l, p) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " (Pruned: " ++ show p ++ ")" ++ " Nodes: " ++ show n

main = do
  let t = fst3 $ SU.topLevel ProgsD.query
  statTree t
