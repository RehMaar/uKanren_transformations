module Main where

import System.Process (system)
import System.Exit (ExitCode)
import DotPrinter
import qualified SeqUnfold as SU
import qualified Desert as ProgsD
import qualified Bottles as ProgsB
import qualified DTree as DT

fst3 (a, _, _) = a

statTree :: DT.DTree -> IO ()
statTree t = do
  let d = DT.countDepth t
  let (l, p) = DT.countLeafs t
  let n = DT.countNodes t
  putStrLn $ "Depth: " ++ show d ++ " Leafs: " ++ show l ++ " (Pruned: " ++ show p ++ ")" ++ " Nodes: " ++ show n

printToPdf :: DotPrinter a => String -> a -> IO ExitCode
printToPdf name t = do
    let dotfilename = name ++ ".dot"
    let pdffilename = name ++ ".pdf"
    printTree dotfilename t
    system $ "dot -Tpdf '" ++ dotfilename ++ "' > '" ++ pdffilename ++ "'"

main = do
  let t = fst3 $ SU.topLevel ProgsB.query
  statTree t
--  printToPdf "a" t
