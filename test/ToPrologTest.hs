module ToPrologTest where

import Syntax
import OCanrenize
import ToProlog
import Bridge
import Sudoku4x4
import Bottles

printInFile :: FilePath -> G X -> IO ()
printInFile file g = do
  writeFile file $ translateAndPrint g

toNat i = if i == 0 then C "o" [] else C "s" [toNat $ i - 1]


bridgeG  = game2Big      $ fresh ["a", "b"] (call "getAnswer" [V "a", C "some" [V "b"]])
sudokuG  = fst sudoku4x4 $ fresh ["a"] (call "check_sudoku" [V "a", C "true" []])
bottlesG = fst bottles   $
    fresh ["caps", "ans"]
      (call "capacities1" [V "caps"] &&&
       call "checkAnswer" [V "ans", V "caps", toNat 6, C "true" []])


printAfterPrologSpec :: String -> String -> IO ()
printAfterPrologSpec name s =
  toOCanren' ocanrenize' (name ++ "_prolog.ml") name Nothing $ prologToG s



main = do
  --printInFile "bridge.pl" bridgeG
  --printInFile "sudoku.pl" sudokuG
  --printInFile "bottles.pl" bottlesG
  readFile "bridge_spec.pl" >>= printAfterPrologSpec "bridge"
