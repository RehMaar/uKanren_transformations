{-
Эксперементы
* doubleAppendo -- depth: 7, leafs: 4
* reverso -- depth: 5, leafs: 4
* revacco -- depth: 3, leafs: 2
* maxLenghto -- depth: 17, leafs 14
* sorto -- depth: 9, leafs: 8
* bottles (query) -- :(
* desert (query) -- :(
-}


module SeqUnfold where
    
import Syntax
import DTree

import qualified CPD
import qualified Eval as E
import qualified Purification as P
import qualified GlobalControl as GC

import Data.Maybe (mapMaybe)
import Data.List (group, sort)
import qualified Data.Set as Set

import Text.Printf
import DotPrinter

import Debug.Trace

trace' _ = id

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  descendGoal = CPD.Descend [lgoal] Set.empty
  tree = derivationStep descendGoal 0 lgamma E.s0 Set.empty  0
  in (tree, lgoal, lnames)

derivationStep
  :: DDescendGoal    -- Conjunction of invokes and substs.
  -> Int             -- Index of the conj in the ^ we need to unfold
  -> E.Gamma         -- Context
  -> E.Sigma         -- Substitution
  -> Set.Set DGoal   -- Already seen
  -> Int -- Debug, depth
  -> DTree
derivationStep d@(CPD.Descend goal ancs) idx env subst seen depth
  | depth >= 10
  = Prune d
  | CPD.variantCheck goal seen
  = Leaf d subst env -- (getVariant goal seen)
  | otherwise
  = trace' ("\n>> Goal: " ++ show goal ++ " Idx: " ++ show idx) $ let
    -- immute -- неизменяемая часть конъюнкции, которую уже обработали
    -- conj -- конъюнкция, которую обрабатываем на данном шаге
    -- mute -- часть конъюнкции, которую ещё будем изменять дальше
    (immute, conj, mute) = splitGoal idx goal
    -- uEnv -- обновлённое окружение
    -- uConj -- тело вызова `conj`
    (uEnv, uConj) = unfold conj env
    -- Преобразуем тело в обычное ДНФ
    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
  -- in trace ("\n$$$Unfolded: " ++ show unConj) $ let
    newAncs = Set.insert goal ancs
    newSeen = Set.insert goal seen

  in step unConj immute mute uEnv newAncs newSeen
  where
    -- Поочердёно применяем f к списку xs, передавая обработанный результат в следующую функцию
    -- Используем для раскрытия конъюнкции.
    run f init [] = []
    run f init (x:xs) = let tree = f init x in tree : run f (Set.union init $ treeGoals tree) xs

    step [] _ _ _ _ _ = Fail
    -- cs -- раскрытая часть конъюнкции
    -- immut -- часть исходной цели-конъюнкции, которую не раскарываем
    -- mut -- часть исходной цели-конъюнкции, которую ещё нужно будет расскрыть
    -- env -- окружение
    -- ancs -- предки узла
    -- seen -- уже просмотренные узлы дерева
    -- idx -- индекс конъюнкции, которую мы расскрыли, в исходной конъюнкции
    step cs immut mut env ancs seen = Or (run step' seen cs) subst d
      -- error $ "Cs: " ++ show cs ++ " immut: " ++ show immut ++ " mut: " ++ show mut ++ " | Goal: " ++ show goal
      where
        -- Получаем сюда immut, с и mut
        -- склеиваем
        -- делаем substituteConjs
        -- проверяем на всякие вариант-чеки и эмбединг
        -- пускаем дальше
        step' seen (c, subst) = let
            goal = E.substituteConjs subst (immut ++ c ++ mut)
          in trace' ("\n> STEP': Goal: " ++ show (length goal) ++ " = immut: " ++ show (length immut) ++ " c: " ++ show (length c) ++ " mut: " ++ show (length mut)) $ let
            dgoal = CPD.Descend goal ancs
          in
          if null goal
          then Success subst
          -- Если новая цель это вариант просмотренных узлов
          else if CPD.variantCheck goal seen
          -- То добавляем новый лист
          then trace' "\nLEAF" $ Leaf dgoal subst env -- (getVariant goal seen)
          -- Если в новую цель эмбедятся предки
          else if isGen goal ancs
          -- то обобщаем
          -- then Gen (Leaf dgoal subst env) subst --error $ "\n##Gen: " ++ show goal ++ " -- " ++ show ancs
          then let
             newAncs = Set.insert goal ancs
             newSeen = Set.insert goal seen
          --in trace ("\nGOAL: " ++ show goal ++ "\nAncs: " ++ show ancs) $ let
             abs = GC.abstractChild ancs (subst, goal, Just env)
          in trace' ("\nGen: " ++ showAbs abs) $ And (run (stepGen newAncs) newSeen abs) subst dgoal
          -- Иначе делаем следующий шаг
          else let
            -- TODO: выглядит не очень надёжно
            nextIdx = let i = length immut + length c in if i >= length goal then 0 else i
            tree = derivationStep dgoal nextIdx env subst seen (succ depth)
          in Node tree dgoal subst

        stepGen ancs seen (subst, goal, gen, env) = let
            tree = derivationStep (CPD.Descend goal ancs) 0 env subst seen (succ depth)
          in if null gen then tree else Gen tree gen

showAbs = concatMap showAbs'
  where
    showAbs' (subst, goal, gen, _) = "(" ++ show subst ++ ", " ++ show goal ++ ", " ++ show gen ++ ")"

-- TODO: it's not very smart splitting, but do I have to do it better?
splitGoal _ [] = error "wtf?"
splitGoal _ [g] = ([], g, [])
splitGoal idx gs | idx >= length gs = splitGoal 0 gs
splitGoal idx gs = let
    ls = take idx gs
    c  = gs !! idx
    rs = drop (succ idx) gs
  in (ls, c, rs)
