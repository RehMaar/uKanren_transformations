{- Test results

* doubleAppendo a b c d -- Depth: 5  Leafs: 4  Nodes: 10
* reverso a b           -- Depth: 4  Leafs: 4  Nodes: 8
* reverso [1, 2, 3] b   -- Depth: 12 Leafs: 7  Nodes: 24
* revacco a acc b       -- Depth: 4  Leafs: 2  Nodes: 5
* revacco a [] b        -- Depth: 7  Leafs: 3  Nodes: 9
* sorto xs ys           -- Depth: 7  Leafs: 8  Nodes: 17
* maxLengtho x m l      -- Depth: 12 Leafs: 14 Nodes: 35

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
import Unfold

import Debug.Trace

trace' _ = id

data SUGoal = SUGoal DGoal Int

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = SUGoal [lgoal] 0
  tree = fst $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)


instance Unfold SUGoal where
  getGoal (SUGoal dgoal _) = dgoal

  initGoal goal = SUGoal goal 0

  emptyGoal (SUGoal dgoal _) = null dgoal

  mapGoal (SUGoal dgoal idx) f = SUGoal (f dgoal) idx

  unfoldStep = seqUnfoldStep


seqUnfoldStep :: SUGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, SUGoal)], E.Gamma)
seqUnfoldStep (SUGoal dgoal idx) env subst = let
    (immut, conj, mut) = splitGoal idx dgoal
  -- in trace ("Goal: " ++ show dgoal ++ "\n Unfold: " ++ show conj) $ let
    (newEnv, uConj) = unfold conj env

    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, suGoal subst immut cs mut)) <$> unConj
  in (us, newEnv)
  where
    suGoal subst immut cs mut = let
        goal = E.substituteConjs subst $ immut ++ cs ++ mut
        newIdx = let i = idx + length cs in if i >= length goal then 0 else i
      in SUGoal goal newIdx

{-
topLevel' :: G X -> (DTree, G S, [S])
topLevel' g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  descendGoal = CPD.Descend [lgoal] Set.empty
  tree = derivationStep' descendGoal 0 lgamma E.s0 Set.empty  0
  in (tree, lgoal, lnames)

derivationStep'
  :: DDescendGoal    -- Conjunction of invokes and substs.
  -> Int             -- Index of the conj in the ^ we need to unfold
  -> E.Gamma         -- Context
  -> E.Sigma         -- Substitution
  -> Set.Set DGoal   -- Already seen
  -> Int -- Debug, depth
  -> DTree
derivationStep' d@(CPD.Descend goal ancs) idx env subst seen depth
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
            tree = derivationStep' dgoal nextIdx env subst seen (succ depth)
          -- in Node tree dgoal subst
          in tree

        stepGen ancs seen (subst, goal, gen, env) = let
            tree = derivationStep' (CPD.Descend goal ancs) 0 env subst seen (succ depth)
          in if null gen then tree else Gen tree gen


showAbs = concatMap showAbs'
  where
    showAbs' (subst, goal, gen, _) = "(" ++ show subst ++ ", " ++ show goal ++ ", " ++ show gen ++ ")"
-}

-- TODO: it's not very smart splitting, but do I have to do it better?
splitGoal _ [] = error "wtf?"
splitGoal _ [g] = ([], g, [])
splitGoal idx gs | idx >= length gs = splitGoal 0 gs
splitGoal idx gs = let
    ls = take idx gs
    c  = gs !! idx
    rs = drop (succ idx) gs
  in (ls, c, rs)
