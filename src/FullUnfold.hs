{- Test results.

* doubleAppendo a b c d -- Depth: 4  Leafs: 4  Nodes: 7
* reverso a b           -- Depth: 4  Leafs: 4  Nodes: 8
* reverso [1, 2, 3] b   -- Depth: 5  Leafs: 4  Nodes: 8
* revacco a acc b       -- Depth: 4  Leafs: 2  Nodes: 5
* revacco a [] b        -- Depth: 7  Leafs: 3  Nodes: 9
* sorto xs ys           -- Depth: 7  Leafs: 8  Nodes: 17
* maxLengtho x m l      -- Depth: 13 Leafs: 89 Nodes: 157

Too long:
* bottles (query)
* desert (query)

-}

module FullUnfold where

import DTree
import Syntax

import qualified CPD
import qualified Eval as E
import qualified GlobalControl as GC

import Data.Maybe (mapMaybe)
import Data.List (group, sort)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Text.Printf
import DotPrinter
import Unfold

import Debug.Trace

newtype FUGoal = FUGoal DGoal

topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = FUGoal [lgoal]
  tree = fst $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

instance Unfold FUGoal where
  getGoal (FUGoal dgoal) = dgoal

  initGoal = FUGoal

  emptyGoal (FUGoal dgoal) = null dgoal

  mapGoal (FUGoal dgoal) f = FUGoal (f dgoal)

  unfoldStep = fullUnfoldStep
    where
      fullUnfoldStep :: FUGoal  -> E.Gamma -> E.Sigma -> ([(E.Sigma, FUGoal)], E.Gamma)
      fullUnfoldStep (FUGoal goal) env subst = let
          (newEnv, unfoldedGoal) = unfoldAll env goal
          n = (goalToDNF <$> unfoldedGoal)
          -- Goal :: [DNF of each body] :: [Body DNF [[Conj]]]
          normalizedGoal = conjOfDNFtoDNF n
          -- Goal :: [Unified DNF] :: [Body DNF [[Conj] and Substs]]
          unifiedGoal = (\(conj, subst) -> (subst, FUGoal $ E.substituteConjs subst conj)) <$> unifyAll subst normalizedGoal
        in (unifiedGoal, newEnv)



{-
topLevel :: G X -> (DTree, G S, [S])
topLevel g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  descendGoal     = dGoal lgoal Set.empty
  tree = fst $ derivationStep descendGoal lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)


totalDepth = 6

derivationStep
  :: DDescendGoal      -- Conjunction of invokes and substs.
  -> E.Gamma           -- Context
  -> E.Sigma           -- Substitution
  -> Set.Set DGoal     -- Already seen
  -> Int -- Debug depth
  -> (DTree, Set.Set DGoal)
derivationStep d@(CPD.Descend goal ancs) env subst seen depth
 -- | depth >= 4
 -- = (Prune d, seen)
  | CPD.variantCheck goal seen
  -- =  trace ("Is variant: " ++ show goal ++ " " ++ (show $ getVariant goal seen)) (Leaf d subst env, seen) -- We didn't add `Leaf' to the `seen' set.
  = (Leaf d subst env, seen) -- We didn't add `Leaf' to the `seen' set.
  | otherwise
  = let
    newAncs = Set.insert goal ancs
    newSeen = Set.insert goal seen
  in case fullUnfoldStep goal env subst of
     ([], _)          -> (Fail, newSeen)
     (uGoals, newEnv) -> let
         (seen', ts) = foldl (\(seen, ts) g -> (:ts) <$> evalSubTree depth newEnv newAncs seen g) (newSeen, []) uGoals
       in (Or (reverse ts) subst d, seen')

evalSubTree depth _ _ seen (subst, []) = (seen, Success subst)
evalSubTree depth env ancs seen (subst, goal)
  | not (CPD.variantCheck goal seen)
  , isGen goal ancs
  = let
      descend  = CPD.Descend goal ancs
      newAncs  = Set.insert goal ancs
      absGoals = GC.abstractChild ancs (subst, goal, Just env)
      (seen', ts) = foldl (\(seen, ts) g -> (:ts) <$> evalGenSubTree depth newAncs seen g) (seen, []) absGoals
    in (seen', And (reverse ts) subst descend)
  | otherwise
  = let
      descend = CPD.Descend goal ancs
      (tree, seen') = derivationStep descend env subst seen (1 + depth)
    in (seen', tree) -- Node tree descend subst)

evalGenSubTree depth ancs seen (subst, goal, gen, env) = let
    descend = CPD.Descend goal ancs
    (newDepth, subtree) = if null gen then (1 + depth, tree) else (2 + depth, Gen tree gen)
    (tree, seen') = derivationStep descend env subst seen newDepth
    -- subtree = if null gen then tree else Gen tree gen
  in (seen', subtree)
-}
{-

topLevel' :: G X -> (DTree, G S, [S])
topLevel' g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  descendGoal     = dGoal lgoal Set.empty
  tree = derivationStep' descendGoal lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)

derivationStep'
  :: DDescendGoal      -- Conjunction of invokes and substs.
  -> E.Gamma           -- Context
  -> E.Sigma           -- Substitution
  -> Set.Set DGoal     -- Already seen
  -> Int -- Debug depth
  -> DTree
derivationStep' d@(CPD.Descend goal ancs) env subst seen depth
  -- | depth >= totalDepth
  -- = Prune d
  | CPD.variantCheck goal seen
  -- = trace ("Is variant: " ++ show goal ++ " " ++ (show $ getVariant goal seen)) $ Leaf d subst env
  = Leaf d subst env
  -- Unfold all.
  | otherwise
  = let
      -- Goal :: [Body of each Invoke]
      (newEnv, unfoldedGoal) = unfoldAll env goal
      n = (goalToDNF <$> unfoldedGoal)
      -- Goal :: [DNF of each body] :: [Body DNF [[Conj]]]
      normalizedGoal = conjOfDNFtoDNF n
      -- Goal :: [Unified DNF] :: [Body DNF [[Conj] and Substs]]
      unifiedGoal = (\(conj, subst) -> (subst, E.substituteConjs subst conj)) <$> unifyAll subst normalizedGoal

      newAncs = Set.insert goal ancs
      newSeen = Set.insert goal seen
    in step unifiedGoal newEnv newAncs newSeen
    where
      run f init [] = []
      run f init (x:xs) = let tree = f init x in tree : run f (Set.union init $ treeGoals tree) xs

      step [] _ _ _ = Fail
      step xs env' ancs seen = Or (run (step' env' ancs) seen xs) subst d

      step' _ _ _ (subst', []) = Success subst'
      step' env' ancs' seen' (subst', cs)
        | not (CPD.variantCheck cs seen')
        , isGen cs ancs'
        = let
            gen = GC.abstractChild ancs' (subst', cs, Just env')
            ancs'' = Set.insert cs ancs'
          in And (run (stepGen ancs'') seen' gen) subst' (CPD.Descend cs ancs')
        | otherwise
        = let
            descend = CPD.Descend cs ancs'
            tree = derivationStep' descend env' subst' seen' (2 + depth)
          in tree -- Node tree descend subst'

      stepGen ancs' seen' (subst'', goal'', [], env'')
        = tree 
        where
          tree = derivationStep' descend env'' subst'' seen' (succ depth)
          descend = CPD.Descend goal'' ancs'
      stepGen ancs' seen' (subst'', goal'', gen'', env'')
        = if null gen'' then tree else Gen tree gen''
        where
          tree = derivationStep' descend env'' subst'' seen' (2 + depth)
          descend = CPD.Descend goal'' ancs'

-}


-- Return value is Conj (G S), but now (G S) is a body of corresponding Invoke.
unfoldAll :: E.Gamma -> Conj (G S) -> (E.Gamma, Conj (G S))
unfoldAll gamma = foldl unfold' (gamma, [])
  where
    unfold' (gamma, goals) inv = (:goals) <$> unfold inv gamma

showUnified :: Disj (E.Sigma, Conj (G S)) -> String
showUnified = concatMap (\(subst, conj) -> "(" ++ show (null subst) ++ ", " ++ show conj ++ ")")
