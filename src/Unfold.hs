{-# LANGUAGE ScopedTypeVariables #-}

module Unfold where
    
import DTree
import Syntax

import qualified CPD
import qualified Eval as E
import qualified GlobalControl as GC
import qualified Purification as P
import qualified Tree as T

import DotPrinter

import Data.Maybe (mapMaybe)
import Data.List (group, sort)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Text.Printf
import Debug.Trace

import Control.Exception

{-
topLevelGen :: UnfoldFunc -> G X -> (DTree, G S, [S])
topLevelGen unfoldStep g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  descendGoal = dGoal lgoal Set.empty
  tree = fst $ derivationStep descendGoal lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)
  where
    -- derivationStep
    --   :: a -- Conjunction of invokes and substs.
    --   -> E.Gamma           -- Context
    --   -> E.Sigma           -- Substitution
    --   -> Set.Set DGoal     -- Already seen
    --   -> Int               -- Debug depth
    --   -> (DTree, Set.Set DGoal)
    derivationStep d@(CPD.Descend goal ancs) env subst seen depth
     -- | depth >= 4
     -- = (Prune d, seen)
      | CPD.variantCheck goal seen
      = (Leaf d subst env, seen)
      | otherwise
      = let
        newAncs = Set.insert goal ancs
        newSeen = Set.insert goal seen
      in case unfoldStep goal env subst of
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

-- topLevelU :: G X -> (DTree, G S, [S])
-- topLevelU g = let
--   (lgoal, lgamma, lnames) = goalXtoGoalS g
--   -- descendGoal = descendGoal lgoal Set.empty
--   igoal = (goal, 0)
--   tree = fst $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
--   in (tree, lgoal, lnames)


class Unfold a where
  getGoal    :: a -> DGoal
  initGoal   :: DGoal -> a
  unfoldStep :: a -> E.Gamma -> E.Sigma -> ([(E.Sigma, a)], E.Gamma)
  emptyGoal  :: a -> Bool
  mapGoal    :: a -> (DGoal -> DGoal) -> a

  derivationStep
    :: a -- Conjunction of invokes and substs.
    -> Set.Set DGoal
    -> E.Gamma           -- Context
    -> E.Sigma           -- Substitution
    -> Set.Set DGoal     -- Already seen
    -> Int               -- Debug depth
    -> (DTree, Set.Set DGoal)
  derivationStep goal ancs env subst seen depth
   -- | depth >= 4
   -- = (Prune d, seen)
    | CPD.variantCheck (getGoal goal) seen
    = (Leaf (CPD.Descend (getGoal goal) ancs) subst env, seen)
    | otherwise
    = let
      descend = CPD.Descend (getGoal goal) ancs
      newAncs = Set.insert (getGoal goal) ancs
      newSeen = Set.insert (getGoal goal) seen
    in case unfoldStep goal env subst of
       ([], _)          -> (Fail, newSeen)
       (uGoals, newEnv) -> let
           (seen', ts) = foldl (\(seen, ts) g -> (:ts) <$> evalSubTree depth newEnv newAncs seen g) (newSeen, []) uGoals
         in (Or (reverse ts) subst descend, seen')

  evalSubTree :: Int -> E.Gamma -> Set.Set DGoal -> Set.Set DGoal -> (E.Sigma, a) -> (Set.Set DGoal, DTree)
  evalSubTree depth env ancs seen (subst, goal)
    | emptyGoal goal
    = (seen, Success subst)
    | not (CPD.variantCheck (getGoal goal) seen)
    , isGen (getGoal goal) ancs
    =
      let
        newAncs  = Set.insert realGoal ancs
        absGoals = GC.abstractChild ancs (subst, realGoal, Just env)
        (seen', ts) = foldl (\(seen, ts) g -> (:ts) <$> evalGenSubTree depth newAncs seen g) (seen, []) absGoals
      in (seen', And (reverse ts) subst descend)
    | otherwise
    = let
        (tree, seen') = derivationStep goal ancs env subst seen (1 + depth)
      in (seen', tree) -- Node tree descend subst)
    where
      realGoal = getGoal goal
      descend = CPD.Descend realGoal ancs

      evalGenSubTree depth ancs seen (subst, goal, gen, env) =
        -- trace ("Goal: " ++ show goal ++ " Ancs: " ++ show ancs ++ " Gen: " ++ show gen) $
        let
          (newDepth, subtree) = if null gen then (1 + depth, tree) else (2 + depth, Gen tree gen)
          (tree, seen')       = derivationStep ((initGoal :: DGoal -> a) goal) ancs env subst seen newDepth
        in (seen', subtree)

getVariant goal nodes = let
    vs = Set.filter (CPD.isVariant goal) nodes
  in assert (length vs == 1) $ Set.elemAt 0 vs


--

goalXtoGoalS :: G X -> (G S, E.Gamma, [S])
goalXtoGoalS g = let
  (goal, _, defs)    = P.justTakeOutLets (g, [])
  gamma              = E.updateDefsInGamma E.env0 defs
  in E.preEval' gamma goal

--

isGen goal ancs = any (`CPD.embed` goal) ancs && not (Set.null ancs)

--

unfold :: G S -> E.Gamma -> (E.Gamma, G S)
unfold g@(Invoke f as) env@(p, i, d)
  | (n, fs, body) <- p f
  , length fs == length as
  = let i'            = foldl extend i (zip fs as)
        (g', env', _) = E.preEval' (p, i', d) body
    in (env', g')
  | otherwise = error "Unfolding error: different number of factual and actual arguments"
unfold g env = (env, g)

extend :: E.Iota -> (X, Ts) -> E.Iota
extend = uncurry . E.extend

--

unifyAll :: E.Sigma -> Disj (Conj (G S)) -> Disj (Conj (G S), E.Sigma)
unifyAll = mapMaybe . CPD.unifyStuff

--
-- Conjunction of DNF to DNF
--

conjOfDNFtoDNF :: Ord a => Conj (Disj (Conj a)) -> Disj (Conj a)
conjOfDNFtoDNF = {- unique . -} conjOfDNFtoDNF'


conjOfDNFtoDNF' :: Ord a => Conj (Disj (Conj a)) -> Disj (Conj a)
conjOfDNFtoDNF' [] = []
conjOfDNFtoDNF' (x:[]) = x
conjOfDNFtoDNF' (x {- Disj (Conj a) -} :xs) = concat $ addConjToDNF x <$> conjOfDNFtoDNF xs {- Disj (Conj a) -}

addConjToDNF :: Disj (Conj a) -> Conj a -> Disj (Conj a)
addConjToDNF ds c = (c ++) <$> ds

