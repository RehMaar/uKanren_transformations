module RandUnfold where
    
import Syntax
import DTree

import qualified CPD
import qualified Eval as E
import qualified Purification as P
import qualified GlobalControl as GC
import qualified SeqUnfold as SU

import Data.Maybe (mapMaybe)
import Data.List
import qualified Data.Set as Set
import System.Random

import Text.Printf
import DotPrinter
import Unfold

import Debug.Trace

data RndGoal = RndGoal DGoal StdGen deriving Show

seedFromGoal dgoal = foldPoly (fst $ random (mkStdGen $ length dgoal)) $ concatMap getVarFromDGoal dgoal

foldPoly x  = foldr (\el acc -> el + acc * x) 0

getVarFromDGoal (Invoke _ as) = concatMap getVarS as
getVarFromDGoal _ = []

getVarS (C _ ts) = concatMap getVarS ts
getVarS (V t) = [t]

topLevel :: Int -> G X -> (DTree, G S, [S])
topLevel seed g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = RndGoal [lgoal] (mkStdGen seed)
  tree = fst $ derivationStep igoal Set.empty lgamma E.s0 Set.empty 0
  in (tree, lgoal, lnames)


topLevel' seed g = let
  (lgoal, lgamma, lnames) = goalXtoGoalS g
  igoal = RndGoal [lgoal] (mkStdGen seed)
  in derivationStep igoal Set.empty lgamma E.s0 Set.empty 0

instance Unfold RndGoal where
    getGoal (RndGoal dgoal _) = dgoal

    initGoal dgoal = RndGoal dgoal (mkStdGen $ seedFromGoal dgoal)

    emptyGoal (RndGoal dgoal _) = null dgoal

    mapGoal (RndGoal dgoal rng) f = RndGoal (f dgoal) rng

    unfoldStep = randUnfoldStep

randUnfoldStep :: RndGoal -> E.Gamma -> E.Sigma -> ([(E.Sigma, RndGoal)], E.Gamma)
randUnfoldStep (RndGoal dgoal rng) env subst = let
    len = length dgoal

    (idx, rng') = randomR (0, len) rng

    (_, (ls, conj, rs)) = SU.splitGoal idx dgoal

    (newEnv, uConj) = unfold conj env
    nConj = goalToDNF uConj
    unConj = unifyAll subst nConj
    us = (\(cs, subst) -> (subst, rndGoal subst ls cs rs rng')) <$> unConj

  in (us, newEnv)
  where
    rndGoal subst ls cs rs rng = let
        goal = ls ++ cs ++ rs
        len = length goal
        (_, rng') = random rng :: (Int, StdGen)
        dgoal = E.substituteConjs subst goal
      in RndGoal dgoal rng
