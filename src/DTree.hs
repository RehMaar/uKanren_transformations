module DTree where

import Syntax

import qualified CPD
import qualified Eval as E
import qualified Purification as P
import qualified GlobalControl as GC

import qualified Data.Set as Set

import Data.Maybe (mapMaybe)
import Text.Printf
import DotPrinter

import Debug.Trace


type Conj a = [a]
type Disj a = [a]

type DGoal = Conj (G S)

-- Conjunction of invokes and substitutions
type DDescendGoal = CPD.Descend DGoal

-- Simple initial constractor.
dGoal :: G S -> Set.Set [G S] -> DDescendGoal
dGoal goal ancs = CPD.Descend [goal] ancs

-- Logic expression to DNF
goalToDNF :: G S -> Disj (Conj (G S))
goalToDNF = CPD.normalize


-- Derivation Tree
data DTree = Fail -- Failed derivation.
  | Success E.Sigma -- Success derivation.
  | Or [DTree] E.Sigma DDescendGoal -- Node for a disjunction.
  | And [DTree] E.Sigma DDescendGoal -- Node for a conjunction.
  | Node DTree DDescendGoal E.Sigma -- Auxiliary node.
  | Leaf DDescendGoal E.Sigma E.Gamma -- Variant leaf
  | Gen DTree E.Sigma -- Generalizer
  | Prune DDescendGoal -- Debug node

--

instance DotPrinter DTree where
  labelNode t@(Or ch _ _) = addChildren t ch
  labelNode t@(And ch _ _) = addChildren t ch
  labelNode t@(Node ch _ _) = addChild t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t


instance Dot DTree where
  dot Fail = "Fail"
  dot (Success s) = "Success <BR/> " ++ (E.dotSigma s)
  dot (Node _ d s) = printf "Node <BR/> Goal: %s <BR/> Subst: %s" (dot $ CPD.getCurr d)  (E.dotSigma s)
  dot (Gen _ s) = printf "Gen <BR/> Generalizer: %s" (E.dotSigma s)
  dot (And _ s d) = printf "And <BR/> Subst: %s <BR/> Goal: %s" (E.dotSigma s) (dot $ CPD.getCurr d)
  dot (Or ts s d) = printf "Or %d <BR/> Subst: %s <BR/> Goal: %s" (length ts) (E.dotSigma s) (dot $ CPD.getCurr d)
  dot (Leaf goal s _) = printf "Leaf <BR/> Goal: %s <BR/> Subst: %s" (dot $ CPD.getCurr goal)  (E.dotSigma s)
  dot (Prune d) = printf "Prune <BR/> Goal: %s" (dot $ CPD.getCurr d) 

--

instance Show DTree where
  show Fail = "Fail"
  show (Success s) = "{Success}"
  show (Or ts _ goal) = "{Or \n [" ++ concatMap show ts ++ "]\n}"
  show (And ts _ goal) = "{And \n [" ++ concatMap show ts ++ "]\n}"
  show (Node t d s) = "{Node [" ++ show t ++ "]\n}"
  show (Gen t s) = "{Gen  " ++ show t ++ "\n}"
  show (Leaf g _ _) = "{Leaf " ++ show g ++ "}"
  show (Prune d) = "{Prune " ++ show d ++ "}"

--

-- TODO: useless?

data Resultant = Resultant {
    resSubst :: E.Sigma
  , resGoal  :: DGoal
  , resGamma :: E.Gamma
  }

instance Show Resultant where
  show (Resultant subst goal _) = "Resulant { subst: <" ++ show subst ++ ">, goal: <" ++ show goal ++ ">}"

resultants :: DTree -> [Resultant]
resultants Fail = []
resultants (Success s) = [Resultant s [] E.env0]
resultants (Leaf goal subst gamma) = [Resultant subst (CPD.getCurr goal) gamma]
resultants (Node t _ _) = resultants t
resultants (And ts _ _) = concat (resultants <$> ts)
resultants (Or ts _ _) = concat (resultants <$> ts)
resultants (Gen t _) = resultants t
resultants _ = error "The tree has bad leafs (Prune...)"

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

--
-- DTree to a set of goals of its nodes
--
treeGoals :: DTree -> Set.Set DGoal
treeGoals (Or ts _ goal) = Set.insert (CPD.getCurr goal) (Set.unions (treeGoals <$> ts))
treeGoals (And ts _ goal) = Set.insert (CPD.getCurr goal) (Set.unions (treeGoals <$> ts))
treeGoals (Node t goal _) = Set.insert (CPD.getCurr goal) (treeGoals t)
treeGoals (Leaf goal _ _) = Set.singleton (CPD.getCurr goal)
treeGoals (Gen t _) = treeGoals t
treeGoals (Prune goal) = Set.singleton (CPD.getCurr goal)
treeGoals _ = Set.empty

--
-- Evaluate tree's metrics.
--

--                    (leafs, pruned leafs)
countLeafs :: DTree -> (Int, Int)
countLeafs (Or ts _ _) = foldl (\(n1, m1) (n2, m2) -> (n1 + n2, m1 + m2)) (0, 0) (countLeafs <$> ts)
countLeafs (And ts _ _) = foldl (\(n1, m1) (n2, m2) -> (n1 + n2, m1 + m2)) (0, 0) (countLeafs <$> ts)
countLeafs (Node t _ _) = countLeafs t
countLeafs (Gen t _) = countLeafs t
countLeafs (Prune _) = (1, 1)
countLeafs _ = (1, 0)

countDepth :: DTree -> Int
countDepth (Or ts _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (And ts _ _) = 1 + foldl max 0 (countDepth <$> ts)
countDepth (Node t _ _) = 1 + countDepth t
countDepth (Gen t _) = 1 + countDepth t
countDepth _ = 1

countNodes :: DTree -> Int
countNodes (Or ts _ _) = 1 + sum (countNodes <$> ts)
countNodes (And ts _ _) = 1 + sum (countNodes <$> ts)
countNodes (Node t _ _) = 1 + countNodes t
countNodes (Gen t _) = 1 + countNodes t
countNodes _ = 1
