module DTResidualize where

import Syntax

import qualified DTree as DT
import qualified Eval as E
import qualified CpdResidualization as CR
import qualified Residualize as R
import qualified CPD

import Data.List
import Miscellaneous
import Data.Maybe (isJust, fromMaybe)
import Data.Char (toUpper)
import Control.Arrow (second)

import qualified Data.Set as Set


-- residualize :: DTree -> G X -> [S] -> (G X, [X])
residualize tree goal names = let
    xs = R.vident <$> names
  in undefined --(E.postEval' xs <$> resM tree, xs)

-- Derivation Tree
data MarkedTree = Fail
  | Success E.Sigma
  | Or [MarkedTree] E.Sigma  DT.DDescendGoal Bool
  | And [MarkedTree] E.Sigma DT.DDescendGoal Bool
  | Leaf DT.DDescendGoal E.Sigma E.Gamma
  | Gen MarkedTree E.Sigma


instance Show MarkedTree where
  show Fail                  = "Fail"
  show (Success s)           = "{Success}"
  show (Or ts _ goal isVar)  = "{Or " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (And ts _ goal isVar) = "{And " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s)             = "{Gen  " ++ show t ++ "\n}"
  show (Leaf g _ _)          = "{Leaf " ++ show g ++ "}"


data Call = Call { callName :: Name, callArgs :: [S] }
  deriving Show


makeMarkedTree :: DT.DTree -> MarkedTree
makeMarkedTree x = makeMarkedTree' x (DT.leaves x) x

makeMarkedTree' _ _ DT.Fail                  = Fail
makeMarkedTree' _ _ (DT.Success s)           = Success s
makeMarkedTree' root leaves (DT.Gen t s)     = Gen (makeMarkedTree' root leaves t) s
makeMarkedTree' root leaves (DT.Leaf df s g) = Leaf df s g
makeMarkedTree' root leaves (DT.Or ts s dg@(CPD.Descend g _))  = let
    isVar = any (CPD.isVariant g) leaves
    ts'   = makeMarkedTree' root leaves <$> ts
  in Or ts' s dg isVar
makeMarkedTree' root leaves (DT.And ts s dg@(CPD.Descend g _))  = let
    isVar = any (CPD.isVariant g) leaves
    ts'   = makeMarkedTree' root leaves <$> ts
  in And ts' s dg isVar
makeMarkedTree' root leaves _ = undefined

--
-- Generate invocation by goal.
--
genInvoke goal = Invoke name args
  where name = genCallName goal
        args = genArgs goal

--
-- Generate invocation by goal with given name.
--
genNamedInvoke :: Name -> [G S] -> G X
genNamedInvoke name = Invoke name . genArgs

genLet goal body = Let def newGoal
  where
    (name, args) = genLetSig goal
    argsX = R.toX <$> args
    argsS = show <$> argsX
    def = (name, argsS, body)
    newGoal = Invoke name argsX

--
-- Generate call signature
--
genLetSig :: Ord a => [G a] -> (Name, [Term a])
genLetSig goal = (genCallName goal, genLetArgs goal)

--
-- Generate arguments for `Let`.
--
genLetArgs :: Ord a => [G a] -> [Term a]
genLetArgs goal = let
    args = getArgs goal
    terms = Set.toList $ Set.fromList $ concatMap getVarFromTerm args
  in terms


--
-- Get all variables from the given term.
--
getVarFromTerm :: Term x -> [Term x]
getVarFromTerm v@(V _) = [v]
getVarFromTerm (C _ vs) = concatMap getVarFromTerm vs

--
--
genArgs :: [G S] -> [Term X]
genArgs = map R.toX . getArgs

--
-- Collect arguments of all invocations of the goal.
--
getArgs :: [G a] -> [Term a]
getArgs = concat . map getInvokeArgs

getInvokeArgs (Invoke _ ts) = ts
getInvokeArgs _ = []

--
-- Generate name for an invocation.
--
genCallName :: [G a] -> String
genCallName = concat . toUpperTail . fmap toName . filter isInvoke
  where toName (Invoke g _) = g

genCall :: [G S] -> Call
genCall goal = let
    name = genCallName goal
    args = getArgsForCall goal
  in Call name args

getArgsForCall goal = CR.uniqueArgs (getInvokeArgs <$> goal)

--
-- Capitalize tail of the list of strings.
--
toUpperTail :: [String] -> [String]
toUpperTail [] = []
toUpperTail (x:xs) = x : ((\(c:cs) -> toUpper c : cs) <$> xs)

--
-- Check if the goal is an invocation
--
isInvoke (Invoke _ _) = True
isInvoke _ = False

--
-- Collect all invocation from the derivation tree.
--
collectCallNames :: MarkedTree -> [(DT.DGoal, Call)]
collectCallNames (Or ts _ (CPD.Descend goal _) True)  = (goal, genCall goal) : (concatMap collectCallNames ts)
collectCallNames (And ts _ (CPD.Descend goal _) True) = (goal, genCall goal) : (concatMap collectCallNames ts)
collectCallNames (Or ts _ _ _)  = concatMap collectCallNames ts
collectCallNames (And ts _ _ _) = concatMap collectCallNames ts
collectCallNames (Gen t _) = collectCallNames t
collectCallNames _ = []


topLevel t@(DT.Or ts _ dgoal) = let
    goal = CPD.getCurr dgoal
    mt = makeMarkedTree t
    cs = collectCallNames mt

    -- defs :: (Call name args, body)
    (defs, body) = f cs [] mt
    args' = R.vident <$> getArgsForCall goal

    body' = E.postEval' args' body

    def = (genCallName goal, args', body')

    name = genCallName goal
    args = Set.toList $ Set.fromList $ genArgs goal

    goal' = Invoke name args
  -- in genLet (CPD.getCurr dgoal) body
  in Let def $ foldl1 (.) defs goal'
topLevel DT.Fail = error "Unable to residualize failed derivation"
topLevel _ = error "Who else could be root node?"

helper cs s ts subst dg foldf =
  let
    (defs, goals) = unzip $ f cs (s `union` subst) <$> ts
    goal = CPD.getCurr dg

    Call name args = findCall cs goal

    body = E.postEval' (R.vident <$> args) $ foldl1 foldf goals

    def = Let (name, R.vident <$> args, body)

    iname = genCallName goal
    iargs = genArgs goal

    goal' = CR.residualizeSubst (subst \\ s) :/\: Invoke iname iargs
  in (def : concat defs, goal')

f cs s (Or ts subst dg True) = helper cs s ts subst dg (:\/:)
f cs s (Or ts subst dg _) = let (defs, goals) = unzip $ f cs s <$> ts in (concat defs, foldl1 (:\/:) goals)

f cs s (And ts subst dg True) = helper cs s ts subst dg (:/\:)
f cs s (And ts subst dg _)   = let (defs, goals) = unzip $ f cs s <$> ts in (concat defs, foldl1 (:/\:) goals)

f cs s (Gen t subst) = second (CR.residualizeSubst (subst \\ s) :/\:) (f cs s t)

f cs s (Leaf dg [] env)    = ([], findInvoke cs (CPD.getCurr dg))
f cs s (Leaf dg subst env) = ([], CR.residualizeSubst (subst \\ s) :/\: findInvoke cs (CPD.getCurr dg))

f _ s  (Success subst) = ([], CR.residualizeSubst (subst \\ s))
f _ _ Fail = error "What to do with failed derivations?"


findCall :: [([G S], Call)] -> [G S] -> Call
findCall cs goal = snd
                   $ fromMaybe (error $ "No invocation for the leaf: " ++ show goal)
                   $ find (CPD.isVariant goal . fst) cs

findInvoke :: [([G S], Call)] -> [G S] -> G X
findInvoke cs goal = let
     name = callName $ findCall cs goal
  in genNamedInvoke name goal
