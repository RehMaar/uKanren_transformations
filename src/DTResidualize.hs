module DTResidualize where

import Syntax
import DotPrinter

import qualified DTree as DT
import qualified Eval as E
import qualified CpdResidualization as CR
import qualified Residualize as R
import qualified CPD

import Data.List
import Miscellaneous
import Data.Maybe (isJust, fromMaybe, mapMaybe)
import Data.Char (toUpper)
import Control.Arrow (first, second)

import qualified Data.Set as Set

import Debug.Trace
import Text.Printf


--
-- Marked Derivation Tree
--
-- `Bool` flag for `And` and `Or` constructors set to True
-- if some `Leaf` is a variant of one of these nodes.
--
data MarkedTree = Fail
  | Success E.Sigma
  | Or  [MarkedTree] E.Sigma DT.DGoal Bool
  | And [MarkedTree] E.Sigma DT.DGoal Bool
  | Leaf DT.DGoal E.Sigma
  | Gen MarkedTree E.Sigma

--
-- Debug output.
--
instance Show MarkedTree where
  show Fail                  = "Fail"
  show (Success s)           = "{Success}"
  show (Or ts _ goal isVar)  = "{Or " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (And ts _ goal isVar) = "{And " ++ show isVar ++ "\n [" ++ concatMap show ts ++ "]\n}"
  show (Gen t s)             = "{Gen  " ++ show t ++ "\n}"
  show (Leaf g _)          = "{Leaf " ++ show g ++ "}"


--
--
--
instance DotPrinter MarkedTree where
  labelNode t@(Or ch _ _ _) = addChildren t ch
  labelNode t@(And ch _ _ _) = addChildren t ch
  labelNode t@(Gen ch _) = addChild t ch
  labelNode t = addLeaf t

--
-- Change to downscale the tree.
--
-- dotSigma _ = ""
dotSigma = E.dotSigma

instance Dot MarkedTree where
  dot Fail = "Fail"
  dot (Success s)   = "Success <BR/> " ++ (dotSigma s)
  dot (Gen _ s)     = "Gen <BR/> Generalizer: " ++ dotSigma s
  dot (And _ s d f) = printf "And %s <BR/> Subst: %s <BR/> Goal: %s" (showF f) (dotSigma s) (dot d)
  dot (Or ts s d f) = printf "Or %s <BR/> Subst: %s <BR/> Goal: %s" (showF f) (dotSigma s) (dot d)
  dot (Leaf goal s) = printf "Leaf <BR/> Goal: %s <BR/> Subst: %s" (dot goal)  (dotSigma s)

showF True = "T"
showF _ = ""

--
--
--
data Call = Call { callName :: Name, callArgs :: [S], callOrigArgs :: [S] }
  deriving Show


makeMarkedTree :: DT.DTree
               -> MarkedTree
makeMarkedTree x = makeMarkedTree' x (DT.leaves x) x


makeMarkedTree' :: DT.DTree      -- Root of the tree
                -> [DT.DGoal]    -- Leaves of the tree (Only `Leaf` nodes)
                -> DT.DTree      -- Currently traversed tree.
                -> MarkedTree
makeMarkedTree' _ _ DT.Fail                  = Fail
makeMarkedTree' _ _ (DT.Success s)           = Success s
makeMarkedTree' root leaves (DT.Gen t s)     = Gen (makeMarkedTree' root leaves t) s
makeMarkedTree' root leaves (DT.Leaf df s g) = Leaf (CPD.getCurr df) s
makeMarkedTree' root leaves (DT.Or ts s dg@(CPD.Descend g _))  = let
    isVar = any (CPD.isVariant g) leaves
    ts'   = makeMarkedTree' root leaves <$> ts
  in Or ts' s g isVar
makeMarkedTree' root leaves (DT.And ts s dg@(CPD.Descend g _))  = let
    isVar = any (CPD.isVariant g) leaves
    ts'   = makeMarkedTree' root leaves <$> ts
  in And ts' s g isVar
makeMarkedTree' root leaves _ = undefined

--
-- Get all variables from the given term.
--
getVarFromTerm :: Term x -> [Term x]
getVarFromTerm v@(V _) = [v]
getVarFromTerm (C _ vs) = concatMap getVarFromTerm vs

getSFromTerm :: Term S -> [S]
getSFromTerm (V v)    = [v]
getSFromTerm (C _ vs) = concatMap getSFromTerm vs

argsToS :: [Term S] -> [S]
argsToS = concatMap getSFromTerm

--
-- Generate name for an invocation.
--
genCallName :: [G a] -> String
genCallName = concat . toUpperTail . fmap toName . filter isInvoke
  where toName (Invoke g _) = g

--
-- Return all arguments of the conj's invokes.
--
getArgs :: [G a] -> [Term a]
getArgs = concatMap getInvokeArgs . filter isInvoke


genCall :: [G S] -> Call
genCall = genCall' []

genCall' cs goal = let
    nameSet = Set.fromList ((\(_, Call name _ _) -> name) <$> cs)
    name = CR.generateFreshName (genCallName goal) nameSet
    args = argsToS $ genArgs goal
    orig = argsToS $ getArgs goal
  in Call name args orig

genArgs :: Eq a => [G a] -> [Term a]
genArgs = nub . genArgs'

genArgs' = concatMap getVarFromTerm . getArgs


-- genArgsByOrig :: [S] -> [S] -> [G S] -> [Term S]
genArgsByOrig args orig goalArgs
  | Just ms <- mapTwoLists orig goalArgs
  = (\a -> fromMaybe (error $ "Couldn't find argument " ++ show a ++ " in original argument list") $ lookup a ms) <$> args
  | otherwise
  = error $ "\nUnable to match goal args and invoke args: Args = " ++ show args
             ++ " Orig = " ++ show orig
             ++ " GoalArgs = " ++ show goalArgs ++ "\n"

genInvokeByCall (Call name args orig) goal = let
     goalArgs = genArgs' goal
     invArgs = map R.toX $ genArgsByOrig args orig goalArgs
     in Invoke name invArgs

--
-- Generate call signature
--
genLetSig :: Ord a => [G a] -> (Name, [Term a])
genLetSig goal = (genCallName goal, genArgs goal)

--
-- Get arguments from the given invoke.
--
getInvokeArgs (Invoke _ ts) = ts
getInvokeArgs _ = []

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
collectCallNames cs (And ts _ goal True) = let c = (goal, genCall' cs goal) in foldl collectCallNames (c:cs) ts
collectCallNames cs (Or  ts _ goal True) = let c = (goal, genCall' cs goal) in foldl collectCallNames (c:cs) ts
collectCallNames cs (Or  ts _ _ _) = foldl collectCallNames cs ts
collectCallNames cs (And ts _ _ _) = foldl collectCallNames cs ts
collectCallNames cs (Gen t _) = collectCallNames cs t
collectCallNames cs _ = cs

topLevel t = topLevel' $ cutFailedDerivations $ makeMarkedTree t

topLevel' Fail = error "How to residualize failed derivation?"
topLevel' mt = let
  cs = collectCallNames [] mt
  (defs, body) = res cs [] mt
  in foldDefs defs body
{-
    -- Mark derivation tree.
    -- Kludge: root Or node must be unmarked
    mt = (\root -> case root of { (Or ts s goal f) -> Or ts s goal False; _ -> root}) $ makeMarkedTree t
    -- Generate function signature for upper function.
    c@(Call name args argsOrig) = genCall goal
    -- Collect all signatures from the marked tree.
    cs = collectCallNames [(goal, c)] mt


    -- Residualizate the tree
    -- defs -- collected function definitions
    -- body -- Let (name, args, def) body
    (defs, body) = res cs [] mt

    args' = R.vident <$> args
    args'' = map R.toX $ genArgsByOrig args argsOrig $ genArgs' goal

    -- post-eval for freshes.
    body' = E.postEval' args' body
    -- definition of the topLevel call.
    def = (name, args', body')

    -- name = genCallName goal
    goal' = Invoke name args''

  -- in genLet (CPD.getCurr dgoal) body
  in -- trace ("\nInv: " ++ show goal' ++ " Args': " ++ show args' ++ " Call: " ++ show c ++ "\n") $
    Let def $ foldDefs defs goal'
-}

foldDefs [] g = g
foldDefs xs g = foldl1 (.) xs g

foldGoals _ [] = error "Empty goals!"
foldGoals _ [g] = g
foldGoals f gs  = foldl1 f gs

res = f
  where
    --
    -- Common function to handle nodes that define a new subroutine.
    --
    helper cs s ts subst goal foldf = let
        (defs, goals) = unzip $ f cs (s `union` subst) <$> ts
        --
        -- cs -- list of collected function names and args.
        --
        Call name args argsOrig = findCall cs goal

        argsS = R.vident <$> args
        --
        -- Fold all residualized subterms.
        --
        -- Call `postEval'` to add `fresh`.
        body = E.postEval' argsS $ foldGoals foldf goals

        -- Create definition (without adding `goal` for later composition)
        def = Let (name, argsS, body)

        -- Args for a call
        goalArgs = genArgs' goal

        iargs = map R.toX $ genArgsByOrig args argsOrig goalArgs

        diff  = subst \\ s
        goal' = let g = Invoke name iargs in if null diff then g else CR.residualizeSubst diff :/\: g
      in (def : concat defs, goal')

    --
    -- The only nodes which can define new calls are `Or` and `And`.
    --
    -- If last field is True, the node defines a call.
    f cs s (Or ts subst dg True) = helper cs s ts subst dg (:\/:)
    -- Otherwise do a disjunction of residualized subtrees.
    f cs s (Or ts subst dg _) = let (defs, goals) = unzip $ f cs s <$> ts in (concat defs, foldGoals (:\/:) goals)
    -- For `And` do the same.
    f cs s (And ts subst dg True) = helper cs s ts subst dg (:/\:)
    f cs s (And ts subst dg _) = let (defs, goals) = unzip $ f cs s <$> ts in (concat defs, foldGoals (:/\:) goals)

    -- For `Gen` do conj of generalizer and the residualized goal.
    f cs s (Gen t subst) = second (CR.residualizeSubst (subst \\ s) :/\:) (f cs s t)

    --
    -- For `Leaf` find function' call from the given list of calls.
    f cs s (Leaf dg [])    = ([], findInvoke cs  dg)
    -- And is subst isn't empty, return conjunction of gaol with it.
    f cs s (Leaf dg subst) = ([], CR.residualizeSubst (subst \\ s) :/\: findInvoke cs dg)

    -- For `Success` just return substitution.
    -- As no definitions possible, return [] as `defs`.
    f _ s  (Success subst) = ([], CR.residualizeSubst (subst \\ s))

    f _ _ Fail = error "What to do with failed derivations? Cut them off?"



findCall cs goal = snd
  $ fromMaybe (error $ "No invocation for the leaf: " ++ show goal)
  $ find (CPD.isVariant goal . fst) cs

--
-- Find a call and generate `Invoke`.
--
findInvoke :: [([G S], Call)] -> [G S] -> G X
findInvoke cs goal = genInvokeByCall (findCall cs goal) goal

--
--
-- Build a mapping from the first list to the second one and
-- check its consistency.
--
mapTwoLists :: (Eq a, Eq b) => [a] -> [b] -> Maybe [(a, b)]
mapTwoLists l1 l2
  | length l1 == length l2
  = checkMap $ zip l1 l2
  | otherwise
  = Nothing
  where
    checkMap [] = Just []
    checkMap ms = foldr checkMap' (Just []) ms

    checkMap' m@(m1, m2) (Just as)
      | Just x <- lookup m1 as
      , x /= m2
      = Nothing
      | otherwise = Just (m:as)
    checkMap' _ _ = Nothing

--

-- За один шаг. Предполагаем, что всё строилось слева направо. В процессе прохода собираем список плохих помеченных `Or`
-- и каждый лист, который вариант плохого `Or`, обрабатывать как Fail.
--
cutFailedDerivations = fromMaybe Fail . fst . cfd Set.empty 
  where
    cfd :: Set.Set DT.DGoal    -- *Плохие* узлы, которые привели только к Fail узлам.
        -> MarkedTree -- Текущий узел
        -> (Maybe MarkedTree, Set.Set DT.DGoal) -- Новое поддерево и обновлённых список *плохих* узлов
    cfd gs Fail = (Nothing, gs)
    cfd gs t@(Success _) = (Just t, gs)
    cfd gs t@(Leaf goal _)
      | Just _ <- find (CPD.isVariant goal) gs
      = (Nothing, gs)
      | otherwise
      = (Just t, gs)
    cfd gs (Gen t s) = first (flip Gen s <$>) (cfd gs t)
    cfd gs (Or  ts f1 g True) = cfdCommon1 Or gs ts f1 g
    cfd gs (And ts f1 g True) = cfdCommon1 And gs ts f1 g
    cfd gs (Or  ts f1 f2 f3) = cfdCommon2 Or  gs ts f1 f2 f3
    cfd gs (And ts f1 f2 f3) = cfdCommon2 And gs ts f1 f2 f3

    cfdCommon1 ctr gs ts f1 g = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = mapMaybe id mts
      in if null ts' then (Nothing, Set.insert g gs') else (Just $ ctr ts' f1 g True, gs')

    cfdCommon2 ctr gs ts f1 f2 f3 = let
        (mts, gs') = foldl foldCfd ([], gs) ts
        ts' = mapMaybe id mts
      in if null ts' then (Nothing, gs') else (Just $ ctr ts' f1 f2 f3, gs')


    foldCfd (ts, gs) t = first (:ts) (cfd gs t)
