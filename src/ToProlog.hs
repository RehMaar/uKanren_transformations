module ToProlog where

import Syntax
import Eval
import Purification

import Data.Char
import Data.List

import Bridge

--takeOutLets :: G X -> (G X, [Def])

{-------------------------------------------}
{-------------------------------------------}
{-------------------------------------------}

unifyTerms :: Term X -> Term X -> Subst -> Maybe Subst
unifyTerms x y s = unify' (walk x s) (walk y s) where
  unify' (V v1)   (V v2)   | v1 == v2                         = Just s
  unify' (V v)    t                                           = occursCheck v t $ (v, t) : s
  unify' t        (V v)                                       = occursCheck v t $ (v, t) : s
  unify' (C a as) (C b bs) | a == b && length as == length bs = foldl (\st (t1, t2) -> st >>= unifyTerms t1 t2) (Just s) $ zip as bs
  unify' _        _                                           = Nothing

  walk t@(V v) s = case lookup v s of
                   Nothing -> t
                   Just t' -> walk t' s
  walk t       _ = t

  occursCheck v t s = if elem v $ fv t then Nothing else Just s

{-------------------------------------------}
goalToDNF :: G X -> [(Subst, Funcs)]
goalToDNF g = toDNF [] g where
  toDNF s (t1 :=: t2)  = case unifyTerms t1 t2 s of
                         Nothing -> []
                         Just s' -> [(s', [])]
  toDNF s (Invoke n a) = [(s, [(n, a)])]
  toDNF s (Fresh _ g') = toDNF s g'
  toDNF s (g1 :\/: g2) = toDNF s g1 ++ toDNF s g2
  toDNF s (g1 :/\: g2) = [(s2, f1 ++ f2) | (s1, f1) <- toDNF s g1, (s2, f2) <- toDNF s1 g2]

{-------------------------------------------}
applySubst :: Subst -> Term X -> Term X
applySubst s t@(V v) = case lookup v s of
                       Nothing -> t
                       Just t' -> applySubst s t'
applySubst s (C n a) = C n $ map (applySubst s) a

{-------------------------------------------}
applyInFunc :: Subst -> Func -> Func
applyInFunc s (n, a) = (n, map (applySubst s) a)


{-------------------------------------------}
defToProlog :: Def -> Rules
defToProlog (n, a, g) = map (\(s, f) -> (applyInFunc s (n, map V a), map (applyInFunc s) f)) $ goalToDNF g

{-------------------------------------------}
goalToProlog :: G X -> [Funcs]
goalToProlog g = map (\(s, f) -> map (applyInFunc s) f) $ goalToDNF g

{-------------------------------------------}
toProlog :: G X -> (Rules, [Funcs])
toProlog g = let (g', defs) = takeOutLets g in
             let rules = concatMap defToProlog defs in
             let goals = goalToProlog g' in
             (rules, goals)

{-------------------------------------------}
{-------------------------------------------}
{-------------------------------------------}

replaceChars '\'' = "_0"
replaceChars c   = c : []

toConstrName :: String -> String
toConstrName "%"   = "cons"
toConstrName (c:s) = concatMap replaceChars $ toLower c : s

{-------------------------------------------}
toVarName :: String -> String
toVarName (c:s) = toUpper c : s

{-------------------------------------------}
toFuncName :: String -> String
toFuncName = toConstrName

{-------------------------------------------}
printTerm :: Term X -> String
printTerm (V x)    = toVarName x
printTerm (C n []) = toConstrName n
printTerm (C n a)  = toConstrName n ++ "(" ++ intercalate ", " (map printTerm a) ++ ")"

{-------------------------------------------}
printFunc :: Func -> String
printFunc (n, a) = toFuncName n ++ "(" ++ intercalate ", " (map printTerm a) ++ ")"

{-------------------------------------------}
printFuncs :: Funcs -> String
printFuncs = intercalate ", " . map printFunc

{-------------------------------------------}
printRule :: Rule -> String
printRule (h, []) = printFunc h ++ "."
printRule (h, t) = printFunc h ++ " :- " ++ printFuncs t ++ "."

{-------------------------------------------}
printRules :: Rules -> String
printRules = intercalate "\n" . map printRule

{-------------------------------------------}
printGoal :: Funcs -> String
printGoal = (++ ".") . (":- " ++) . printFuncs

{-------------------------------------------}
printGoals :: [Funcs] -> String
printGoals = intercalate "\n" . map printGoal

{-------------------------------------------}
printProg :: (Rules, [Funcs]) -> String
printProg ([], []) = ""
printProg (rs, []) = printRules rs
printProg ([], gs) = printGoals gs
printProg (rs, gs) = printRules rs ++ "\n" ++ printGoals gs

{-------------------------------------------}
{-------------------------------------------}
{-------------------------------------------}

translateAndPrint :: G X -> String
translateAndPrint = printProg . toProlog
