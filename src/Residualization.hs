module Residualization where
import qualified Data.Set as Set
import MuKanren hiding (Subst)
import Driver hiding (rename)
import Data.List (find, delete, partition, (\\))
import Data.Maybe (isJust, catMaybes, fromJust)
import Data.Foldable (foldrM)
import Debug.Trace

data Subst n t = Subst { getSubst :: n -> t , getVars :: [n] }

data Remapping n = Remapping { getRemapping :: n -> n, getRemapped :: [n] }

-- From https://github.com/nh2/haskell-ordnub
ordNub :: (Ord a) => [a] -> [a]
ordNub l = go Set.empty l
  where
    go _ [] = []
    go s (x:xs) = if x `Set.member` s then go s xs
                                      else x : go (Set.insert x s) xs

makeSubst :: (Eq n, Show n) => [(n, t)] -> Subst n t
makeSubst list =
  Subst
    (\n -> case lookup n list of
             Nothing -> error $ "element " ++  show n  ++ " not in substitution!"
             Just x  -> x)
    (map fst list)

termVars (Var v) = [v]
termVars (Pair l r) = termVars l ++ termVars r
termVars _ = []

substVars s =  ordNub $ getVars s ++ concatMap (termVars . getSubst s) (getVars s)

astVars a =
  ordNub $ go a
  where
    go (Uni l r) = termVars l ++ termVars r
    go (Conj l r) = go l ++ go r
    go (Disj l r) = go l ++ go r
    go (Zzz x) = go x
    go (Call (Fun n b) args) = map (\(Var v) -> v) args ++ go b
    go x = trace ("unexpected ast: " ++ show x) []

remap :: Ord n => Remapping n -> Subst n t -> Subst n t
remap (Remapping r rs) (Subst s vs) =
  Subst (s . r) (ordNub $ (vs \\ map r rs) ++ rs) -- map r vs ?

addRemap :: Eq n => n -> n -> Remapping n -> Remapping n
addRemap n1 n2 (Remapping r rs) =
  Remapping ((\n -> if n == n1 then n2 else r n)) (n1 : rs)

--rename :: Remapping n -> Term n a -> Term n a
rename bound (Remapping r _) (Var n) = Var (if n `elem` bound then n else r n)
rename bound r (Pair t1 t2) = Pair (rename bound r t1) (rename bound r t2)
rename _ _ a = a

residualizeSubst bound s =
  trace ("vars: " ++ show (substVars s)) $
  go (substVars s) (Remapping id []) (Remapping id [])
  where
    go [] fromNew fromOld =
      let subst' = remap fromNew s
      in
          conj (map (\n ->
                           let n' = rename bound fromOld (Var n)
                               ov = getSubst s n
                               ov' = rename bound fromOld ov
                           in  Uni n' ov'
                    )
--                           Uni (rename bound fromOld (Var n))
--                               (rename bound fromOld (getSubst subst' n)))
                    (getVars s))
    go (n:ns) fromNew fromOld =
      Fresh (\(Var x) -> go ns (addRemap x n fromNew) (addRemap n x fromOld))

getRenaming l r =
  go l r []
  where
    go l r renaming =
      case (l,r) of
       (Uni l1 l2, Uni r1 r2) -> let r' = termRename l1 r1 renaming in termRename l2 r2 r'
       (Conj l1 l2, Conj r1 r2) -> go l2 r2 $ go l1 r1 renaming
       (Disj l1 l2, Disj r1 r2) -> go l2 r2 $ go l1 r1 renaming
       (Zzz l1, Zzz r1) -> go l1 r1 renaming
       (Call (Fun ln lb) larg, Call (Fun rn rb) rarg) ->
         foldr (\(x,y) acc -> termRename x y acc) renaming (zip larg rarg)
       _ -> undefined
    termRename l r renaming =
      case (l,r) of
        (Var l', Var r') -> case lookup l' renaming of
                              Nothing -> (l',r') : renaming
                              Just r'' -> if r' == r'' then renaming else error "Renaming failed: multiple variable for one"
        (Pair l1 l2, Pair r1 r2) -> termRename l2 r2 $ termRename l1 r1 renaming
        _ -> renaming

--residualizeBackRef bound node args subst = undefined
----  go (astVars subst) (Remapping id []) (Remapping id [])
----  where


residualize tree =
  residualize' tree [] []
  where
    residualize' Fail _ _ = Nothing
    residualize' (Success (s,c)) _ bound = Just $ residualizeSubst bound $ makeSubst s
    residualize' node@(Step n subst ast t) ancs bound = residualize' t ((n,node,ast):ancs) bound
    residualize' node@(Or n subst ast l r) ancs bound =
      let ancs' = (n,node,ast):ancs
      in  Just $ disj (catMaybes [residualize' l ancs' bound, residualize' r ancs' bound])
    residualize' node@(Up n subst ast) ancs bound =
      let (_,anc,a) = fromJust (find (\(k,_,_) -> k == n) ancs)
          bound' = astVars a
          args = let renaming = getRenaming ast a
                 in  map (\x -> Var $ fromJust $ lookup x renaming) bound
          fun = Fun ("fun" ++ show n) $ fromJust $ residualize' anc ancs bound-- (residualizeBackRef bound anc args subst)
      in  Just $ call fun args

