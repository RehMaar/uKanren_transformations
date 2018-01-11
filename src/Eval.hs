{-# LANGUAGE TupleSections #-}module Eval where

import Control.Monad
import Data.List
import Data.Maybe 
import Syntax
import Stream
import Debug.Trace

-- States
type Iota  = X -> Ts
type Sigma = [(S, Ts)]
type Delta = [S]
type P     = Name -> Def
type Gamma = (P, Iota, Delta)

-- Unification
unify :: Maybe Sigma -> Ts -> Ts -> Maybe Sigma 
unify Nothing _ _ = Nothing
unify st@(Just subst) u v = 
  unify' (walk u subst) (walk v subst)  where
    unify' (V u) (V v) | u == v = Just subst
    unify' (V u) t              = occursCheck u t $ Just $ (u, v) : subst
    unify' t (V v)              = occursCheck v t $ Just $ (v, u) : subst
    unify' (C a as) (C b bs) | a == b && length as == length bs = 
      foldl (\ st (u, v) -> unify st u v) st $ zip as bs
    unify' _ _ = Nothing
    walk x@(V v) s =
      case lookup v s of
        Nothing -> x
        Just t  -> walk t s
    walk u     _ = u
    occursCheck u t s = if elem u $ fv t then error "Occurs check!" else s

---- Interpreting syntactic variables 
infix 9 <@>
(<@>) :: Iota -> Tx -> Ts
i <@> (V x)    = i x
i <@> (C c ts) = C c $ map (i<@>) ts

---- Extending variable interpretation
extend :: Iota -> X -> Ts -> Iota
extend i x ts y = if x == y then ts else i y 

---- Applying substitution
substitute :: Sigma -> Ts -> Ts
substitute s t@(V x)  = case lookup x s of Nothing -> t ; Just tx -> substitute s tx
substitute s (C m ts) = C m $ map (substitute s) ts

---- Composing substitutions
o :: Sigma -> Sigma -> Sigma
o sigma theta =
  case map fst sigma `intersect` map fst theta of
    [] -> map (\ (s, ts) -> (s, substitute sigma ts)) theta ++ sigma
    _  -> error "Non-disjoint domains in substitution composition"  

-- Pre-evaluation
pre_eval' :: Gamma -> G X -> (G S, Gamma, [S])
pre_eval' env goal = pre_eval [] env goal
 where
  pre_eval vars g@(_, i, _) (t1 :=: t2)    = (i <@> t1 :=: i <@> t2, g, vars)
  pre_eval vars g           (g1 :/\: g2)   = let (g1', g' , vars' ) = pre_eval vars  g  g1 in
                                             let (g2', g'', vars'') = pre_eval vars' g' g2 in
                                             (g1' :/\: g2', g'', vars'')
  pre_eval vars g           (g1 :\/: g2)   = let (g1', g' , vars')  = pre_eval vars  g  g1 in
                                             let (g2', g'', vars'') = pre_eval vars' g' g2 in
                                             (g1' :\/: g2', g'', vars'')
  pre_eval vars g@(p, i, d) (Fresh x g')   = pre_eval (y : vars) (p, extend i x (V y), d') g' where y : d' = d 
  pre_eval vars g@(_, i, _) (Invoke f fs)  = (Invoke f (map (i <@>) fs), g, vars)
  pre_eval vars e           (Let    def g) = let (g', e', vars') = pre_eval vars e g in
                                             (Let def g', e', vars')

post_eval' :: G X -> G X 
post_eval' = post_eval []
 where
  post_eval vars (Let (f, args, b) g) = 
    Let (f, args, let freshs = ((fvg b) \\ args) \\ vars 
                  in  foldr (\ x g  -> Fresh x g) (post_eval (vars ++ args ++ freshs) b) freshs) $ (post_eval vars g)
  post_eval vars (g1 :/\: g2) = post_eval vars g1 :/\: post_eval vars g2
  post_eval vars (g1 :\/: g2) = post_eval vars g1 :\/: post_eval vars g2
  post_eval _ g = g
   

-- Evaluation relation
eval :: Gamma -> Sigma -> G S -> Stream (Sigma, Delta)
eval     (p, i, d) s (t1 :=:  t2)  = fmap (,d) (maybeToStream $ unify (Just s) t1 t2)
eval env           s (g1 :\/: g2)  = eval env s g1 `mplus` eval env s g2
eval env@(p, i, d) s (g1 :/\: g2)  = eval env s g1 >>= (\ (s', d') -> eval (p, i, d') s' g2)
eval env@(p, i, d) s (Invoke f as) = 
  let (_, fs, g) = p f in
  let i'         = foldl (\ i' (f, a) -> extend i' f a) i $ zip fs as in
  let (g', env', _) = pre_eval' (p, i', d) g in
  eval env' s g'
eval env s (Let def g) = eval (update env def) s g 

env0 :: Gamma
env0 = ((\ _ -> error "Empty environment"), (\ i -> error $ "Empty interpretation on " ++ show i), [0..])

update :: Gamma -> Def -> Gamma
update (p, i, d) def@(name, _, _) = ((\ name' -> if name == name' then def else p name'), i, d) 

s0 :: Sigma
s0 = []

run :: G X -> Stream Sigma
run goal =
  let (goal', env', _) = pre_eval' env0 goal in
  fmap fst $ eval env' s0 goal'
