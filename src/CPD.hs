{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections, InstanceSigs #-}

module CPD where

import           Prelude                           hiding ( lookup )
import           Syntax
import qualified Eval                          as E
import           Text.Printf
import           Control.Monad
import           Data.Maybe
import           Data.List                                ( find
                                                          , nub
                                                          , intersect
                                                          , partition
                                                          , subsequences
                                                          , intercalate
                                                          )
import           Purification
import qualified Data.Map.Strict               as Map
import           Debug.Trace
import qualified Driving                       as D
import qualified Data.Set                      as Set
import           Control.Arrow (second)
import           Control.Applicative ((<|>))


--
-- Let the goal
--  G' = <- (A_1 && .. A_{i - 1} && B_1 && ..  B_k && A_{i + 1} && .. A_n) \Theta
-- be derivied via an SLD-resolution step from the goal
--  G = <- (A_1 && .. A_i && .. A_n),
-- and the clause
--  H = <- B_1 && .. B_k,
-- with selected atom A_i.
--
-- Atoms B_1 \Theta, .. B_k \Theta in G' _descend_ from A_i in G
-- as well as that A_j \Theta in G', for j != i, _descends_ from A_j in G.
--
data Descend a = Descend { getCurr :: a, getAncs :: Set a }
  deriving (Eq)

instance (Show a) => Show (Descend a) where
  show (Descend curr ancs) = printf "%s <- %s" (show curr) (show $ Set.toList ancs)

type DescendGoal = Descend (G S)

data SldTree = Fail
             | Success E.Sigma
             | Or [SldTree] E.Sigma
             | Conj SldTree [DescendGoal] E.Sigma
             | Leaf [DescendGoal] E.Sigma E.Gamma

instance Show SldTree where
    show Fail = "Fail"
    show (Success s) = "Success " ++ show s
    show (Or ss s) = "Or {" ++ show ss ++ " " ++ show s ++ "}"
    show (Conj sld dg s) = "Conj {" ++ show sld ++ " " ++ show dg ++ " " ++ show s ++ "}"
    show (Leaf dgs d gm) = "Leaf {" ++ show dgs ++ " " ++ show d ++ " " ++ showG gm ++ "}"
      where showG (p, i, d) = "Gamma"

select :: [DescendGoal] -> Maybe DescendGoal
select = find (\x -> isSelectable embed (getCurr x) (getAncs x))

selecter :: [DescendGoal] -> ([DescendGoal], [DescendGoal])
selecter gs = span (\x -> not $ isSelectable embed (getCurr x) (getAncs x)) gs

-- TODO reconsider hardcoded list of basic function names
isSelectable :: Show a => (G a -> G a -> Bool) -> G a -> Set (G a) -> Bool
isSelectable _ _ ancs | Set.null ancs = True
isSelectable emb goal ancs = (not $ any (`emb` goal) ancs) && fineToUnfold goal
 where
  fineToUnfold (Invoke f _) = f `notElem` basics
  fineToUnfold _            = False
  basics = []

selectNext :: [DescendGoal] -> Maybe ([DescendGoal], DescendGoal, [DescendGoal])
selectNext gs =
  let (ls, rs) = selecter gs
  in if null rs then Nothing else Just (ls, head rs, tail rs)

sldResolution :: [G S] -> E.Gamma -> E.Sigma -> SldTree
sldResolution goal gamma subst = sldResolutionStep
  (map (\x -> Descend x Set.empty) goal)
  gamma
  subst
  Set.empty
  True

substituteDescend s =
  map $ \(Descend g ancs) -> Descend (E.substituteGoal s g) ancs

extend :: E.Iota -> (X, Ts) -> E.Iota
extend = uncurry . E.extend

unfold :: G S -> E.Gamma -> (G S, E.Gamma)
unfold g@(Invoke f as) env@(p, i, d)
  | (_, fs, body) <- p f
  , length fs == length as
  = let i'            = foldl extend i (zip fs as)
        (g', env', _) = E.preEval' (p, i', d) body
    in  (g', env')
  | otherwise
  = error "Unfolding error: different number of factual and actual arguments"
unfold g env = (g, env)


sldResolutionStep
  :: [DescendGoal] -> E.Gamma -> E.Sigma -> Set [G S] -> Bool -> SldTree
sldResolutionStep gs env@(p, i, d@(temp : _)) s seen isFirstTime
  | variantCheck (map getCurr gs) seen
  = Leaf gs s env
  | Just (ls, Descend g ancs, rs) <- selectNext gs
  = let (g', env') = unfold g env in go g' env' ls rs g ancs isFirstTime
  | otherwise
  = Leaf gs s env
 where
  go g' env' ls rs g ancs isFirstTime
    = let
        normalized = normalize g'
        unified    = mapMaybe (unifyStuff s) normalized
        newSeen    = Set.insert (map getCurr gs) seen
        newList xs = (ls ++ map (\x -> Descend x (Set.insert g ancs)) xs ++ rs)
        addDescends xs s = substituteDescend s (newList xs)
      in
        case unified of
          [] -> Fail
          ns | length ns == 1 || isFirstTime -> Or (step <$> ns) s
           where
            step (xs, s')
              | null xs && null rs
              = Success s'
              | otherwise
              = let newDescends = addDescends xs s'
                    cond = isFirstTime && length ns == 1
                    tree = sldResolutionStep newDescends env' s' newSeen cond
                in  Conj tree newDescends s'
          ns | not (null rs) -> maybe
            (Leaf gs s env)
            (\(ls', Descend nextAtom nextAtomsAncs, rs') ->
              let (g'', env'') = unfold nextAtom env
              in  go g''
                     env''
                     (ls ++ (Descend g ancs : ls'))
                     rs'
                     nextAtom
                     nextAtomsAncs
                     False
            )
            (selectNext rs)
          ns -> Leaf gs s env

--
-- Нормализация выражений: переводит в КНФ, как я поняла.
--
normalize :: G S -> [[G S]] -- disjunction of conjunctions of calls and unifications
normalize (  f      :\/: g) = normalize f ++ normalize g
normalize (  f      :/\: g) = (++) <$> normalize f <*> normalize g
normalize g@(Invoke _    _) = [[g]]
normalize g@(_      :=:  _) = [[g]]
normalize _                 = error "Unexpected goal type in normalization"

unifyStuff :: E.Sigma -> [G S] -> Maybe ([G S], E.Sigma)
unifyStuff state gs = go gs state []
 where
  go []                      state conjs = Just (reverse conjs, state)
  go (g@(Invoke _   _) : gs) state conjs = go gs state (g : conjs)
  go ((  t      :=: u) : gs) state conjs = do
    s <- E.unify (Just state) t u
    go gs s conjs

bodies :: SldTree -> [[G S]]
bodies = leaves

leaves :: SldTree -> [[G S]]
leaves (Or disjs _ ) = concatMap leaves disjs
leaves (Conj ch _ _) = leaves ch
leaves (Leaf ds _ _) = [map getCurr ds]
leaves _             = []

resultants :: SldTree -> [(E.Sigma, [G S], Maybe E.Gamma)]
resultants (Success s    ) = [(s, [], Nothing)]
resultants (Or disjs _   ) = concatMap resultants disjs
resultants (Conj ch _ _  ) = resultants ch
resultants (Leaf ds s env) = [(s, map getCurr ds, Just env)]
resultants Fail            = []

topLevel :: G X -> SldTree
topLevel goal =
  let (goal', _, defs)           = justTakeOutLets (goal, [])
      gamma                      = E.updateDefsInGamma E.env0 defs
      (logicGoal, gamma', names) = E.preEval' gamma goal'
  in  sldResolutionStep [Descend logicGoal Set.empty] gamma' E.s0 Set.empty True

mcs :: (Eq a, Show a) => [G a] -> [[G a]]
mcs []  = []
mcs [g] = [[g]]
mcs (g : gs) =
  let (con, non, _) = foldl
        (\(con, non, vs) x -> if null (vs `intersect` vars x)
          then (con, x : non, vs)
          else (x : con, non, nub $ vars x ++ vs)
        )
        ([g], [], vars g)
        gs
  in  reverse con : mcs (reverse non)

vars :: (Eq a, Show a) => G a -> [Term a]
vars (Invoke _ args) = nub $ concatMap getVars args
 where
  getVars (V v   ) = [V v]
  getVars (C _ ts) = concatMap getVars ts
vars _ = []

msgExists gs hs | length gs == length hs =
  all
      (\x -> case x of
        (Invoke f _, Invoke g _) -> f == g
        _                        -> False
      )
    $ zip gs hs
msgExists _ _ = False

-- ordered subconjunctions of the proper length
subconjs :: [a] -> Int -> [[a]]
subconjs gs n = filter (\x -> n == length x) $ subsequences gs

-- works for ordered subconjunctions
complementSubconjs
  :: (Instance a (Term a), Eq a, Ord a, Show a) => [G a] -> [G a] -> [G a]
complementSubconjs xs ys =
  -- trace (printf "\nComplementing\n%s\nby\n%s\n" (show xs) (show ys)) $
  go xs ys
 where
  go [] xs                              = xs
  go (x : xs) (y : ys) | x == y         = go xs ys
  go (x : xs) (y : ys) | isRenaming x y = go xs ys
  go (x : xs) (y : ys) | isInst x y     = go xs ys
  -- go (x:xs) (y:ys) | isInst y x     = go xs ys
  go xs (y : ys)                        = y : go xs ys
  go xs ys = error (printf "complementing %s by %s" (show xs) (show ys))

-- TODO : implemented literally according to the definition, may be inefficient. Look at the graph approach again.
-- elem q is minimally general of Q iff there doesn't exist another elem q' \in Q which is a strict instance (q' = q \Theta)
-- isStrictInst q t iff q = t \Theta
--
minimallyGeneral :: (Show a, Ord a) => [[G a]] -> [G a]

minimallyGeneral xs =
  -- trace (printf "minimallyGeneral %s" $ show xs) $
    maybe (error "Empty list of best matching conjunctions") id $
    find (\x -> all (not . isStrictInst x) xs) xs <|>
    listToMaybe (reverse xs)

--
-- **Definition**
--
-- Best matching conjunction
--
-- Let Q be a conj and L be a set of conjs. A bmc for Q in L
-- is a minimally general element of the set
--   bmc(Q, L) = { msg(Q, Q') | Q' in L and msg(Q, Q') exists }
--
--
bmc :: E.Delta -> [G S] -> [[G S]] -> ([[G S]], E.Delta)
bmc d q [] = ([], d)
bmc d q (q' : qCurly)
  | msgExists q q' =
    --trace "bmc" $
    let (generalized, _, gen, delta) = D.generalizeGoals d q q'
    in
     --trace (printf "Generalizing\nq: %s\nq':  %s\nRes: %s\nGen: %s\ndelta: %s\n"
     --(show q) (show q') (show generalized) (show gen) (show $ head d) ) $
     let   (gss, delta') = bmc delta q qCurly
     in (generalized : gss, delta')
bmc d q (q' : qCurly) = trace "why msg does not exist?!" $ bmc d q qCurly
-- bmc d q qCurly = [(\(x,_,_,_) -> x) $ D.generalizeGoals d q q' | q' <- qCurly, msgExists q q']

--
-- **Definition**
--
-- Let Q = A_1 && .. && A_n,
--     Q' -- conjunction such that Q <| Q'.
-- Let L be the set of all ordered subconj Q'' of Q'
-- consiting of n atoms such that Q <| Q''.
--
-- Then split_Q(Q') us the pair (B, R) where
-- B = bmc(Q, L)
-- and
-- R is the ordered subconj of Q' such that Q' =_r B && R
--
split :: E.Delta -> [G S] -> [G S] -> (([G S], [G S]), E.Delta)
split d q q' = -- q <= q'
  --trace (printf "splitting\nq:  %s\nq': %s\n" (show q) (show q')) $
  let n = length q in 
  -- let qCurly = filterTrace (\q'' -> q `embed` q'') $ subconjs q' n in
   --trace (intercalate "\n" $ map show $ map (\q'' -> (q, q'', zipWith embed q q'')) $ subconjs q' n) $
  let qCurly = filter (and . zipWith embed q) $ subconjs q' n in
  -- trace (printf "\nQcurly: %s" (show qCurly)) $
  let (bestMC, delta) = bmc d q qCurly in 
   --trace (printf "\nBMC: %s" $ show bestMC ) $
  let b = minimallyGeneral bestMC in 
   --trace (printf "\nQcurly: %s\nBestMC: %s\nB:  %s\nQ': %s\nQ:  %s\n" (show qCurly) (show bestMC) (show b) (show q') (show q)) $
  ((b, if length q' > n then complementSubconjs b q' else []) , delta)


class (Eq b) => Instance a b | b -> a where
  inst :: b -> b -> Map a (Term a) -> Maybe (Map a (Term a))

  isInst :: b -> b -> Bool
  isInst x y = isJust $ inst x y Map.empty

  isStrictInst :: b -> b -> Bool
  isStrictInst x y = isInst x y && not (isInst y x)

  isVariant :: b -> b -> Bool
  isVariant x y = x == y || isInst x y && isInst y x

  isRenaming :: b -> b -> Bool
  isRenaming x y =
    x == y || maybe False (all (\e -> case e of V _ -> True; _ -> False ) . Map.elems) (inst x y Map.empty)

  instanceCheck :: b -> [b] -> Bool
  instanceCheck g = any (isInst g)

  variantCheck :: Foldable t => b -> t b -> Bool
  variantCheck g = any (isVariant g)

instance (Eq a, Ord a) => Instance a (Term a) where
  inst (V v) u subst =
    case Map.lookup v subst of
      Just w | u == w -> Just subst
      Just w -> Nothing
      Nothing -> Just $ Map.insert v u subst
  inst (C n as) (C m bs) subst
    | length as == length bs =
      foldl (\s (a, b) -> s >>= inst a b) (Just subst) (zip as bs)
  inst _ _ _ = Nothing

instance (Eq a, Ord a) => Instance a (G a) where
  inst (Invoke f as) (Invoke g bs) subst
    | f == g
    , length as == length bs =
      foldl (\s (a, b) -> s >>= inst a b) (Just subst) (zip as bs)
  inst _ _ _ = Nothing

instance (Eq a, Ord a) => Instance a [G a] where
  inst as bs subst
    | length as == length bs =
      foldl (\s (a, b) -> s >>= inst a b) (Just subst) (zip as bs)
  inst _ _ _ = Nothing

class AlwaysEmbeddable a where
  isAlwaysEmbeddable :: a -> Bool

instance AlwaysEmbeddable (G a) where
  isAlwaysEmbeddable (Invoke f _) = f `elem` [] --[] -- ["leo", "gto"]
  isAlwaysEmbeddable _ = False

instance AlwaysEmbeddable [G a] where
  isAlwaysEmbeddable = null

instance AlwaysEmbeddable (Term a) where
  isAlwaysEmbeddable = const True

--
-- Homeomorphic embedding
--
-- Let Q = A_1 & .. A_n and q' be conjs.
-- Q is embedded in Q' iff Q' !< Q and
-- exists ordered subconj A'_1 & .. A'_n of Q' such that
-- forall i. A_i <| A_'
--
-- So what is `couple` and `diving`?
class AlwaysEmbeddable a => Homeo a where
  couple :: a -> a -> Bool
  diving :: a -> a -> Bool
  homeo  :: a -> a -> Bool
  homeo x y = couple x y || diving x y

instance Homeo (Term a) where
  couple (C n as) (C m bs) | n == m && length as == length bs =
    all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving v (C _ as) = any (homeo v) as
  diving _ _ = False

  homeo (V _) (V _) = True
  homeo x y = couple x y || diving x y

instance Show a => Homeo (G a) where
  couple goal@(Invoke f as) (Invoke g bs) | isAlwaysEmbeddable goal || f == g && length as == length bs =
    all (uncurry homeo) $ zip as bs
  couple _ _ = False

  diving _ _ = False

instance Show a => Homeo [G a] where
  couple = undefined
  diving = undefined

  homeo gs hs =
    any (all (uncurry homeo) . zip gs) (subconjs hs (length gs))
  -- couple gs hs | length gs == length hs =
  --   all (uncurry homeo) $ zip gs hs
  -- couple _ _ = False
  --
  -- diving gs (h:hs) = homeo gs hs
  -- diving _ _ = False

-- Strict homeomorphic embedding. Explore: use a variants check instead of the instance check.
class (Homeo b, Instance a b, Eq b, Show a) => Embed a b | b -> a where
  embed :: b -> b -> Bool
  embed g h = isAlwaysEmbeddable g || g == h || homeo g h && not (isStrictInst h g)

instance (Ord a, Eq a, Show a) => Embed a (G a)
instance (Ord a, Eq a, Show a) => Embed a [G a] where
  embed gs hs =
    let subs = subconjs hs (length gs) in
    any (and . zipWith embed gs) subs
