{-# LANGUAGE TupleSections #-}

module GlobalControl where
    
import qualified CPD
import           Syntax
import           Prelude                           hiding ( sequence )
import           Data.Maybe                               ( isJust )
import           Data.List                                ( find
                                                          , partition
                                                          , inits
                                                          )
import qualified Eval                          as E
import qualified Driving                       as D
import           Purification
import           Text.Printf
import           Debug.Trace
import qualified Data.Set                      as Set
import qualified Tree                          as T
import           Miscellaneous
import           DotPrinter
import           SldTreePrinter
import           Control.Arrow (first)
import qualified CharacteristicAtoms           as CA

type Descend = CPD.Descend

data GlobalTree = Leaf  (Descend [G S]) T.Generalizer E.Sigma
                | Node  (Descend [G S]) T.Generalizer CPD.SldTree [GlobalTree]
                | Prune (Descend [G S]) E.Sigma

instance Show GlobalTree where
  show (Leaf d  _ s)    = "\nLeaf ("++ show s ++ "): {" ++ show d ++ "} "
  show (Node d  s _ gt) = "\nNode ("++ show s ++  "): {" ++ show d ++ show gt ++ "}"
  show (Prune d  _ )    = "\nPrune: {" ++ show d ++ "} "

sizeGT :: GlobalTree -> Integer
sizeGT (Node _ _ _ ts) = 1 + sum (sizeGT <$> ts)
sizeGT _ = 1

depthGT :: GlobalTree -> Integer
depthGT (Node _ _ _ ts) = 1 + maximum (depthGT <$> ts)
depthGT _ = 1

sequence :: Descend a -> Set a
sequence = CPD.getAncs

branch :: GlobalTree -> Set [G S]
branch (Leaf d _ _  ) = sequence d
branch (Node d _ _ _) = sequence d

leaves :: GlobalTree -> Set [G S]
leaves (Leaf d _ _) = Set.singleton $ CPD.getCurr d
leaves (Node _ _ _ ch) =
  let sets = map leaves ch in foldr Set.union Set.empty sets

-- initial splitting into maximally connected suconjunctions, may be something else
part :: [G S] -> [[G S]]
part = CPD.mcs

whistle :: Descend [G S] -> [G S] -> Maybe [G S]
whistle descend m =
  let res = find (\b -> CPD.embed b m && not (CPD.isVariant b m))
                 (sequence descend)
  in  --trace (printf "Whistling\n%s\n%s" (show m) (show res)) $
  res

--
-- **Definition**
--
-- For a global tree t, a node L, and a conjunction M define
-- generalize(t, L, M) =
--   let B in Seq_{\beta_L} such that B <| M & B != M
--       (M_1, M_2) = split_B(M)
--   in mcs(msg(M_1, B) \cup mcs(M_2))
--
generalize :: [G S] -> [G S] -> E.Delta -> ([([G S], T.Generalizer)], E.Delta)
generalize m b d =
  --trace "GENERALIZE" $
  let ((m1, m2), delta) = CPD.split d b m
      (generalized, _, gen, delta') = D.generalizeGoals d m1 b
  in  (fmap (project gen) $ CPD.mcs generalized ++ CPD.mcs m2, delta')
 where
  project gen goals =
    ( goals
    , {- filter (\(x, _) -> (V x) `elem` concatMap CPD.vars goals) -}
      gen
    )

abstract
  :: Descend [G S] -- The goal with ancs
  -> [G S]         -- The goal (from usage)
  -> E.Delta       -- Set of used semantic variables
  -> ([([G S], T.Generalizer)], E.Delta)
abstract descend goals d =
 --trace (printf "\nAbstracting \n%s\nDescend\n%s\n" (show goals) (show descend)) $
 go ((,[]) <$> part goals) d
 where
  -- May d == []?
  go []              d@(x : _) = ([], d)
  go ((m, gen) : gs) d
    | Just b <- whistle descend m =
          let (goals, delta) = generalize m b d
              goals' = case goals of
                         [(goal, _)] | CPD.isVariant goal m -> []
                         _ -> goals
          in  go (gs ++ goals') delta
    | otherwise = first ((m, gen):) (go gs d)

abstractChild
  :: Set [G S]                       -- Ancestors of the goal
  -> (E.Sigma, [G S], Maybe E.Gamma) -- Body: the goal with subst and ctx
  -> [(E.Sigma, [G S], T.Generalizer, E.Gamma)]
abstractChild _ (_, _, Nothing) = []
abstractChild ancs (subst, g, Just env@(x, y, d)) =
  let (abstracted, delta) = abstract (CPD.Descend g ancs) g d
  in  map (\(g, gen) -> (subst, g, gen, (x, y, delta))) abstracted

conjToList :: G a -> [G a]
conjToList (  g      :/\: h) = conjToList g ++ conjToList h
conjToList x@(Invoke _    _) = [x]
conjToList _                 = error "This conjunction is not a list of calls"

topLevel :: G X -> (GlobalTree, G S, [S])
topLevel goal =
  let (goal', defs) = takeOutLets goal
      gamma = E.updateDefsInGamma E.env0 defs
      (logicGoal, gamma', names) = E.preEval' gamma goal'
      nodes = [[logicGoal]] in
  (go nodes (CPD.Descend [logicGoal] Set.empty) gamma' E.s0 [] [], logicGoal, names) where
    go nodes d@(CPD.Descend goal ancs) gamma subst defs generalizer =
      -- if head (trd3 gamma) <= 21
      -- then
        --trace (printf "GlobalLevel:\n%s\n" $ show goal) $
        let subst = E.s0
            sldTree = CPD.sldResolution goal gamma subst in
        --trace (printf "\n\nSLDDDD\n%s\n\n%s\n\n\n" (show goal)"t" ) $ -- $  sldTree) $
        let (substs, bodies) = partition (null . snd3) $ CPD.resultants sldTree
            abstracted = map (abstractChild ancs) bodies
            (toUnfold, toNotUnfold, newNodes) =
                foldl (\ (yes, no, seen) gs ->
                            let (variants, brandNew) = partition (\(_, g, _, _) -> null g || any (CPD.isVariant g) seen) gs in
                            (yes ++ brandNew, no ++ variants, map snd4 brandNew ++ seen)
                      )
                      ([], [], nodes)
                      abstracted
        -- let leafGoals = map snd3 toUnfold in
            (def, newDefs) = undefined
            ch = map (\(subst, g, gen, env) -> go newNodes (CPD.Descend g (Set.insert goal ancs)) env subst newDefs gen) toUnfold
            forgetEnv = map (\(x, y, _) -> (x, y, []))
            forgetStuff = map (\(x, y, gen, _) -> (x,y, gen))
            substLeaves = forgetEnv substs
            leaves = forgetStuff toNotUnfold
        in Node d generalizer sldTree (map (\(subst, g, gen) -> Leaf (CPD.Descend g Set.empty) [] subst) (substLeaves ++ leaves) ++ ch)
