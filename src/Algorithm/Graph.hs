{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}

module Algorithm.Graph
  ( invert
  , invertToMap
  , reachableRefl
  , reachable
  , dominatedBy
  , allDominators
  , allDominatorsToMap
  , dataflowFix
  , dataflowFixToMap
  , findDuplicates
  ) where

-- Stdlib imports
import           Data.Maybe ( fromMaybe )
import qualified Data.List.NonEmpty as NE
import           Data.List.NonEmpty ( NonEmpty ((:|)) )
-- Extra stdlib imports
import           Control.Monad ( unless, when, join, mapM_ )
import qualified Control.Monad.State as S
import           Control.Monad.State ( State, execState )
import qualified Control.Monad.RWS as RWS
import           Control.Monad.RWS ( RWS )
import qualified Control.Monad.Reader as R
import           Control.Monad.Reader ( Reader )
import qualified Data.Map as Map
import           Data.Map ( Map )
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Strict ( IntMap )
import qualified Data.IntSet as IntSet
import           Data.IntSet ( IntSet )
-- External library imports
import qualified Data.EqRel as EqRel
import           Data.EqRel ( EqRel )
import qualified Data.IntEqRel as IntEqRel
import           Data.IntEqRel ( IntEqRel )


-- | Internal.
type Visited = IntSet

-- | /O(n)/. Inverts the given graph.
--
-- Nodes in graphs are represented by 'Int's. The input graph is fully described
-- by the root nodes and a transition function to the next nodes in the graph.
-- Note that the graph is thus considered to contain only the nodes reachable
-- from the roots.
invert :: ( Int -> IntSet ) -> IntSet -> ( Int -> IntSet )
invert fNext roots = safeLookup IntSet.empty $ invertToMap fNext roots

-- | /O(n)/. Inverts the given graph.
--
-- Nodes in graphs are represented by 'Int's. The input graph is fully described
-- by the root nodes and a transition function to the next nodes in the graph.
-- Note that the graph is thus considered to contain only the nodes reachable
-- from the roots.
invertToMap :: ( Int -> IntSet ) -> IntSet -> IntMap IntSet
invertToMap fNext roots = snd $ execState (mapM_ invertFrom $ IntSet.toList roots) (IntSet.empty, IntMap.empty)
  where
  invertFrom :: Int -> State (Visited, IntMap IntSet) ()
  invertFrom i =
    unlessM (isVisited i) $
      do
        markVisited i
        let nextNodes = IntSet.toList $ fNext i
        mapM_ (\j -> insertEdge j i) nextNodes
        mapM_ invertFrom nextNodes

  markVisited :: Int -> State (Visited, a) ()
  markVisited = S.modify . mapFst . IntSet.insert

  isVisited :: Int -> State (Visited, a) Bool
  isVisited i = S.gets ( IntSet.member i . fst )

  insertEdge :: Int -> Int -> State (a, IntMap IntSet) ()
  insertEdge i j = S.modify $ mapSnd $ IntMap.alter (Just . IntSet.insert j . fromMaybe IntSet.empty) i

-- | /O(n)/. Returns the set of nodes reachable from the given source nodes.
--
-- This determines reflexive transitive reachability. So every node always
-- reaches itself.
reachableRefl :: ( Int -> IntSet ) -> IntSet -> IntSet
reachableRefl fNext roots = roots `IntSet.union` reachable fNext roots

-- | /O(n)/. Returns the set of nodes reachable from the given source nodes.
--
-- Note that this only determines transitive reachability, so a node /cannot/
-- generally reach itself. A node can only reach itself through a cycle. if
-- /reflexive/ reachability is desired, use 'reachableRefl' instead.
reachable :: ( Int -> IntSet ) -> IntSet -> IntSet
reachable fNext roots = execState (mapM_ reachableFrom $ IntSet.toList $ foldMapIntSet fNext roots) IntSet.empty
  where
  reachableFrom :: Int -> State Visited ()
  reachableFrom i =
    unlessM (isVisited i) $
      do
        markVisited i
        mapM_ reachableFrom (IntSet.toList $ fNext i)

  markVisited :: Int -> State Visited ()
  markVisited = S.modify . IntSet.insert

  isVisited :: Int -> State Visited Bool
  isVisited i = S.gets ( IntSet.member i )


-- | /O(n)/. Returns the set of nodes dominated by the given node. The path from
-- /every/ root node to a dominated node passes through the dominator.
dominatedBy :: ( Int -> IntSet ) -> IntSet -> Int -> IntSet
dominatedBy fNext roots node =
  IntMap.keysSet $ IntMap.filter id $ execState (mapM_ (dominatedFrom False) (IntSet.toList roots)) IntMap.empty
  where
  -- When a node is `Nothing` it can become `Just True` or `Just False`,
  -- depending on whether the dominator was visited. When it is `Just True`,
  -- it can become `Just False` if a path without dominator is found.
  -- So: Nothing ~> Just True ~> Just False
  -- Every node is thus visited at most once. Hence the entire procedure takes
  -- /O(n)/.
  dominatedFrom :: Bool -> Int -> State (IntMap Bool) ()
  dominatedFrom isDominatorVisited i =
    do
      m <- S.get
      let isDominatorVisited' = isDominatorVisited || i == node
      case i `IntMap.lookup` m of
        Nothing ->
          do
            S.modify $ IntMap.insert i isDominatorVisited'
            mapM_ (dominatedFrom isDominatorVisited') (IntSet.toList $ fNext i)
        Just False ->
          -- There is a path where this node is /not/ preceded by the dominator,
          -- so it's not dominated. Ignore.
          return ()
        Just True ->
          unless isDominatorVisited' $
            do
              -- A path is found where the dominator is not visited. So the
              -- current node is not dominated after all.
              S.modify $ IntMap.insert i False
              mapM_ (dominatedFrom False) (IntSet.toList $ fNext i)

-- | /O(n^2)/. Computes for each node in the graph its dominators. A node
-- dominates another if /every/ path from /every/ root passes through the
-- dominator.
allDominators :: ( Int -> IntSet ) -> IntSet -> ( Int -> IntSet )
allDominators fNext roots =
  safeLookup IntSet.empty $ allDominatorsToMap fNext roots

-- | /O(n^2)/. Computes for each node in the graph its dominators. A node
-- dominates another if /every/ path from /every/ root to the dominated node
-- passes through the dominator.
--
-- This function produces a map with an entry for each node. This entry contains
-- the node's dominators.
allDominatorsToMap :: ( Int -> IntSet ) -> IntSet -> IntMap IntSet
allDominatorsToMap fNext roots =
  execState (mapM_ (\i -> intersectStep i (IntSet.singleton i)) $ IntSet.toList roots) IntMap.empty
  where
  allNodes :: IntSet
  allNodes = reachableRefl fNext roots

  intersectStep :: Int -> IntSet -> State (IntMap IntSet) ()
  intersectStep i s =
    do
      currSet <- S.gets $ fromMaybe allNodes . IntMap.lookup i
      let newSet = currSet `IntSet.intersection` (IntSet.insert i s)
      when (newSet /= currSet) $
        do
          S.modify $ IntMap.insert i newSet
          mapM_ (\j -> intersectStep j newSet) $ IntSet.toList (fNext i)

-- | /O(n^2)/. An iterative algorithm that finds the /least fixed point/ for the
-- given dataflow equation. Transitions exist on the edges.
dataflowFix :: Eq a => a -> a -> ( a -> a -> a ) -> ( Int -> [ ( Int, a -> a ) ] ) -> IntSet -> ( Int -> a )
dataflowFix aTop aBottom fConfluence fNext roots =
  safeLookup aTop $ dataflowFixToMap aTop aBottom fConfluence fNext roots

-- | /O(n^2)/. An iterative algorithm that finds the /least fixed point/ for the
-- given dataflow equation. Transitions exist on the edges.
dataflowFixToMap :: forall a . Eq a => a -> a -> ( a -> a -> a ) -> ( Int -> [ ( Int, a -> a ) ] ) -> IntSet -> IntMap a
dataflowFixToMap aTop aBottom fConfluence fNext roots =
  -- Note that the roots are initialised to the /top/ value, as nothing is known
  -- about them. The other (reachable) nodes are initialised with /bottom/.
  -- Through iteration, a "higher" value (in the lattice) can be found that is
  -- consistent with the equation.
  execState (mapM_ (step aTop) $ IntSet.toList roots) IntMap.empty
  where
  step :: a -> Int -> State (IntMap a) ()
  step aInput i =
    do
      -- If the node's value is unknown, it's initialised with /bottom/.
      -- Through iteration it may obtain a "better" value that is consistent
      -- with the graph under the dataflow equation.
      currVal <- S.gets $ fromMaybe aBottom . IntMap.lookup i
      let newVal = fConfluence currVal aInput
      -- Only continue forward if something has changed. Otherwise it won't
      -- terminate upon reaching a fixed point.
      when ( currVal /= newVal ) $
        do
          S.modify $ IntMap.insert i newVal
          mapM_ (\(i, fTransition) -> step (fTransition newVal) i) (fNext i)

-- /O(n^3)/. Finds duplicate nodes in the graph.
--
-- With a good classifier and "typical" graph, the complexity is close to
-- /Ω(n^2)/.
findDuplicates :: Ord b
               => ( a -> b ) -- ^ Classify
               -> ( forall m . ( Int -> Int -> m Bool ) -> a -> a -> m Bool )
                  -- ^ Is Equal
               -> ( a -> IntSet ) -- ^ Next
               -> ( Int -> a )    -- ^ Graph node mapping
               -> IntSet          -- ^ Roots
               -> IntEqRel
findDuplicates fClassify fIsEq fNext fNode roots =
  let nodeIds    = reachableRefl (fNext . fNode) roots
      nodeGroups = classify (fClassify . fNode) (IntSet.toList nodeIds)
      nodePairs  = concatMap reflPermutations nodeGroups
  in
  fst $ S.execState (mapM (uncurry storeEq) nodePairs) (IntEqRel.empty, IntMap.empty)
  where
  storeEq :: Int -> Int -> State (IntEqRel, IntUneqRel) ()
  storeEq a b =
    do
      (eqRel, uneqRel) <- S.get
      let (areEqAB, uneqRel', _) = RWS.runRWS (areEq a b) eqRel uneqRel
      S.put (eqRel, uneqRel')

  areEq :: Int -> Int -> RWS IntEqRel () IntUneqRel Bool
  areEq a b =
    do
      (areEqAB, eqRel) <- R.asks (IntEqRel.areEq a b)
      areUneqAB <- S.gets (areInUneq a b)
      if areEqAB then
        return True
      else if areUneqAB || fClassify (fNode a) /= fClassify (fNode b) then
        return False
      else
        do
          let aNode = fNode a
              bNode = fNode b
          isActualEq <- R.local (const $ IntEqRel.equate a b eqRel) (fIsEq areEq aNode bNode)
          unless isActualEq (S.modify $ insertUneq a b)
          return isActualEq


-- # Helpers #

mapFst :: ( a -> c ) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd :: ( b -> c ) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb m = join (unless <$> mb <*> pure m)

safeLookup :: a -> IntMap a -> ( Int -> a )
safeLookup a m i = fromMaybe a (IntMap.lookup i m)

foldMapIntSet :: ( Int -> IntSet ) -> IntSet -> IntSet
foldMapIntSet fNext = foldMap fNext . IntSet.toList

-- | 
reflPermutations :: NonEmpty a -> [(a,a)]
reflPermutations (x :| [])        = []
reflPermutations (x :| ys@(z:zs)) = [(x,y) | y <- ys] ++ reflPermutations (z :| zs)

classify :: forall a b . Ord b => ( a -> b ) -> [a] -> [NonEmpty a]
classify fClassify = Map.elems . foldr classify' Map.empty
  where
  classify' :: a -> Map b (NonEmpty a) -> Map b (NonEmpty a)
  classify' a = Map.alter (Just . mCons a) (fClassify a)

  mCons :: c -> Maybe (NonEmpty c) -> NonEmpty c
  mCons x Nothing   = x :| []
  mCons x (Just xs) = x :| NE.toList xs

-- Internal. Stores an /inequality/ relation. The lowest int is the map key,
-- while the highest int is the set element.
type IntUneqRel = IntMap IntSet

areInUneq :: Int -> Int -> IntUneqRel -> Bool
areInUneq a b m
  | a < b      = maybe False (IntSet.member b) (IntMap.lookup a m)
  | a > b      = maybe False (IntSet.member a) (IntMap.lookup b m)
  | otherwise  = False

insertUneq :: Int -> Int -> IntUneqRel -> IntUneqRel
insertUneq a b m
  | a < b      = IntMap.alter (Just . IntSet.insert b . fromMaybe IntSet.empty) a m
  | a > b      = IntMap.alter (Just . IntSet.insert a . fromMaybe IntSet.empty) b m
  | otherwise  = error "a /= a"
