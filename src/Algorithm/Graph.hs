
module Algorithm.Graph
  ( invert
  , invertToMap
  , reachableRefl
  , reachable
  , dominatedBy
  , allDominators
  , allDominatorsToMap
  ) where

-- Stdlib imports
import           Data.Maybe ( fromMaybe )
-- Extra stdlib imports
import           Control.Monad ( unless, join, mapM_ )
import qualified Control.Monad.State as S
import           Control.Monad.State ( State, execState )
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Strict ( IntMap )
import qualified Data.IntSet as IntSet
import           Data.IntSet ( IntSet )


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
-- any root node to a dominated node passes through the dominator.
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

allDominators :: ( Int -> IntSet ) -> IntSet -> ( Int -> IntSet )
allDominators fNext roots = safeLookup IntSet.empty $ allDominatorsToMap fNext roots

-- | /O(n^2)/.
allDominatorsToMap :: ( Int -> IntSet ) -> IntSet -> IntMap IntSet
allDominatorsToMap fNext roots =
  let allNodes = reachableRefl fNext roots
  in execState (mapM_ (\i -> intersectStep i (IntSet.singleton i)) $ IntSet.toList roots) IntMap.empty
  where
  allNodes :: IntSet
  allNodes = reachableRefl fNext roots

  intersectStep :: Int -> IntSet -> State (IntMap IntSet) ()
  intersectStep i s =
    do
      currSet <- S.gets $ fromMaybe allNodes . IntMap.lookup i
      let newSet = currSet `IntSet.intersection` (IntSet.insert i s)
      unless (newSet == currSet) $
        do
          S.modify $ IntMap.insert i newSet
          mapM_ (\j -> intersectStep j newSet) $ IntSet.toList (fNext i)

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
