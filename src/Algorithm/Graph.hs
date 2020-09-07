
module Algorithm.Graph
  ( invert
  , invertToMap
  , reachableRefl
  , reachable
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

-- | Inverts the given graph.
--
-- Nodes in graphs are represented by 'Int's. The input graph is fully described
-- by the root nodes and a transition function to the next nodes in the graph.
-- Note that the graph is thus considered to contain only the nodes reachable
-- from the roots.
invert :: ( Int -> IntSet ) -> IntSet -> ( Int -> IntSet )
invert fNext roots = safeLookup IntSet.empty $ invertToMap fNext roots

-- | Inverts the given graph.
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

-- | Returns the set of nodes reachable from the given source nodes.
--
-- This determines reflexive transitive reachability. So every node always
-- reaches itself.
reachableRefl :: ( Int -> IntSet ) -> IntSet -> IntSet
reachableRefl fNext roots = roots `IntSet.union` reachable fNext roots

-- | Returns the set of nodes reachable from the given source nodes.
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
