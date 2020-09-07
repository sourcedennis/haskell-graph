
module Main where

-- Stdlib imports
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Strict ( IntMap )
import qualified Data.IntSet as IntSet
import           Data.IntSet ( IntSet )
import           Data.Maybe ( fromMaybe )
-- Local imports
import Algorithm.Graph as Graph

main :: IO ()
main =
  let edges = [(0,1), (0,2), (2,3), (3,4), (4,5), (5,1)]
      graph = IntMap.fromListWith IntSet.union $ map (mapSnd IntSet.singleton) edges
  in
  do
    print $ graph
    print $ Graph.invertToMap (\i -> fromMaybe IntSet.empty $ IntMap.lookup i graph) (IntSet.singleton 0)
    print $ Graph.reachableRefl (\i -> fromMaybe IntSet.empty $ IntMap.lookup i graph) (IntSet.singleton 4)

    let edges2 = [(0,1),(1,3),(3,5),(5,2),(0,2),(2,4),(4,6),(6,1)]
        graph2 = IntMap.fromListWith IntSet.union $ map (mapSnd IntSet.singleton) edges2
    print graph2
    print $ Graph.dominatedBy (\i -> fromMaybe IntSet.empty $ IntMap.lookup i graph2) (IntSet.singleton 0) 1

mapSnd :: ( b -> c ) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)
