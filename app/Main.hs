
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
  let edges = [(0,1), (1,2), (2,4), (4,5), (5,6), (1,3), (3,7), (7,8), (8,3), (5,7), (7,9), (9,10)]
      graph = IntMap.fromListWith IntSet.union $ map (mapSnd IntSet.singleton) edges
      fNext = (\i -> fromMaybe IntSet.empty $ IntMap.lookup i graph)
  in
  print $ Graph.allDominatorsToMap fNext (IntSet.singleton 0)

mapSnd :: ( b -> c ) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)
