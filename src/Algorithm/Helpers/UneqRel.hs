
-- | Internal module. Contains data structures that can store an inequality
-- relation
module Algorithm.Helpers.UneqRel where

-- Stdlib imports
import           Data.Maybe ( fromMaybe )
-- Extra stdlib imports
import qualified Data.Set as Set
import           Data.Set ( Set )
import qualified Data.Map as Map
import           Data.Map ( Map )
import qualified Data.IntSet as IntSet
import           Data.IntSet ( IntSet )
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Strict ( IntMap )


-- # IntUneqRel #

-- Internal. Stores an /inequality/ relation. The lowest int is the map key,
-- while the highest int is the set element.
newtype IntUneqRel = IntUneqRel (IntMap IntSet)

-- | The empty inequality relation. No element is unequal to any other element.
emptyIntUneq :: IntUneqRel
emptyIntUneq = IntUneqRel IntMap.empty

-- | Returns `True` iff the provided elements are unequal within the relation.
-- Returns `False` otherwise.
areIntUneq :: Int -> Int -> IntUneqRel -> Bool
areIntUneq a b (IntUneqRel m)
  | a < b      = maybe False (IntSet.member b) (IntMap.lookup a m)
  | a > b      = maybe False (IntSet.member a) (IntMap.lookup b m)
  | otherwise  = False

-- | Insert an inequality into the relation. As the inequality relation is
-- /irreflexive/ (i.e., @x /= x@ is always false), this method throws an error
-- whenever that happens. The stated liquid type should eliminate this
-- possibility, making the function total for the "refined domain".
{-@ insertIntUneq :: x:Int -> {y:Int | x != y} -> IntUneqRel -> IntUneqRel @-}
insertIntUneq :: Int -> Int -> IntUneqRel -> IntUneqRel
insertIntUneq x y (IntUneqRel m)
  | x < y      = IntUneqRel $ IntMap.alter (Just . IntSet.insert y . fromMaybe IntSet.empty) x m
  | x > y      = IntUneqRel $ IntMap.alter (Just . IntSet.insert x . fromMaybe IntSet.empty) y m
  | otherwise  = error "a /= a" -- This case is eliminated by the liquid type


-- # OrdUneqRel #

-- Internal. Stores an /inequality/ relation. The lowest int is the map key,
-- while the highest int is the set element.
newtype OrdUneqRel a = OrdUneqRel (Map a (Set a))

-- | The empty inequality relation. No element is unequal to any other element.
emptyOrdUneq :: OrdUneqRel a
emptyOrdUneq = OrdUneqRel Map.empty

-- | Returns `True` iff the provided elements are unequal within the relation.
-- Returns `False` otherwise.
areOrdUneq :: Ord a => a -> a -> OrdUneqRel a -> Bool
areOrdUneq a b (OrdUneqRel m)
  | a < b      = maybe False (Set.member b) (Map.lookup a m)
  | a > b      = maybe False (Set.member a) (Map.lookup b m)
  | otherwise  = False

-- | Insert an inequality into the relation. As the inequality relation is
-- /irreflexive/ (i.e., @x /= x@ is always false), this method throws an error
-- whenever that happens. The stated liquid type should eliminate this
-- possibility, making the function total for the "refined domain".
{-@ insertOrdUneq :: Ord a => x:a -> {y:a | x != y} -> OrdUneqRel a -> OrdUneqRel a @-}
insertOrdUneq :: Ord a => a -> a -> OrdUneqRel a -> OrdUneqRel a
insertOrdUneq x y (OrdUneqRel m)
  | x < y      = OrdUneqRel $ Map.alter (Just . Set.insert y . fromMaybe Set.empty) x m
  | x > y      = OrdUneqRel $ Map.alter (Just . Set.insert x . fromMaybe Set.empty) y m
  | otherwise  = error "a /= a" -- This case is eliminated by the liquid type
