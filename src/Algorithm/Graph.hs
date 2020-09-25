{-# LANGUAGE ScopedTypeVariables, RankNTypes, TupleSections #-}

-- | A collection of several graph algorithms.
--
-- All functions in this module are /total/, provided that any argument 
-- functions are also total.
--
-- For most functions, graphs are represented by several root nodes accompanied
-- by a successor function.
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
  , Graph (..)
  , findDuplicates
  , removeDuplicates
  , toMap
  , toMapG
  , toMapMaybe
  , isPathEq
  ) where

-- Stdlib imports
import           Data.Maybe ( fromMaybe )
import qualified Data.List.NonEmpty as NE
import           Data.List.NonEmpty ( NonEmpty ((:|)) )
-- Extra stdlib imports
import           Control.Monad ( foldM, unless, when, join, mapM_ )
import qualified Control.Monad.RWS as RWS
import           Control.Monad.RWS ( RWS, evalRWS )
import qualified Control.Monad.State as S
import           Control.Monad.State ( State, execState )
import qualified Control.Monad.Reader as R
import           Control.Monad.Reader ( Reader, runReader )
import           Control.Monad.Identity ( Identity (..), runIdentity )
import qualified Data.Map as Map
import           Data.Map ( Map )
import qualified Data.Set as Set
import           Data.Set ( Set )
import qualified Data.IntMap.Strict as IntMap
import           Data.IntMap.Strict ( IntMap )
import qualified Data.IntSet as IntSet
import           Data.IntSet ( IntSet )
-- External library imports
import qualified Data.EqRel as EqRel
import           Data.EqRel ( EqRel )
import qualified Data.IntEqRel as IntEqRel
import           Data.IntEqRel ( IntEqRel )
import qualified Data.Frozen.IntEqRel as FrozenIntEqRel
import           Data.Frozen.IntEqRel ( FrozenIntEqRel )
-- Local imports
import           Algorithm.Helpers.UneqRel
  ( OrdUneqRel, emptyOrdUneq, areOrdUneq, insertOrdUneq
  , IntUneqRel, emptyIntUneq, areIntUneq, insertIntUneq
  )


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
dominatedBy :: ( Int -> IntSet ) -> Int -> Int -> IntSet
dominatedBy fNext root node =
  IntMap.keysSet $ IntMap.filter id $ execState (dominatedFrom False root) IntMap.empty
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
dataflowFix :: Eq a => a -> ( Int -> a ) -> ( a -> a -> a ) -> ( Int -> [ ( Int, a -> a ) ] ) -> IntSet -> ( Int -> a )
dataflowFix aTop faBottom fConfluence fNext roots =
  safeLookup aTop $ dataflowFixToMap aTop faBottom fConfluence fNext roots

-- | /O(n^2)/. An iterative algorithm that finds the /least fixed point/ for the
-- given dataflow equation. Transitions exist on the edges.
dataflowFixToMap :: forall a . Eq a => a -> ( Int -> a ) -> ( a -> a -> a ) -> ( Int -> [ ( Int, a -> a ) ] ) -> IntSet -> IntMap a
dataflowFixToMap aTop faBottom fConfluence fNext roots =
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
      currVal <- S.gets $ fromMaybe (faBottom i) . IntMap.lookup i
      let newVal = fConfluence currVal aInput
      -- Only continue forward if something has changed. Otherwise it won't
      -- terminate upon reaching a fixed point.
      when ( currVal /= newVal ) $
        do
          S.modify $ IntMap.insert i newVal
          mapM_ (\(i, fTransition) -> step (fTransition newVal) i) (fNext i)

-- | One particular graph representation. It is polymorphic in its node type.
-- It is entirely represented by the roots, and nodes reachable from the roots.
data Graph a =
  Graph {
    next      :: a -> IntSet
  , nodeById  :: Int -> a
  , root      :: Int
  }

-- | /O(n^3)/. Finds duplicate nodes in the graph.
--
-- With a good classifier and "typical" graph, the complexity is close to
-- /Ω(n)/.
findDuplicates :: forall a c . Ord c
               => ( a -> c ) -- ^ Classify
               -> ( forall m . Monad m => ( Int -> Int -> m Bool ) -> a -> a -> m Bool )
                  -- ^ Is Equal
               -> Graph a
               -> IntEqRel
findDuplicates fClassify fIsEq graph =
  let nodeIds    = reachableRefl (fNext . fNode) (IntSet.singleton $ root graph)
      nodeGroups = classify (fClassify . fNode) (IntSet.toList nodeIds)
      nodePairs  = concatMap (reflPermutations . NE.toList) nodeGroups
  in
  fst $ S.execState (mapM (uncurry storeEq) nodePairs) (IntEqRel.empty, emptyIntUneq)
  where
  fNext :: a -> IntSet
  fNext = next graph

  fNode :: Int -> a
  fNode = nodeById graph

  fIsEqNode :: forall m2 . Monad m2 => ( Int -> Int -> m2 Bool ) -> Int -> Int -> m2 Bool
  fIsEqNode f i j = fIsEq f (fNode i) (fNode j)

  -- | The input nodes themselves, as well as its successor nodes are compared.
  -- This continuously traverses the outgoing paths until unequal nodes are
  -- found, or they are all equal. If the input nodes /could/ be equal (e.g.,
  -- they share the same constructor), they are /assumed/ to be equal while
  -- traversing the path. If this proves consistent (i.e., no unequal nodes are
  -- found), the nodes are /actually/ equal.
  storeEq :: Int -> Int -> State (IntEqRel, IntUneqRel) ()
  storeEq a b =
    do
      (eqRel, uneqRel) <- S.get
      -- Find out whether `a` and `b` are equal. Use previously determined
      -- equalities and inequalities to speed this up.
      let (areEqAB, uneqRel', _) = RWS.runRWS (areEqRWS (fNext . fNode) fIsEqNode a b) eqRel uneqRel
          eqRel' = applyIf areEqAB (IntEqRel.equate a b) eqRel
      S.put (eqRel', uneqRel')

-- | /O(n^3)/. Removes duplicate nodes from the graph. The output is entirely
-- represented by a new node-by-id function. This function can eliminate
-- duplicate cycles.
--
-- With a good classifier and "typical" graph, the complexity is close to
-- /Ω(n)/.
removeDuplicates :: forall a b c . Ord c
                 => ( a -> c ) -- ^ Classify
                 -> ( forall m . Monad m => ( Int -> Int -> m Bool ) -> a -> a -> m Bool )
                    -- ^ Is Equal
                 -> ( ( Int -> Int ) -> a -> b ) -- ^ Rebuild
                 -> Graph a
                 -> ( Int -> b )
removeDuplicates fClassify fIsEq fRebuild graph =
  -- Rebuild the node for the given id. Every successor reference is replaced
  -- by the canonical equivalent node (i.e., the equivalence class
  -- representative).
  \nodeI ->
    let reprI = FrozenIntEqRel.representative nodeI eqrel
    in
    fRebuild (\a -> FrozenIntEqRel.representative a eqrel) (nodeById graph reprI)
  where
  eqrel :: FrozenIntEqRel
  eqrel = fst $ IntEqRel.freeze $ findDuplicates fClassify fIsEq graph

-- | /O(n log n)/. Converts a graph - which is represented by roots and transfer
-- functions - into an `IntMap` containing all nodes.
--
-- See also `toMapG`, which operates on the `Graph` datastructure. See also
-- `reachableRefl`, which explores the same set of nodes.
toMap :: forall a . ( Int -> a ) -> ( a -> IntSet ) -> IntSet -> IntMap a
toMap fNode fNext roots =
  foldr addToMap IntMap.empty (IntSet.toList roots)
  where
  addToMap :: Int -> IntMap a -> IntMap a
  addToMap i m =
    if i `IntMap.notMember` m then
      let n  = fNode i
          m' = IntMap.insert i n m
      in foldr addToMap m' (IntSet.toList $ fNext n)
    else
      m

-- | /O(n log n)/. Converts a graph - which is represented by roots and transfer
-- functions - into an `IntMap` containing all nodes.
--
-- This variant operates on the `Graph` datastructure, while the `toMap` variant
-- operates on its fields only.
--
-- See also `reachableRefl`, which explores the same set of nodes.
toMapG :: forall a . Graph a -> IntMap a
toMapG g = toMap (nodeById g) (next g) (IntSet.singleton $ root g)

-- | /O(n log n)/. Converts a graph - that is represented by roots and transfer
-- functions - into an `IntMap` containing all nodes. If any of the reachable
-- nodes is `Nothing`, this function also returns `Nothing`.
--
-- See also `reachableRefl`, which explores the same set of nodes.
toMapMaybe :: forall a . ( Int -> Maybe a ) -> ( a -> IntSet ) -> IntSet -> Maybe (IntMap a)
toMapMaybe fNode fNext roots =
  foldM (flip addToMap) IntMap.empty (IntSet.toList roots)
  where
  addToMap :: Int -> IntMap a -> Maybe (IntMap a)
  addToMap i m =
    if i `IntMap.notMember` m then
      do
        n <- fNode i
        let m' = IntMap.insert i n m
        foldM (flip addToMap) m' (IntSet.toList $ fNext n)
    else
      return m

-- | Returns `True` if both graphs contain an identical set of paths.
isPathEq :: forall a c
          . Ord c
         => ( a -> c )
         -> ( forall m . Monad m => ( Int -> Int -> m Bool ) -> a -> a -> m Bool )
         -> Graph a
         -> Graph a
         -> Bool
isPathEq fClassify fIsEq a b =
  -- fst $ evalRWS
  --   (areEqOrdRWS eitherNext isEqEither (Left $ root a) (Right $ root b))
  --   EqRel.empty
  --   emptyOrdUneq
  runReader
    (areEqOrdRWS eitherNext isEqEither (Left $ root a) (Right $ root b))
    (EqRel.empty, emptyOrdUneq)
  where
  eitherNext :: Either Int Int -> Set (Either Int Int)
  eitherNext = either (mapIntSet Left . next a . nodeById a) (mapIntSet Right . next b . nodeById b)

  isEqEither :: Monad m => ( Either Int Int -> Either Int Int -> m Bool ) -> Either Int Int -> Either Int Int -> m Bool
  isEqEither f (Left i)  (Left j)  = fIsEq (\x y -> f (Left x)  (Left y))  (nodeById a i) (nodeById b j)
  isEqEither f (Left i)  (Right j) = fIsEq (\x y -> f (Left x)  (Right y)) (nodeById a i) (nodeById b j)
  isEqEither f (Right i) (Left j)  = fIsEq (\x y -> f (Right x) (Left y))  (nodeById a i) (nodeById b j)
  isEqEither f (Right i) (Right j) = fIsEq (\x y -> f (Right x) (Right y)) (nodeById a i) (nodeById b j)

  fNode :: Either Int Int -> a
  fNode = either (nodeById a) (nodeById b)


-- # Helpers #

mapFst :: ( a -> c ) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd :: ( b -> c ) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

safeLookup :: a -> IntMap a -> ( Int -> a )
safeLookup a m i = fromMaybe a (IntMap.lookup i m)

foldMapIntSet :: ( Int -> IntSet ) -> IntSet -> IntSet
foldMapIntSet fNext = foldMap fNext . IntSet.toList

intSetToSetInt :: IntSet -> Set Int
intSetToSetInt = Set.fromList . IntSet.toList

mapIntSet :: Ord a => ( Int -> a ) -> IntSet -> Set a
mapIntSet f = Set.fromList . map f . IntSet.toList

-- | Internal. Compares the nodes represented by its two inputs. This operates
-- under the /assumption/ of their equality (and equality of subsequent nodes),
-- and then tests if this is consistent. The `Reader` part contains these
-- assumptions that are propagated. The `State` part stores nodes that are surely unequal.
areEqRWS :: ( Int -> IntSet )
         -> ( forall m . Monad m => ( Int -> Int -> m Bool ) -> Int -> Int -> m Bool )
         -> Int
         -> Int
         -> RWS IntEqRel () IntUneqRel Bool
areEqRWS fNext fIsEq a b =
  do
    (areEqAB, eqRel) <- R.asks (IntEqRel.areEq a b)
    areUneqAB <- S.gets (areIntUneq a b)
    if areEqAB then
      return True
    else if areUneqAB then
      return False
    else
      do
        -- Assume `a` and `b` are equal, and traverse forward. If this is
        -- consistent, they are actually equal.
        isActualEq <- R.local (const $ IntEqRel.equate a b eqRel) (fIsEq (areEqRWS fNext fIsEq) a b)
        unless isActualEq (S.modify $ insertIntUneq a b)
        return isActualEq
        
-- -- | Internal. Compares the nodes represented by its two inputs. This operates
-- -- under the /assumption/ of their equality (and equality of subsequent nodes),
-- -- and then tests if this is consistent. The `Reader` part contains these
-- -- assumptions that are propagated. The `State` part stores nodes that are surely unequal.
-- areEqOrdRWS :: Ord idx
--             => ( idx -> Set idx )
--             -> ( forall m . Monad m => ( idx -> idx -> m Bool ) -> idx -> idx -> m Bool )
--             -> idx
--             -> idx
--             -> RWS (EqRel idx) () (OrdUneqRel idx) Bool
-- areEqOrdRWS fNext fIsEq a b =
--   do
--     (areEqAB, eqRel) <- R.asks (EqRel.areEq a b)
--     areUneqAB <- S.gets (areOrdUneq a b)
--     if areEqAB then
--       return True
--     else if areUneqAB then
--       return False
--     else
--       do
--         -- Assume `a` and `b` are equal, and traverse forward. If this is
--         -- consistent, they are actually equal.
--         isActualEq <- R.local (const $ EqRel.equate a b eqRel) (fIsEq (areEqOrdRWS fNext fIsEq) a b)
--         unless isActualEq (S.modify $ insertOrdUneq a b)
--         return isActualEq
        
-- | Internal. Compares the nodes represented by its two inputs. This operates
-- under the /assumption/ of their equality (and equality of subsequent nodes),
-- and then tests if this is consistent. The `Reader` part contains these
-- assumptions that are propagated. The `State` part stores nodes that are surely unequal.
areEqOrdRWS :: Ord idx
            => ( idx -> Set idx )
            -> ( forall m . Monad m => ( idx -> idx -> m Bool ) -> idx -> idx -> m Bool )
            -> idx
            -> idx
            -> Reader (EqRel idx, OrdUneqRel idx) Bool
areEqOrdRWS fNext fIsEq a b =
  do
    (areEqAB, eqRel) <- R.asks (EqRel.areEq a b . fst)
    areUneqAB <- R.asks (areOrdUneq a b . snd)
    if areEqAB then
      return True
    else if areUneqAB then
      return False
    else
      do
        -- Assume `a` and `b` are equal, and traverse forward. If this is
        -- consistent, they are actually equal.
        R.local (mapFst $ const $ EqRel.equate a b eqRel) (fIsEq (areEqOrdRWS fNext fIsEq) a b)

applyIf :: Bool -> ( a -> a ) -> a -> a
applyIf True  f a = f a
applyIf False _ a = a

mapEither :: ( a -> c ) -> ( b -> d ) -> Either a b -> Either c d
mapEither f g = either (Left . f) (Right . g)

-- | 
reflPermutations :: [a] -> [(a,a)]
reflPermutations (x:ys) = [(x,y) | y <- ys] ++ reflPermutations ys
reflPermutations _      = []

classify :: forall a b . Ord b => ( a -> b ) -> [a] -> [NonEmpty a]
classify fClassify = Map.elems . foldr classify' Map.empty
  where
  classify' :: a -> Map b (NonEmpty a) -> Map b (NonEmpty a)
  classify' a = Map.alter (Just . mCons a) (fClassify a)

  mCons :: c -> Maybe (NonEmpty c) -> NonEmpty c
  mCons x Nothing   = x :| []
  mCons x (Just xs) = x :| NE.toList xs

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb m = join (unless <$> mb <*> pure m)
