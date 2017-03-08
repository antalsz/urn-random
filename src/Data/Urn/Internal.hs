{-# LANGUAGE GeneralizedNewtypeDeriving, PatternSynonyms #-}
{-# OPTIONS_HADDOCK not-home #-}

module Data.Urn.Internal (
  -- * Types
  -- ** Parameters of the trees
  Weight, Index(..), Size(..),
  -- ** Tree types (and constructors)
  BTree(..), WTree(..), pattern WLeaf, pattern WNode, Urn(..),
  -- * Sampling/lookup ('WTree's and 'BTree's)
  sample, bsample,
  -- * Insertion ('Urn's)
  insert, uninsert,
  -- * Update and construct ('WTree's)
  update, replace, construct,
  -- * General weight-based 'WTree' traversal
  foldWTree,
  -- * Raw random index generation
  randomIndexWith,
  -- * Debugging
  showTree
) where

import Data.Bits
import Data.Foldable (toList)
import Data.Urn.Internal.AlmostPerfect

-- For the 'Show' instance
import qualified Data.Ord  as Ord
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tree (Tree(..), drawTree)

----------------------------------------

type Weight = Word

newtype Index = Index { getIndex :: Word } deriving (Eq, Ord)
-- This type is opaque, so there's no 'Show' instance.

newtype Size = Size { getSize :: Word }
             deriving ( Eq, Ord, Show, Bounded, Enum
                      , Num, Real, Integral
                      , Bits, FiniteBits )

data BTree a = BLeaf a
             | BNode !(WTree a) !(WTree a)
             deriving (Eq, Ord, Show)

data WTree a = WTree { weight :: !Weight
                     , btree  :: !(BTree a) }
             deriving (Eq, Ord, Show)

pattern WLeaf :: Weight -> a -> WTree a
pattern WNode :: Weight -> WTree a -> WTree a -> WTree a
pattern WLeaf w a   = WTree { weight = w, btree = BLeaf a }
pattern WNode w l r = WTree { weight = w, btree = BNode l r }

data Urn a = Urn { size  :: !Size
                 , wtree :: !(WTree a) }
-- TODO: 'Eq' and 'Ord' instances?  We can provide an O(n²) 'Eq' instance, and
-- an O(n log n) 'Ord' instance; the 'Eq' instance goes down to O(n log n) if
-- we're willing to require an 'Ord' constraint.

-- |This 'Show' instance prints out the elements from most-weighted to
-- least-weighted; however, do not rely on the order of equally-weighted
-- elements, as this may depend on details of the implementation.
instance Show a => Show (Urn a) where
  showsPrec p u = showParen (p > 10) $
                    showString "fromList " . shows (toList [] $ wtree u) where
    toList acc (WLeaf w a)   = List.insertBy (flip $ Ord.comparing fst) (w,a) acc
    toList acc (WNode _ l r) = toList (toList acc l) r

-- TODO: A debugging equivalent of 'show' for the tree structure, like
-- 'Data.Set.showTree'?

showTree :: Show a => Urn a -> String
showTree (Urn s t)=
  "(" ++ show (getSize s) ++ ")\n" ++ drawTree (stringTree t)
  where
    stringTree (WLeaf w a)   = Node (show (w, a)) []
    stringTree (WNode w l r) = Node (show w) [stringTree l, stringTree r]

----------------------------------------

randomIndexWith :: Functor f => ((Word,Word) -> f Word) -> Urn a -> f Index
randomIndexWith rand u  = Index <$> rand (0, getSize (size u) - 1)
{-# INLINABLE randomIndexWith #-}

----------------------------------------

bsample :: BTree a -> Index -> a
bsample (BLeaf a) _ =
  a
bsample (BNode (WTree wl l) (WTree _ r)) (Index i)
  | i < wl    = bsample l (Index i)
  | otherwise = bsample r (Index $ i - wl)

sample :: WTree a -> Index -> a
sample = bsample . btree
{-# INLINABLE sample #-}

foldWTree :: (Weight -> a -> b)
          -> (Weight -> b -> WTree a -> b)
          -> (Weight -> WTree a -> b -> b)
          -> Size -> WTree a
          -> b
foldWTree fLeaf fLeft fRight = go where
  go _    (WLeaf w a)                      = fLeaf  w a
  go path (WNode w l r) | path `testBit` 0 = fRight w l            (go path' r)
                        | otherwise        = fLeft  w (go path' l) r
                        where path' = path `shiftR` 1
{-# INLINABLE foldWTree #-}

insert :: Weight -> a -> Urn a -> Urn a
insert w' a' (Urn size wt) =
  Urn (size+1) $ foldWTree (\w a -> WNode (w+w') (WLeaf w a) (WLeaf w' a'))
                           (\w   -> WNode (w+w'))
                           (\w   -> WNode (w+w'))
                           size wt
{-# INLINABLE insert #-}

uninsert :: Urn a -> (Weight, a, Weight, Maybe (Urn a))
uninsert (Urn size wt) =
  case foldWTree (\w a       -> (w, a, 0, Nothing))
                 (\w ul' r   -> case ul' of
                                  (w', a', lb, Just l') -> (w', a', lb, Just $ WNode (w-w') l' r)
                                  (w', a', lb, Nothing) -> (w', a', lb, Just r))
                 (\w l   ur' -> case ur' of
                                  (w', a', lb, Just r') -> (w', a', lb + weight l, Just $ WNode (w-w') l r')
                                  (w', a', lb, Nothing) -> (w', a', lb + weight l, Just l))
                 (size-1) wt of
    (w', a', lb, mt) -> (w', a', lb, Urn (size-1) <$> mt)
{-# INLINABLE uninsert #-}

update :: (Weight -> a -> (Weight, a)) -> WTree a -> Index -> (Weight, a, Weight, a, WTree a)
update upd = go where
  go (WLeaf w a) _ =
    let (wNew, aNew) = upd w a
    in (w, a, wNew, aNew, WLeaf wNew aNew)
  go (WNode w l@(WTree wl _) r) (Index i)
    | i < wl    = case go l (Index i) of
                    (wOld, aOld, wNew, aNew, l') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l' r)
    | otherwise = case go r (Index $ i-wl) of
                    (wOld, aOld, wNew, aNew, r') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l r')

replace :: Weight -> a -> WTree a -> Index -> (Weight, a, WTree a)
replace wNew aNew = go where
  go (WLeaf w a) _ =
    (w, a, WLeaf wNew aNew)
  go (WNode w l@(WTree wl _) r) (Index i)
    | i < wl    = case go l (Index i) of
                    (w', a', l') -> (w', a', WNode (w-w'+wNew) l' r)
    | otherwise = case go r (Index $ i-wl) of
                    (w', a', r') -> (w', a', WNode (w-w'+wNew) l r')

construct :: NonEmpty (Weight, a) -> Urn a
construct list = Urn (Size size) tree
  where
    size = fromIntegral $ length list
    tree = almostPerfect (\l r -> WNode (weight l + weight r) l r)
                         (uncurry WLeaf)
                         size
                         (toList list)
