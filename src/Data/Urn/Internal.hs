-- TODO: |delete| is wrong!!!

{-# LANGUAGE GeneralizedNewtypeDeriving, PatternSynonyms #-}

module Data.Urn.Internal where

import Prelude hiding (lookup)
import Data.Bifunctor
import Data.Foldable
import Data.Bits
import Test.QuickCheck

type Weight = Word

newtype Index = Index Word deriving (Eq, Ord) -- Show?

newtype Size = Size Word deriving ( Eq, Ord, Show, Bounded, Enum
                                  , Num, Real, Integral
                                  , Bits, FiniteBits )

data BTree a = BLeaf a
             | BNode !(WTree a) !(WTree a)
             deriving (Eq, Ord, Show)

data WTree a = WTree { weight :: !Weight
                     , btree  :: !(BTree a) }
             deriving (Eq, Ord, Show)

pattern WLeaf w a   = WTree { weight = w, btree = BLeaf a }
pattern WNode w l r = WTree { weight = w, btree = BNode l r }

data Urn a = Urn { size  :: !Size
                 , wtree :: !(WTree a) }
           deriving (Eq, Ord, Show)

blookup :: BTree a -> Index -> a
blookup (BLeaf a) _ =
  a
blookup (BNode (WTree wl l) (WTree _ r)) (Index i)
  | i < wl    = blookup l (Index i)
  | otherwise = blookup r (Index $ i - wl)

lookup :: Urn a -> Index -> a
lookup = blookup . btree . wtree

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

uninsert :: Urn a -> (Weight, a, Maybe (Urn a))
uninsert (Urn size wt) =
  case foldWTree (\w a       -> (w, a, Nothing))
                 (\w ul' r   -> case ul' of
                                  (w', a', Just l') -> (w', a', Just $ WNode (w-w') l' r)
                                  (w', a', Nothing) -> (w', a', Just r))
                 (\w l   ur' -> case ur' of
                                  (w', a', Just r') -> (w', a', Just $ WNode (w-w') l r')
                                  (w', a', Nothing) -> (w', a', Just l))
                 (size-1) wt of
    (w', a', mt) -> (w', a', Urn (size-1) <$> mt)

wupdate :: (Weight -> a -> (Weight, a)) -> WTree a -> Index -> (Weight, a, Weight, a, WTree a)
wupdate upd = go where
  go (WLeaf w a) _ =
    let (wNew, aNew) = upd w a
    in (w, a, wNew, aNew, WLeaf wNew aNew)
  go (WNode w l@(WTree wl _) r) (Index i)
    | i < wl    = case go l (Index i) of
                    (wOld, aOld, wNew, aNew, l') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l' r)
    | otherwise = case go r (Index $ i-wl) of
                    (wOld, aOld, wNew, aNew, r') -> (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l r')

update :: (Weight -> a -> (Weight, a)) -> Urn a -> Index -> (Weight, a, Weight, a, Urn a)
update upd (Urn size wt) i =
  case wupdate upd wt i of
    (wOld, aOld, wNew, aNew, wt') -> (wOld, aOld, wNew, aNew, Urn size wt')

wreplace :: Weight -> a -> WTree a -> Index -> (Weight, a, WTree a)
wreplace wNew aNew = go where
  go (WLeaf w a) _ =
    (w, a, WLeaf wNew aNew)
  go (WNode w l@(WTree wl _) r) (Index i)
    | i < wl    = case go l (Index i) of
                    (w', a', l') -> (w', a', WNode (w-w'+wNew) l' r)
    | otherwise = case go r (Index $ i-wl) of
                    (w', a', r') -> (w', a', WNode (w-w'+wNew) l r')

replace :: Weight -> a -> Urn a -> Index -> (Weight, a, Urn a)
replace wNew aNew (Urn size wt) i = case wreplace wNew aNew wt i of
                                      (w', a', wt') -> (w', a', Urn size wt')

delete :: Urn a -> Index -> (Weight, a, Maybe (Urn a))
delete t i = case uninsert t of
               (w', a', Just t')   -> case replace w' a' t' i of
                                        (w'', a'', t'') -> (w'', a'', Just t'')
               res@(_, _, Nothing) -> res

singleton :: Weight -> a -> Urn a
singleton w a = Urn { size = 1, wtree = WLeaf w a }

fromList :: [(Weight,a)] -> Maybe (Urn a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldl' (flip $ uncurry insert) (singleton w t) wts

frequencyT :: Urn (Gen a) -> Gen a
frequencyT (Urn _ (WTree w bt)) = blookup bt . Index =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "frequency' used with empty list") frequencyT . fromList

prop_insert_uninsert :: NonZero Weight -> Char -> NonEmptyList (NonZero Weight, Char) -> Bool
prop_insert_uninsert (NonZero w) x (NonEmpty cs) =
  let Just t = fromList $ map (first getNonZero) cs
  in uninsert (insert w x t) == (w, x, Just t)
