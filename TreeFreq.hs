{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, GADTs,
             GeneralizedNewtypeDeriving, PatternSynonyms, TypeOperators #-}
{-# OPTIONS_GHC -funbox-strict-fields -Wall #-}

module TreeFreq where

import Prelude hiding (lookup)
import Data.Foldable
import Test.QuickCheck

type Weight = Word

data Direction = GoLeft | GoRight deriving (Eq, Ord, Show, Read, Enum, Bounded)

data Tree' a = Leaf' a
             | Node' !Direction !(Tree a) !(Tree a)
             deriving (Eq, Ord, Show)

data Tree a = Tree { weight :: !Weight
                   , tree'  :: !(Tree' a) }
            deriving (Eq, Ord, Show)

pattern Leaf w a     = Tree { weight = w, tree' = Leaf' a }
pattern Node w p l r = Tree { weight = w, tree' = Node' p l r }

lookup :: Tree' a -> Weight -> a
lookup (Leaf' a) _ =
  a
lookup (Node' _ (Tree wl l) (Tree _ r)) i
  | i < wl    = lookup l i
  | otherwise = lookup r (i - wl)

insert :: Weight -> a -> Tree a -> Tree a
insert w' a' = go where
  go leaf@(Leaf w _)      = Node (w+w') GoLeft  leaf   (Leaf w' a')
  go (Node w GoLeft  l r) = Node (w+w') GoRight (go l) r
  go (Node w GoRight l r) = Node (w+w') GoLeft  l      (go r)

delete :: Weight -> Tree a -> (Weight, a, Maybe (Tree a))
delete i t = case uninsert t of
               (w', a', Just t')   -> case replace w' a' i t' of
                                        (w'', a'', t'') -> (w'', a'', Just t'')
               res@(_, _, Nothing) -> res

uninsert :: Tree a -> (Weight, a, Maybe (Tree a))
uninsert (Leaf w a)           =
  (w, a, Nothing)
uninsert (Node w GoLeft  l r) =
  case uninsert r of
    (w', a', Just r') -> (w', a', Just $ Node (w-w') GoRight l r')
    (w', a', Nothing) -> (w', a', Just l)
uninsert (Node w GoRight l r) =
  case uninsert l of
    (w', a', Just l') -> (w', a', Just $ Node (w-w') GoLeft  l' r)
    (w', a', Nothing) -> (w', a', Just r)

replace :: Weight -> a -> Weight -> Tree a -> (Weight, a, Tree a)
replace wNew aNew = go where
  go _ (Leaf w a) =
    (w, a, Leaf wNew aNew)
  go i (Node w d l@(Tree wl _) r)
    | i < wl    = case go i l of
                    (w', a', l') -> (w', a', Node (w-w'+wNew) d l' r)
    | otherwise = case go (i-wl) r of
                    (w', a', r') -> (w', a', Node (w-w'+wNew) d l r')

fromList :: [(Weight,a)] -> Maybe (Tree a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldl' (flip $ uncurry insert) (Leaf w t) wts

frequencyT :: Tree (Gen a) -> Gen a
frequencyT (Tree w t) = lookup t =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "frequency' used with empty list") frequencyT . fromList
