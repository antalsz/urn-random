{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, GADTs,
             GeneralizedNewtypeDeriving, PatternSynonyms, TypeOperators #-}
{-# OPTIONS_GHC -funbox-strict-fields -Wall #-}

import Prelude hiding (lookup)
import Test.QuickCheck

type Weight = Int

data Direction = GoLeft | GoRight deriving (Eq, Ord, Show, Read, Enum, Bounded)

inv :: Direction -> Direction
inv GoLeft  = GoRight
inv GoRight = GoLeft

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
  go t@(Leaf w _)       = Node (w+w') GoLeft  t      (Leaf w' a')
  go (Node w GoLeft  l r) = Node (w+w') GoRight (go l) r
  go (Node w GoRight l r) = Node (w+w') GoLeft  l      (go r)

-- Not self-balancing!… yet
delete :: Weight -> Tree a -> (Weight, a, Maybe (Tree a))
delete _ (Leaf w a) =
  (w, a, Nothing)
delete i (Node w d l@(Tree wl _) r)
  | i < wl    = case delete i l of
                  (w', a, Just l') -> (w', a, Just $ Node (w-w') d l' r)
                  (w', a, Nothing) -> (w', a, Just r)
  | otherwise = case delete (i-wl) r of
                  (w', a, Just r') -> (w', a, Just $ Node (w-w') d l r')
                  (w', a, Nothing) -> (w', a, Just l)

fromList :: [(Weight,a)] -> Maybe (Tree a)
fromList []          = Nothing
fromList ((w,t):wts) = Just $ foldr (uncurry insert) (Leaf w t) wts

frequencyT :: Tree (Gen a) -> Gen a
frequencyT (Tree w t) = lookup t =<< choose (0, w-1)

frequency' :: [(Weight,Gen a)] -> Gen a
frequency' = maybe (error "frequency' used with empty list") frequencyT . fromList
