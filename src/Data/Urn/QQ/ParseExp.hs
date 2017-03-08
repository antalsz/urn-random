{-# LANGUAGE LambdaCase, TemplateHaskellQuotes #-}

module Data.Urn.QQ.ParseExp (
  -- * Parse a literal 'Urn'
  parseUrnList, parseUrn,
  -- * Lift components of 'Urn's straight to 'Exp's (without 'Q')
  wordExp, weightExp, sizeExp,
  btreeExp, wtreeExp,
  urnExp
) where

import Data.Traversable

import Language.Haskell.TH
import Language.Haskell.Meta.Parse

import Data.Urn.Internal
import Data.Urn.Common (fromList)

-- We don't handle extensions
parseUrnList :: String -> Either String [(Word, Exp)]
parseUrnList str =
  case parseExp $ "[" ++ str ++ "]" of
    Left  _ ->
      Left "Parse error in urn"
    Right (ListE tups) ->
      for tups $ \case
        TupE [LitE (IntegerL w), e] | toInteger (minBound :: Word) <= w
                                    , w <= toInteger (maxBound :: Word) ->
          Right (fromInteger w :: Word, e)
        TupE [_, _] ->
          Left $ "A weighted pair in this urn lacked a valid literal weight"
        _ ->
          Left $ "This urn contained a non-pair element"
    Right _ ->
      Left "This urn does not contain a list of pairs"

parseUrn :: String -> Either String (Urn Exp)
parseUrn str = (fromList <$> parseUrnList str) >>= \case
                 Just urn -> Right urn
                 Nothing  -> Left  "Empty urn"

wordExp :: Word -> Exp
wordExp = LitE . IntegerL . toInteger

weightExp :: Weight -> Exp
weightExp = wordExp

sizeExp :: Size -> Exp
sizeExp (Size s) = ConE 'Size `AppE` wordExp s

btreeExp :: BTree Exp -> Exp
btreeExp (BLeaf a)   = ConE 'BLeaf `AppE` a
btreeExp (BNode l r) = ConE 'BNode `AppE` wtreeExp l `AppE` wtreeExp r
               
wtreeExp :: WTree Exp -> Exp
wtreeExp wt = RecConE 'WTree [ ('weight, weightExp $ weight wt)
                             , ('btree,  btreeExp  $ btree  wt) ]

urnExp :: Urn Exp -> Exp
urnExp u = RecConE 'Urn [ ('size,  sizeExp  $ size  u)
                        , ('wtree, wtreeExp $ wtree u) ]
