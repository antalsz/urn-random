{-# LANGUAGE DefaultSignatures #-}

module Data.Urn.RandomWord (RandomWord(..)) where

import Control.Monad.Random
import Test.QuickCheck
import qualified Data.Random as RF

-- Transformers
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.Writer.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy   as Lazy
import qualified Control.Monad.Trans.State.Strict  as Strict
import qualified Control.Monad.Trans.State.Lazy    as Lazy
import qualified Control.Monad.Trans.RWS.Strict    as Strict
import qualified Control.Monad.Trans.RWS.Lazy      as Lazy
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Cont

----------------------------------------

class Monad m => RandomWord m where
  randomWord :: (Word,Word) -> m Word
  default randomWord :: MonadRandom m => (Word,Word) -> m Word
  randomWord = getRandomR

instance RandomWord IO
instance (Monad m, RandomGen g) => RandomWord (RandT g m)

instance RandomWord Gen where
  randomWord = choose

instance RandomWord (RF.RVarT m) where
  randomWord = RF.sample . uncurry RF.Uniform

-- Transformer instances

instance  RandomWord m            => RandomWord (IdentityT      m)       where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (ReaderT        r m)     where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (Strict.StateT  s m)     where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (Lazy.StateT    s m)     where randomWord = lift . randomWord
instance (RandomWord m, Monoid w) => RandomWord (Strict.WriterT w m)     where randomWord = lift . randomWord
instance (RandomWord m, Monoid w) => RandomWord (Lazy.WriterT   w m)     where randomWord = lift . randomWord
instance (RandomWord m, Monoid w) => RandomWord (Strict.RWST    r w s m) where randomWord = lift . randomWord
instance (RandomWord m, Monoid w) => RandomWord (Lazy.RWST      r w s m) where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (ExceptT        e m)     where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (MaybeT         m)       where randomWord = lift . randomWord
instance  RandomWord m            => RandomWord (ContT          r m)     where randomWord = lift . randomWord
