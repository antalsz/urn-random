{-# LANGUAGE DefaultSignatures #-}

module Data.Urn.MonadSample (MonadSample(..)) where

import Control.Monad.Random
import Test.QuickCheck

-- Transformers
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

class Monad m => MonadSample m where
  randomWord :: (Word,Word) -> m Word
  default randomWord :: MonadRandom m => (Word,Word) -> m Word
  randomWord = getRandomR

instance MonadSample IO
instance (Monad m, RandomGen g) => MonadSample (RandT g m)

instance MonadSample Gen where
  randomWord = choose

-- Transformer instances

instance  MonadSample m            => MonadSample (IdentityT      m)       where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (ReaderT        r m)     where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (Strict.StateT  s m)     where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (Lazy.StateT    s m)     where randomWord = lift . randomWord
instance (MonadSample m, Monoid w) => MonadSample (Strict.WriterT w m)     where randomWord = lift . randomWord
instance (MonadSample m, Monoid w) => MonadSample (Lazy.WriterT   w m)     where randomWord = lift . randomWord
instance (MonadSample m, Monoid w) => MonadSample (Strict.RWST    r w s m) where randomWord = lift . randomWord
instance (MonadSample m, Monoid w) => MonadSample (Lazy.RWST      r w s m) where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (ExceptT        e m)     where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (MaybeT         m)       where randomWord = lift . randomWord
instance  MonadSample m            => MonadSample (ContT          r m)     where randomWord = lift . randomWord
