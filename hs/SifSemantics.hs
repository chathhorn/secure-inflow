{-# LANGUAGE GADTs, 
             FlexibleInstances, 
             OverlappingInstances, 
             FlexibleContexts, 
             StandaloneDeriving, 
             ConstraintKinds, 
             TypeFamilies, 
             TypeOperators, 
             MultiParamTypeClasses, 
             NoMonomorphismRestriction, 
             DeriveDataTypeable #-}

module SifSemantics
      (O, H(..), L(..), SNITCH(..), OpLvl, SecLvl, run, ref, deref, (.=), ret, require, demote, empty,
      Ref, RefR, RefW,
      (:<), (:<:), (:<.)) where

import Data.Dynamic
import Data.Maybe
import GHC.Prim

data H = H deriving (Typeable, Show)
data L = L deriving (Typeable, Show)
data SNITCH = SNITCH deriving (Typeable, Show)

data Ref s a where
      Ref :: (SecLvl s, Typeable a) => Int -> Ref s a
      deriving (Typeable)
deriving instance Show (Ref s a)

data RefR s a where
      RefR :: (SecLvl s, Typeable a) => Int -> RefR s a
      deriving (Typeable)
deriving instance Show (RefR s a)

data RefW s a where
      RefW :: (SecLvl s, Typeable a) => Int -> RefW s a
      deriving (Typeable)
deriving instance Show (RefW s a)

putV :: Typeable a => a -> Dynamic
putV = toDyn

getV :: Typeable a => Dynamic -> a
getV = fromJust . fromDynamic

data Store = Store {sto :: Int -> Dynamic, nxtPos :: Int}

tweak :: (Typeable a, SecLvl s, r :< RefW) => r s a -> a -> Store -> Store
tweak r v (Store sto nxt) = 
      let (RefW p) = coerceRef r
          nxt' = if p == nxt then nxt + 1 else nxt
      in Store (\x -> if x == p then putV v else sto x) nxt'

lkup :: (SecLvl s, Typeable a, r :< RefR) => r s a -> Store -> a
lkup r s = 
      let (RefR p) = coerceRef r
      in getV $ sto s $ p

instance Show Store where
      show s = show (map (sto s) [0 .. nxtPos s - 1])

data O o a where 
      O :: (OpLvl o) => (Store -> (a, Store)) -> O o a
      deriving (Typeable)

run :: (OpLvl o) => O o a -> Store -> (a, Store)
run (O f) = f

empty = Store (const $ putV (0::Int)) 0

instance (OpLvl o) => Monad (O o) where
      return a = O $ \s -> (a, s)
      m >>= f = O $ \s ->
            let (a', s') = run m s
            in run (f a') s'

class r :< r' where
      coerceRef :: (SecLvl s) => r s a -> r' s a

instance Ref :< RefW where
      coerceRef (Ref p) = RefW p
instance Ref :< RefR where
      coerceRef (Ref p) = RefR p

instance RefW :< RefW where
      coerceRef = id
instance RefR :< RefR where
      coerceRef = id

class (Typeable s, Show s) => SecLvl s
instance SecLvl H
instance SecLvl L

class (SecLvl s, SecLvl s') => s :<. s'
instance L :<. H
instance L :<. L
instance H :<. H
instance (SecLvl s) => s :<. H
instance (SecLvl s) => L :<. s

class OpLvl o where
      olvl :: O o a -> o
instance OpLvl (L, H) where
      olvl _ = (L, H)
instance OpLvl (L, L) where
      olvl _ = (L, L)
instance OpLvl (H, H) where
      olvl _ = (H, H)
instance OpLvl SNITCH where
      olvl _ = SNITCH

class (OpLvl o, OpLvl o') => o :<: o'
instance (r :<. r', w' :<. w, OpLvl (r, w), OpLvl (r', w')) => (r, w) :<: (r', w')
instance (OpLvl o) => o :<: SNITCH

type family Demote a o o' :: Constraint

-- Demote OK.
type instance Demote () o o' = ()
type instance Demote (Ref H a) o o' = ()
type instance Demote (O (H, H) a) o o' = ()

-- Demote not OK.
type instance Demote Bool o o' = o ~ o'

-- Demote maybe OK.
type instance Demote (Ref L a) o o' = Demote a o o'
type instance Demote (O (L, w) a) o o' = Demote a o o'
type instance Demote (b -> a) o o' = Demote a o o'

demote :: (Demote a o o', OpLvl o, OpLvl o') => O o a -> O o' a
demote (O f) = O f

require :: (OpLvl o) => o -> O o a -> O o a
require _ = id

deref :: (Typeable a, SecLvl s, r :< RefR, (s, H) :<: o) => r s a -> O o a
deref r = O $ \s -> (lkup r s, s)

(.=) :: (Typeable a, SecLvl s, r :< RefW, (L, s) :<: o) => r s a -> a -> O o ()
r .= v = O $ \s -> ((), tweak r v s)

ref :: (Typeable a, SecLvl s, OpLvl o) => s -> a -> O o (Ref s a)
ref _ v = O $ \s ->
      let newRef = Ref (nxtPos s)
      in (newRef, tweak newRef v s)

ret :: (Typeable a, OpLvl o) => a -> O o a
ret a = O $ \s -> (a, s)

-- Examples

--fig260 :: O SNITCH Bool
fig260 = do
      x <- ref L False
      y <- ref L False
      z <- do
            secret <- ref H True
            q <- deref secret
            ret $ if q then x else y
      z .= True
      deref x

--hiBool :: O (H, H) Bool
hiBool = ref H False >>= deref

--fig5 :: O (H, H) Bool -> O (L, H) ()
fig5 c = do 
      wref <- ref H $ ret ()
      w <- ret $ do 
            b <- require (H, H) c
            if b then deref wref >>= id else ret ()
      wref .= w
      demote w

