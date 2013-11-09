{-# LANGUAGE GADTs, 
             FlexibleInstances, 
             OverlappingInstances, 
             FlexibleContexts, 
             TypeOperators, 
             MultiParamTypeClasses, 
             NoMonomorphismRestriction, 
             DeriveDataTypeable #-}

module SifSemantics
      (O, H(H), L(L), OpLvl, SecLvl, run, ref, deref, (.=), ret, require, demote, empty,
      Ref, RefR, RefW,
      (:<|), (:<:), (:<)) where

import Data.Dynamic
import Data.Maybe

data H = H deriving (Typeable, Show)
data L = L deriving (Typeable, Show)

data Ref s a where
      Ref :: (SecLvl s, Typeable a) => Int -> Ref s a
      deriving (Typeable)

data RefR s a where
      RefR :: (SecLvl s, Typeable a) => Int -> RefR s a
      deriving (Typeable)

data RefW s a where
      RefW :: (SecLvl s, Typeable a) => Int -> RefW s a
      deriving (Typeable)

putV :: Typeable a => a -> Dynamic
putV = toDyn

getV :: Typeable a => Dynamic -> a
getV = fromJust . fromDynamic

data Store = Store {sto :: Int -> Dynamic, nxtPos :: Int}

tweak :: (Typeable a, SecLvl s, r :<| RefW) => r s a -> a -> Store -> Store
tweak r v (Store sto nxt) = 
      let (RefW p) = coerceRef r
          nxt' = if p == nxt then nxt + 1 else nxt
      in Store (\x -> if x == p then putV v else sto x) nxt'

lkup :: (SecLvl s, Typeable a, r :<| RefR) => r s a -> Store -> a
lkup r s = 
      let (RefR p) = coerceRef r
      in getV $ sto s $ p

instance Show Store where
      show s = show (map (sto s) [0 .. nxtPos s - 1])

data O o a where 
      O :: (OpLvl o) => (Store -> (a, Store)) -> O o a
      deriving (Typeable)


run' :: (OpLvl o) => O o a -> Store -> (a, Store)
run' (O f) = f

run :: (OpLvl o) => o -> O o a -> Store -> (a, Store)
run _ (O f) = f

empty = Store (const $ putV (0::Int)) 0

instance (OpLvl o) => Monad (O o) where
      return a = O $ \s -> (a, s)
      m >>= f = O $ \s ->
            let (a', s') = run' m s
            in run' (f a') s'

-- informs :: Typeable a => SecLvl -> a -> Bool
-- informs Lo _ = True
-- informs Hi a = informs' $ typeOf a
-- 
-- isBool x = x == typeOf True
-- isUnit x = x == typeOf ()
-- isRefH x = 
--       typeRepTyCon x == typeRepTyCon (typeOf (undefined::Ref H ()))
--       && head (typeRepArgs x) == typeOf H
-- 
-- informs' :: TypeRep -> Bool
-- informs' t 
--       | isBool t = False
--       | isUnit t = True
--       | isRefH t = True
--       | otherwise = informs' $ last $ typeRepArgs t
--       
-- demote :: Typeable a => (a, (SecLvl, SecLvl), Store) -> (a, (SecLvl, SecLvl), Store)
-- demote (a, (r, w), s) 
--       | informs r a = (a, (Lo, w), s)
--       | otherwise = (a, (r, w), s)

class r :<| r' where
      coerceRef :: (SecLvl s) => r s a -> r' s a

instance Ref :<| RefW where
      coerceRef (Ref p) = RefW p
instance Ref :<| RefR where
      coerceRef (Ref p) = RefR p

instance RefW :<| RefW where
      coerceRef = id
instance RefR :<| RefR where
      coerceRef = id

class (Typeable s, Show s) => SecLvl s
instance SecLvl H
instance SecLvl L

class (SecLvl s, SecLvl s') => s :< s'
instance L :< H
instance L :< L
instance H :< H
instance (SecLvl s) => s :< H
instance (SecLvl s) => L :< s

data SNITCH = SNITCH

class OpLvl o
instance (SecLvl r, SecLvl w, r :< w) => OpLvl (r, w)
instance OpLvl SNITCH

class (OpLvl o, OpLvl o') => o :<: o'
instance (r :< r', w' :< w, OpLvl (r, w), OpLvl (r', w')) => (r, w) :<: (r', w')
instance (OpLvl o) => o :<: SNITCH

deref :: (Typeable a, SecLvl s, r :<| RefR, (s, H) :<: o) => r s a -> O o a
deref r = O $ \s -> (lkup r s, s)

(.=) :: (Typeable a, SecLvl s, r :<| RefW, (L, s) :<: o) => r s a -> a -> O o ()
r .= v = O $ \s -> ((), tweak r v s)

ref :: (Typeable a, SecLvl s, OpLvl o) => s -> a -> O o (Ref s a)
ref _ v = O $ \s ->
      let newRef = Ref (nxtPos s)
      in (newRef, tweak newRef v s)

ret :: (Typeable a, (L, H) :<: o) => a -> O o a
ret a = O $ \s -> (a, s)

require :: (o :<: o') => o' -> O o a -> O o' a
require _ (O f) = O f

demote :: (SecLvl r, SecLvl w, (L, w) :<: o) => O (r, w) a -> O o a
demote (O f) = O f

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
            b <- c
            if b then deref wref >>= id else ret ()
      wref .= w
      demote w

--data Sup m o a m' o' a'

-- instance (o :<: o') => Sup m o a m o' a
-- instance (Sup ) => Sup m o a m o' a

-- A < A' and B' < B => A' -> B' < A -> B
--
-- RefR -> Ref  <  Ref -> RefR
-- RefR -> RefR  <  Ref -> RefR
-- RefR -> Ref  <  RefR -> RefR
--
-- RefR -> Ref  <  Ref -> RefW
-- RefW -> Ref  <  Ref -> RefW
-- RefW -> Ref  <  Ref -> RefR
fun c = do
      f <- c
      ret (f (Ref 3))


