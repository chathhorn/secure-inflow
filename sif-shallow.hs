{-# LANGUAGE GADTs, 
             FlexibleInstances, 
             FlexibleContexts, 
             OverlappingInstances, 
             TypeOperators, 
             TypeFamilies, 
             MultiParamTypeClasses, 
             NoMonomorphismRestriction, 
             DeriveDataTypeable #-}

module SifShallow where

import Data.Dynamic
import Data.Maybe

data H = H deriving (Typeable)
data L = L deriving (Typeable)

class (Typeable s) => SecLvl s
instance SecLvl H
instance SecLvl L

class OpLvl o
instance (SecLvl r, SecLvl w) => OpLvl (r, w)

data Ref s a where
      Ref :: (SecLvl s, Typeable a) => Int -> Ref s a
      deriving (Typeable)

data RefR s a where
      RefR :: (SecLvl s, Typeable a) => Int -> RefR s a
      deriving (Typeable)

data RefW s a where
      RefW :: (SecLvl s, Typeable a) => Int -> RefW s a
      deriving (Typeable)

class Loc (r:: * -> * -> *)
instance Loc Ref
instance Loc RefR
instance Loc RefW

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

instance Show Store where
      show s = "Store " 
            ++ show (map (sto s) [0 .. nxtPos s - 1]) ++ " "
            ++ show (nxtPos s)

data O o a where 
      O :: (OpLvl o) => (Store -> (a, Store)) -> O o a
      deriving (Typeable)

run :: O o a -> Store -> (a, Store)
run (O f) = f

instance (OpLvl o) => Monad (O o) where
      return a = O $ \s -> (a, s)
      m >>= f = O $ \s ->
            let (a', s') = run m s
            in run (f a') s'

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

empty = Store (const $ putV (0::Int)) 0

class (Loc r, Loc r') => (r:: * -> * -> *) :<| (r':: * -> * -> *) where
      coerceRef :: (SecLvl s) => r s a -> r' s a

instance Ref :<| RefW where
      coerceRef (Ref p) = RefW p
instance Ref :<| RefR where
      coerceRef (Ref p) = RefR p

class (SecLvl s, SecLvl s') => s :< s'
instance L :< H
instance L :< L
instance H :< H

class (OpLvl o, OpLvl o') => o :<: o'
instance (r :< r', w' :< w) => (r, w) :<: (r', w')
instance (SecLvl r, SecLvl w) => (L, H) :<: (r, w)

class Demote r a
instance Demote r ()
instance Demote r (Ref r a)
instance Demote r (RefR r a)
instance Demote r (RefW r a)

deref' :: (SecLvl s, Typeable a, ref :<| RefR) => ref s a -> Store -> a
deref' r s = 
      let (RefR p) = coerceRef r
      in getV $ sto s $ p

deref :: (Typeable a, SecLvl s, r :<| RefR, (s, H) :<: o) => r s a -> O o a
deref r = O $ \s -> (deref' r s, s)

(.=) :: (Typeable a, SecLvl s, r :<| RefW, (L, s) :<: o) => r s a -> a -> O o ()
r .= v = O $ \s -> ((), tweak r v s)

ref :: (Typeable a, SecLvl s, (L, H) :<: o) => s -> a -> O o (Ref s a)
ref _ v = O $ \s ->
      let newRef = Ref (nxtPos s)
      in (newRef, tweak newRef v s)


ret :: ((L, H) :<: o) => a -> O o a
ret a = O $ \s -> (a, s)
-- 
-- Examples

fig260 :: O (H, L) Bool
fig260 = do
      x <- ref L False
      y <- ref L False
      z <- do
            secret <- ref H True
            q <- deref secret
            ret $ if q then x else y
      z .= True
      deref x

hiBool :: O (H, H) Bool
hiBool = ref H False >>= deref

fig5 :: O (H, H) Bool -> O (H, H) ()
fig5 c = do 
      wref <- ref H $ ret ()
      w <- ret $ do 
            b <- c
            if b then deref wref >>= id else ret ()
      wref .= w
      w


