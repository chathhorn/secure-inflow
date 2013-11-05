{-# LANGUAGE GADTs, FlexibleInstances, DeriveDataTypeable #-}
module SifShallow where

import Data.Dynamic
import Data.Maybe

data SecLvl = Bot | Top
      deriving (Eq, Ord, Show)

lo = (Bot, Top)
hi = (Top, Bot)

data Ref a where
      Ref :: SecLvl -> Int -> Ref a

pos :: Ref a -> Int
pos (Ref _ x) = x

lvl :: Ref a -> SecLvl
lvl (Ref x _) = x

putV :: Typeable a => a -> Dynamic
putV = toDyn

getV :: Typeable a => Dynamic -> a
getV = fromJust . fromDynamic

data Store = Store {olvl :: (SecLvl, SecLvl),  sto :: Int -> Dynamic, nxtPos :: Int}

mut :: Typeable a => Ref a -> a -> (Int -> Dynamic) -> Int -> Dynamic
mut r v sto = \p -> if p == pos r then putV v else sto p

instance Show Store where
      show s = "Store " ++ (show $ olvl s) ++ " " 
            ++ (show $ map (sto s) [0..(nxtPos s) - 1]) ++ " "
            ++ (show $ nxtPos s)

data O a = O {run :: Store -> (Store, a)}
      deriving (Typeable)

instance Monad O where
      return x = O $ \sto -> (sto {olvl = lo}, x)
      m >>= f = O $ \s -> 
            let (s', x) = run m s
            in run (f x) s'

alloc :: Typeable a => SecLvl -> a -> O (Ref a)
alloc secLvl v = O $ \s -> 
      let newRef = Ref secLvl (nxtPos s)
      in (Store lo (mut newRef v (sto s)) $ (nxtPos s) + 1, newRef)

(.=) :: Typeable a => Ref a -> a -> O ()
l .= v = O $ \s -> (Store (newWLvl l $ olvl s) (mut l v $ sto s) $ nxtPos s, ())

fetch :: Typeable a => Ref a -> O a
fetch l = O $ \s -> (Store (newRLvl l $ olvl s) (sto s) $ nxtPos s, getV $ sto s $ pos l)

newWLvl :: Ref a -> (SecLvl, SecLvl) -> (SecLvl, SecLvl)
newWLvl ref (r, w) = (r, min (lvl ref) w)

newRLvl :: Ref a -> (SecLvl, SecLvl) -> (SecLvl, SecLvl)
newRLvl ref (r, w) = (max (lvl ref) r, w)

initStore = Store lo (const $ putV (0::Int)) 0

-- Examples

fig5 :: O Bool -> O ()
fig5 c = do 
      wref <- alloc Bot $ return ()
      w <- return $ do 
            b <- c
            if b then (fetch wref >>= id) else return ()
      wref .= w
      w

