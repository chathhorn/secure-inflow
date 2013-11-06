{-# LANGUAGE GADTs, 
             FlexibleInstances, 
             OverlappingInstances, 
             DeriveDataTypeable #-}

module SifShallow where

import Data.Dynamic
import Data.Maybe

data T = T deriving (Typeable)
data B = B deriving (Typeable)

data SecLvl = Bot | Top
      deriving (Eq, Ord, Show)

instance Ord (SecLvl, SecLvl) where
      (r, w) <= (r', w') = (r <= r') && (w' <= w)

lo = (Bot, Top)
hi = (Top, Bot)

--join :: (SecLvl, SecLvl) -> (SecLvl, SecLvl) -> (SecLvl, SecLvl)
join (Bot, Bot) (Top, Top) = hi
join (Top, Top) (Bot, Bot) = hi
join a b | a <= b = b
         | otherwise = a

data Ref s a where
      Ref :: (Typeable s, Typeable a) => Int -> Ref s a
      deriving (Typeable)

--pos :: Ref s a -> Int
pos (Ref x) = x

class Lvl a where
      lvl :: Ref a b -> SecLvl
instance Lvl B where
      lvl _ = Bot
instance Lvl T where
      lvl _ = Top

putV :: Typeable a => a -> Dynamic
putV = toDyn

getV :: Typeable a => Dynamic -> a
getV = fromJust . fromDynamic

data Store = Store {sto :: Int -> Dynamic, nxtPos :: Int}

tweak :: (Lvl s, Typeable a) => Ref s a -> a -> (Int -> Dynamic) -> Int -> Dynamic
tweak r v sto = \p -> if p == pos r then putV v else sto p

instance Show Store where
      show s = "Store " 
            ++ (show $ map (sto s) [0..(nxtPos s) - 1]) ++ " "
            ++ (show $ nxtPos s)

data O a where 
      O :: (Store -> (a, (SecLvl, SecLvl), Store)) -> O a
      deriving (Typeable)

run' :: O a -> Store -> (a, (SecLvl, SecLvl), Store)
run' (O s) = s

run :: Typeable a => O a -> Store -> (a, (SecLvl, SecLvl), Store)
run = run' . demote

instance Monad O where

      return x = O $ \sto -> (x, lo, sto)

      m >>= f = O $ \s -> 
            let (x, olvl, s') = run' m s
                (x', olvl', s'') = run' (f x) s'
            in (x', join olvl olvl', s'')

--informs :: Typeable a => SecLvl -> a -> Bool
informs Bot _ = True
informs Top a = informs' $ typeOf a

isBool x = x == typeOf True
isUnit x = x == typeOf ()
isRefT x = 
      (typeRepTyCon x) == (typeRepTyCon $ typeOf (undefined::Ref T ()))
      && (head $ typeRepArgs x) == (typeOf T)

--informs' :: TypeRep -> Bool
informs' t 
      | isBool t = False
      | isUnit t = True
      | isRefT t = True
      | otherwise = informs' $ last $ typeRepArgs t
      
--br :: (SecLvl, SecLvl) -> (SecLvl, SecLvl)
br (r, w) = (Bot, w)

--demote' :: Typeable a => (a, (SecLvl, SecLvl), Store) -> (a, (SecLvl, SecLvl), Store)
demote' (a, olvl, s) 
      | informs (fst olvl) a = (a, br olvl, s)
      | otherwise = (a, olvl, s)

demote :: (Typeable a) => O a -> O a
demote m = O $ \s -> demote' $ run' m s

alloc :: (Lvl s, Typeable s, Typeable a) => s -> a -> O (Ref s a)
alloc _ v = demote $ O $ \s -> 
      let newRef = Ref (nxtPos s)
      in (newRef, lo, Store (tweak newRef v (sto s)) $ (nxtPos s) + 1)

--(.=) :: (Lvl s, Typeable a) => Ref s a -> a -> O ()
r .= v = demote $ O $ \s -> ((), (Bot, (lvl r)), Store (tweak r v $ sto s) $ nxtPos s)

fetch :: (Lvl s, Typeable a) => Ref s a -> O a
fetch r = demote $ O $ \s -> (getV $ sto s $ pos r, (lvl r, Top), Store (sto s) $ nxtPos s)

initStore = Store (const $ putV (0::Int)) 0

-- Examples

-- O (T, B) Bool
fig260 :: O Bool
fig260 = do
      x <- alloc B False
      y <- alloc B False
      z <- do
            secret <- alloc T True
            q <- fetch secret
            return $ if q then x else y
      z .= True
      fetch x

-- O (T, T) Bool -> O (B, T) ()
fig5 :: O Bool -> O ()
fig5 c = do 
      wref <- alloc T $ return ()
      w <- return $ do 
            b <- c
            if b then (fetch wref >>= id) else return ()
      wref .= w
      w

