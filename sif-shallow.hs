{-# LANGUAGE GADTs, 
             FlexibleInstances, 
             OverlappingInstances, 
             DeriveDataTypeable #-}

module SifShallow where

import Data.Dynamic
import Data.Maybe

data H = H deriving (Typeable)
data L = L deriving (Typeable)

data SecLvl = Lo | Hi
      deriving (Eq, Ord, Show)

instance Ord (SecLvl, SecLvl) where
      (r, w) <= (r', w') = (r <= r') && (w' <= w)

lo = (Lo, Hi)
hi = (Hi, Lo)

--join :: (SecLvl, SecLvl) -> (SecLvl, SecLvl) -> (SecLvl, SecLvl)
join (Lo, Lo) (Hi, Hi) = hi
join (Hi, Hi) (Lo, Lo) = hi
join a b | a <= b = b
         | otherwise = a

data Ref s a where
      Ref :: (Typeable s, Typeable a) => Int -> Ref s a
      deriving (Typeable)

--pos :: Ref s a -> Int
pos (Ref x) = x

class Lvl a where
      lvl :: Ref a b -> SecLvl
instance Lvl L where
      lvl _ = Lo
instance Lvl H where
      lvl _ = Hi

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
informs Lo _ = True
informs Hi a = informs' $ typeOf a

isBool x = x == typeOf True
isUnit x = x == typeOf ()
isRefH x = 
      (typeRepTyCon x) == (typeRepTyCon $ typeOf (undefined::Ref H ()))
      && (head $ typeRepArgs x) == (typeOf H)

--informs' :: TypeRep -> Bool
informs' t 
      | isBool t = False
      | isUnit t = True
      | isRefH t = True
      | otherwise = informs' $ last $ typeRepArgs t
      
--br :: (SecLvl, SecLvl) -> (SecLvl, SecLvl)
br (r, w) = (Lo, w)

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
r .= v = demote $ O $ \s -> ((), (Lo, (lvl r)), Store (tweak r v $ sto s) $ nxtPos s)

fetch :: (Lvl s, Typeable a) => Ref s a -> O a
fetch r = demote $ O $ \s -> (getV $ sto s $ pos r, (lvl r, Hi), Store (sto s) $ nxtPos s)

empty = Store (const $ putV (0::Int)) 0

-- Examples

-- O (H, L) Bool
fig260 :: O Bool
fig260 = do
      x <- alloc L False
      y <- alloc L False
      z <- do
            secret <- alloc H True
            q <- fetch secret
            return $ if q then x else y
      z .= True
      fetch x

hiBool :: O Bool
hiBool = alloc H False >>= fetch

-- O (H, H) Bool -> O (L, H) ()
fig5 :: O Bool -> O ()
fig5 c = do 
      wref <- alloc H $ return ()
      w <- return $ do 
            b <- c
            if b then (fetch wref >>= id) else return ()
      wref .= w
      w

