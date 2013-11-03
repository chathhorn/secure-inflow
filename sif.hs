{-# LANGUAGE GADTs #-}
module Sif where

data SecLvl = Top | Bot
      deriving (Show)

data Loc a where
      Loc :: (StoreV a) => SecLvl -> Int -> Loc a
pos (Loc _ x) = x
instance Eq (Loc a) where
      x == y = pos x == pos y

-- data O a where
      -- O :: Exp a -> O a
      --O :: SecLvl -> SecLvl -> a -> O a

data Ref a where
      Ref :: SecLvl -> a -> Ref a
data RefR a where
      RefR :: SecLvl -> a -> RefR a
data RefW a where
      RefW :: SecLvl -> a -> RefW a

data Var = Var String

-- Type annotations.
-- data AType where
--       AOne :: AType
--       ABool :: AType
--       ARef ::  SecLvl -> AType -> AType
--       ARefR :: SecLvl -> AType -> AType
--       ARefW :: SecLvl -> AType -> AType
--       AO :: SecLvl -> SecLvl -> AType -> AType
--       AFun :: AType -> AType -> AType
--       deriving (Show)
      
data Term a where
      Const :: a -> Term a
      Val :: Exp a -> Term (O a)
      App :: Term (a -> b) -> Term a -> Term b
      Lam :: (Term a -> Term b) -> Term (a -> b)
      If :: Term Bool -> Term a -> Term a -> Term a

data Exp a where
      Return :: Term a -> Exp a
      Read :: StoreV a => Term (Loc a) -> Exp a
      Assign :: StoreV a => Term (Loc a) -> Term a -> Exp ()
      Alloc :: StoreV a => SecLvl -> Term a -> Exp (Loc a)
      Let :: Term (O a) -> (a -> Exp b) -> Exp b

data V = VBool Bool | VOne
class StoreV a where
      getV :: V -> a
      putV :: a -> V
instance StoreV Bool where
      getV (VBool b) = b
      putV = VBool
instance StoreV () where
      getV (VOne) = ()
      putV () = VOne

data Store where 
      Store :: (Int -> V) -> Int -> Store
mut l v sto = \p -> if p == pos l then putV v else sto p

newtype O a = O {run :: Store -> (Store, a)}

instance Monad O where
      return x = O $ \sto -> (sto, x)
      s >>= f = O $ \sto -> 
            let (sto', x) = run s sto
            in run (f x) sto'

alloc :: StoreV a => SecLvl -> a -> O (Loc a)
alloc lvl v = O $ \(Store sto nxtPos) -> 
      let newLoc = Loc lvl nxtPos
      in (Store (mut newLoc v sto) (nxtPos + 1), newLoc)

set :: StoreV a => Loc a -> a -> O ()
set l v = O $ \(Store sto nxtPos) -> (Store (mut l v sto) nxtPos, ())

get :: StoreV a => Loc a -> O a
get l = O $ \(Store sto nxtPos) -> (Store sto nxtPos, getV $ sto $ pos l)

evalT :: Term a -> a
evalT (Const x) = x
evalT (Val e) = evalE e
evalT (App f x) = (evalT f) (evalT x)
evalT (Lam f) = \x -> evalT $ f $ Const x
evalT (If p b1 b2) = if evalT p then evalT b1 else evalT b2

evalE :: Exp a -> O a
evalE (Return t) = return (evalT t)
evalE (Read l) = get (evalT l)
evalE (Assign l v) = set (evalT l) (evalT v)
evalE (Alloc lvl v) = alloc lvl (evalT v)
evalE (Let m f) = (evalT m) >>= (\x -> evalE $ f x)

