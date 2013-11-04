{-# LANGUAGE GADTs, FlexibleInstances #-}
module Sif where

data SecLvl = Bot | Top
      deriving (Eq, Ord)
lo = (Bot, Top)
hi = (Top, Bot)

instance Show SecLvl where
      show Top = "top"
      show Bot = "bot"

class Loc ref where
      pos :: ref a -> Int
      lvl :: ref a -> SecLvl

data Ref a where
      Ref :: (ObjType a) => SecLvl -> Int -> Ref a
data RefR a where
      RefR :: (ObjType a) => SecLvl -> Int -> RefR a
data RefW a where
      RefW :: (ObjType a) => SecLvl -> Int -> RefW a

instance Loc Ref where
      pos (Ref _ x) = x
      lvl (Ref x _) = x
instance Loc RefR where
      pos (RefR _ x) = x
      lvl (RefR x _) = x
instance Loc RefW where
      pos (RefW _ x) = x
      lvl (RefW x _) = x

instance Loc r => Eq (r a) where
      x == y = pos x == pos y

data Var = Var String

-- Type annotations.
data T where
      TOne :: T
      TBool :: T
      TRef ::  SecLvl -> T -> T
      TRefR :: SecLvl -> T -> T
      TRefW :: SecLvl -> T -> T
      TFun :: T -> T -> T

instance Show T where
      show TOne = "1"
      show TBool = "bool"
      show (TRef lvl t) = "ref " ++ (show lvl) ++ " " ++ (show t)
      show (TRefR lvl t) = "refr " ++ (show lvl) ++ " " ++ (show t)
      show (TRefW lvl t) = "refw " ++ (show lvl) ++ " " ++ (show t)
      show (TFun a b) = (show a) ++ " -> " ++ (show b)

data V where
      VNull :: V
      VOne :: V
      VBool :: Bool -> V
      VT :: T -> V

class ObjType a where
      getV :: V -> a
      putV :: a -> V
      typeV :: a -> T
instance ObjType Bool where
      getV (VBool b) = b
      putV = VBool
      typeV = const TBool
instance ObjType () where
      getV (VOne) = ()
      putV = const VOne
      typeV = const TOne
instance ObjType T where -- TODO
      getV (VT t) = t
      putV = VT
      typeV t = t
instance (ObjType a, ObjType b) => ObjType (a -> b) where
      getV = undefined
      putV = undefined
      typeV f = undefined

data Term a where
      Const :: a -> Term a
      Val :: Exp a -> Term (O a)
      App :: Term (a -> b) -> Term a -> Term b
      Lam :: (Term a -> Term b) -> T -> Term (a -> b)
      If :: Term Bool -> Term a -> Term a -> Term a

data Exp a where
      Return :: Term a -> Exp a
      Read :: (ObjType a, Loc r) => Term (r a) -> Exp a
      Assign :: (ObjType a, Loc r)  => Term (r a) -> Term a -> Exp ()
      Alloc :: (ObjType a) => SecLvl -> Term a -> Exp (Ref a)
      Let :: Term (O a) -> (Term a -> Exp b) -> Exp b

data Store = Store {olvl :: (SecLvl, SecLvl),  sto :: Int -> V, nxtPos :: Int}
mut l v sto = \p -> if p == pos l then putV v else sto p
initStore = Store lo (const VNull) 0

instance Show Store where
      show s = "Store " ++ (show $ olvl s) ++ " " ++ (show $ nxtPos s)

data O a = O {run :: Store -> (Store, a)}

instance Monad O where
      return x = O $ \sto -> (sto {olvl = lo}, x)
      m >>= f = O $ \s -> 
            let (s', x) = run m s
            in run (f x) s'

alloc :: ObjType a => SecLvl -> a -> O (Ref a)
alloc secLvl v = O $ \s -> 
      let newRef = Ref secLvl (nxtPos s)
      in (Store lo (mut newRef v (sto s)) $ (nxtPos s) + 1, newRef)

newWLvl l (r, w) = (r, min (lvl l) w)
newRLvl l (r, w) = (max (lvl l) r, w)

set :: ObjType a => RefW a -> a -> O ()
set l v = O $ \s -> (Store (newWLvl l $ olvl s) (mut l v $ sto s) $ nxtPos s, ())

get :: ObjType a => RefR a -> O a
get l = O $ \s -> (Store (newRLvl l $ olvl s) (sto s) $ nxtPos s, getV $ sto s $ pos l)

toRefR :: (Loc r, ObjType a) => r a -> RefR a
toRefR r = RefR (lvl r) (pos r)

toRefW :: (Loc r, ObjType a) => r a -> RefW a
toRefW r = RefW (lvl r) (pos r)

evalT :: Term a -> a
evalT (Const x) = x
evalT (Val e) = evalE e
evalT (App f x) = (evalT f) (evalT x)
evalT (Lam f _) = \x -> evalT $ f $ Const x
evalT (If p b1 b2) = if evalT p then evalT b1 else evalT b2

evalE :: Exp a -> O a
evalE (Return t) = return $ evalT t
evalE (Read l) = get $ toRefR $ evalT l
evalE (Assign l v) = set (toRefW $ evalT l) (evalT v)
evalE (Alloc lvl v) = alloc lvl (evalT v)
evalE (Let m f) = (evalT m) >>= (\x -> evalE $ f (Const x))

--typeT :: ObjType a => Term a -> T
--typeT (Const x) =  typeV x
--typeT (App f x) = typeT $ evalT f $ evalT x -- TODO
--typeT (Lam f t) = TFun t $ (typeV f) t
--typeT (If p b1 b2) = typeT b1 -- TODO
--typeE :: ObjType a => Exp a -> O T
--typeE (Return t) = return (typeT t)

