{-# LANGUAGE GADTs, 
             TypeOperators,
             DeriveDataTypeable,
             FlexibleContexts,
             FlexibleInstances #-}
module SifSyntax where

import SifSemantics
import Data.Typeable


type NOSEC = (H, L)

-- Type annotations.
data T where
      TOne :: T
      TBool :: T
      TRef ::  (SecLvl s) => s -> T -> T
      TRefR :: (SecLvl s) => s -> T -> T
      TRefW :: (SecLvl s) => s -> T -> T
      TFun :: T -> T -> T
      TO :: (OpLvl o) => o -> T -> T

instance Show T where
      show TOne = "1"
      show TBool = "bool"
      show (TRef lvl t) = "ref " ++ (show lvl) ++ " " ++ (show t)
      show (TRefR lvl t) = "refr " ++ (show lvl) ++ " " ++ (show t)
      show (TRefW lvl t) = "refw " ++ (show lvl) ++ " " ++ (show t)
      show (TFun a b) = (show a) ++ " -> " ++ (show b)

-- data Loc = Loc Int
--       deriving (Typeable)
-- data Var = Var Int
--       deriving (Eq, Typeable)
-- 
-- class Typeable t => ObjType t where
--       conT :: t -> Term
--       desT :: Term -> t
-- 
-- instance ObjType Var where
--       conT (Var x) = VX x
--       desT (VX x) = Var x
-- 
-- instance ObjType () where
--       conT _ = VU
--       desT _ = ()
-- 
-- instance ObjType Bool where
--       conT = VB
--       desT (VB b) = b
-- 
-- instance ObjType Loc where
--       conT (Loc x) = VL x
--       desT (VL x) = Loc x
-- 
-- instance ObjType (Exp Term) where
--       conT x = Do x
--       desT (Do x) = x
-- 
-- instance ObjType Term where
--       conT = id
--       desT = id
-- 
-- instance ObjType (Term -> Term) where
--       conT = undefined
--       desT (Abs x _ t) = \v -> subst x v t

data Val where 
      VB :: Bool -> Val 
      VU :: Val
      VL :: Int -> Val
      VF :: (Val -> Val) -> Val
      VO :: (O NOSEC Term) -> Val
      VR :: (SecLvl s) => Ref s Term -> Val
      deriving (Typeable)

data Term where
      Const :: Val -> Term
      Var :: Int -> Term
      Do :: Exp Term -> Term
      If :: Term -> Term -> Term -> Term
      App :: Term -> Term -> Term
      Abs :: Term -> T -> Term -> Term
      deriving (Typeable)

data Exp a where
      Return' :: a -> Exp a
      Return :: Term -> Exp Term
      Read :: Term -> Exp Term
      Write :: Term -> Term -> Exp Term
      Alloc :: (SecLvl s) => s -> Term -> Exp Term
      Let :: Exp a -> (a -> Exp b) -> Exp b
      deriving (Typeable)

instance Monad Exp where
      return = Return'
      (>>=) = Let

subst' :: Term -> Term -> Exp a -> Exp a
subst' x v (Return t) = Return $ subst x v t
subst' x v (Write l t) = Write l $ subst x v t
subst' x v (Alloc s t) = Alloc s $ subst x v t
subst' x v (Let e f) = Let (subst' x v e) $ \y -> subst' x v $ f y
subst' x v x' = x'

subst :: Term -> Term -> Term -> Term
subst x v (Do e) = Do $ subst' x v e
subst x v (If a b c) = If (subst x v a) (subst x v b) (subst x v c)
subst x v (App f a) = App (subst x v f) $ subst x v a
subst x v (Abs x' t f) = Abs x' t $ subst x v f
subst (Var x) v (Var x')
      | x == x' = v
      | otherwise = (Var x')
subst x v x' = x'

evalT :: Term -> Val
evalT (Const v) = v
evalT (If b x y) = 
      let (VB b') = evalT b
      in if b' then evalT x else evalT y
evalT (App x y) = 
      let (VF f) = evalT x
          v = evalT y

      in f v

evalT (Abs x _ t) = VF $ \v -> 
      evalT $ subst x (Const v) t

evalT (Do e) = evalE e

evalE :: Exp a -> Val
evalE (Return a) = VO $ ret a
evalE (Read r) = case (evalT r) of
      (VR r') -> VO $ deref r'

evalE (Write r v) = case (evalT r) of
      (VR r') -> VO $ Const $ r' .=  (evalT v)

--evalE (Alloc s a) = VO $ ref s $ evalT a
--evalE (Let m f) = VO $ (evalE m) >>= \x -> (evalE $ f x)

--typeT :: ObjType a => Term -> T
--typeT (Const x) =  typeV x
--typeT (App f x) = typeT $ evalT f $ evalT x -- TODO
--typeT (Lam f t) = TFun t $ (typeV f) t
--typeT (If p b1 b2) = typeT b1 -- TODO
--typeE :: ObjType a => Exp a -> O T
--typeE (Return t) = return (typeT t)

-- Examples

-- fig5 = 
--       Abs (\c -> 
--             Do (Let $ \wref ->
--                   

false = Const $ VB False
true = Const $ VB True
unit = Const VU

fig260 = do
      x <- Alloc L false
      y <- Alloc L false
      z <- do
            secret <- Alloc H false
            q <- Read secret
            Return $ If q x y
      Write z true
      Read x
      
