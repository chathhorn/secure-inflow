{-# LANGUAGE GADTs, FlexibleInstances #-}
module SifSyntax where

import SifSemantics

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

data Term a where
      Const :: a -> Term a
      Val :: Exp a -> Term (O a)
      App :: Term (a -> b) -> Term a -> Term b
      Lam :: (Term a -> Term b) -> T -> Term (a -> b)
      If :: Term Bool -> Term a -> Term a -> Term a

data Exp a where
      Return :: Term a -> Exp a
      Read :: Term (r a) -> Exp a
      Assign :: Term (r a) -> Term a -> Exp ()
      Alloc :: s -> Term a -> Exp (Ref a)
      Let :: Term (O a) -> (Term a -> Exp b) -> Exp b

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

