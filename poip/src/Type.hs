module Type where

import Data.List (union)

data Kind
  = Star
  | Kfun Kind Kind
  deriving (Eq, Show)

data Type
  = TVar TyVar
  | TCon TyCon
  | TApp Type Type
  | TGen Int
  deriving (Eq, Show)

data TyVar = TyVar Id Kind deriving (Eq, Show)
data TyCon = TyCon Id Kind deriving (Eq, Show)

type Id = String

type Subst = [(TyVar, Type)]

v +-> t = [(v, t)]

infixr 4 @@
s1 @@ s2 = [(v, apply s1 t) | (v, t) <- s2] ++ s1

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [TyVar]

-- apply ["a"->"b", "b"->t] "a"ってtになるほうが都合がいいと思ってたけど、H in Hの実装だと"b"になってた。一番簡略化されたやつになるほうがいいと思うんだけどなんでなんだろう
instance Types Type where
  apply s (TVar v) =
    case lookup v s of
      Just t -> t
      Nothing -> TVar v
  apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply s t = t 

  tv (TVar v) = [v]
  tv (TApp l r) = tv l `union` tv r
  tv t = []

class HasKind t where
  kind :: t -> Maybe Kind

instance HasKind TyVar where
  kind (TyVar t k) = Just k

instance HasKind TyCon where
  kind (TyCon t k) = Just k

instance HasKind Type where
  kind (TVar v) = kind v
  kind (TCon c) = kind c
  kind (TApp t _) = 
    case kind t of
      Just (Kfun _ k) -> Just k
      _ -> Nothing

mgu :: Type -> Type -> Either String Subst
mgu (TApp l1 r1) (TApp l2 r2) = do
  s1 <- mgu l1 l2
  s2 <- mgu (apply s1 r1) (apply s1 r2)
  return $ s1 @@ s2
mgu (TCon c1) (TCon c2) | c1 == c2 = return []
mgu (TVar v) t = mguVar v t
mgu t (TVar v) = mguVar v t
mgu t1 t2 = Left $ "type " ++ show t1 ++ " and " ++ show t2 ++ " is can not be unified!"

mguVar :: TyVar -> Type -> Either String Subst
mguVar v t
  | TVar v == t       = return []
  | v `elem` tv t     = Left "occures"
  | kind v /= kind t  = Left "kind do not match" 
  | otherwise         = return $ v +-> t