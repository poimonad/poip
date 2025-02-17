module Type where

import Prelude hiding (lookup)

import qualified Data.List as L (union, lookup)
import qualified Data.Map as M (Map, insert, lookup)
import Data.Maybe (isJust)
import Data.Foldable (find)

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

data Qual t = [Pred] :=> t deriving (Show, Eq)

data Pred = Constraint Id Type deriving (Show, Eq)

newtype Class = Class ([Id], [Inst]) deriving (Show, Eq)

newtype Inst = Qual Pred deriving (Show, Eq)

newtype ClassEnv = ClassEnv { classes :: M.Map Id Class } deriving (Show, Eq)

type ClassEnvTransformer = ClassEnv -> Either String ClassEnv

(+->) :: a -> b -> [(a, b)]
v +-> t = [(v, t)]

infixr 4 @@
(@@) :: Subst -> [(TyVar, Type)] -> [(TyVar, Type)]
s1 @@ s2 = [(v, apply s1 t) | (v, t) <- s2] ++ s1

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [TyVar]

-- apply ["a"->"b", "b"->t] "a"ってtになるほうが都合がいいと思ってたけど、H in Hの実装だと"b"になってた。一番簡略化されたやつになるほうがいいと思うんだけどなんでなんだろう
instance Types Type where
  apply s (TVar v) =
    case L.lookup v s of
      Just t -> t
      Nothing -> TVar v
  apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply _ t = t 

  tv (TVar v) = [v]
  tv (TApp l r) = tv l `L.union` tv r
  tv _ = []

class HasKind t where
  kind :: t -> Maybe Kind

instance HasKind TyVar where
  kind (TyVar _ k) = Just k

instance HasKind TyCon where
  kind (TyCon _ k) = Just k

instance HasKind Type where
  kind (TVar v) = kind v
  kind (TCon c) = kind c
  kind (TApp t _) = 
    case kind t of
      Just (Kfun _ k) -> Just k
      _ -> Nothing
  kind (TGen _) = Nothing
  

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

addClass :: Id -> [Id] -> ClassEnvTransformer
addClass i is ce
  | defined i ce = Left $ "class " ++ show i ++ " is already defined."
  | (not . all (`defined` ce)) is = 
      case find (not . (`defined` ce)) is of
        Just s -> Left $ "super class " ++ show s ++ " is not defined."
  | otherwise = return ce { classes = M.insert i (Class (is, [])) $ classes ce }

defined :: Id -> ClassEnv -> Bool
defined i ce = isJust . M.lookup i $ classes ce