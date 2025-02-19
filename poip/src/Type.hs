module Type where

import Prelude hiding (lookup)

import qualified Data.List as L (union, lookup)
import qualified Data.Map as M (Map, insert, lookup)
import Data.Maybe (isJust)
import Data.Foldable (find, msum)
import Data.Either (isRight)
import Data.List (intersect)

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

type Class = ([Id], [Inst])

type Inst = Qual Pred

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

instance Types Pred where
  apply s (Constraint i t) = Constraint i $ apply s t
  tv (Constraint _ t) = tv t

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

merge :: Subst -> Subst -> Either String Subst
merge s1 s2 = if agree then return (s1++s2) else Left "merge"
   where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                     (fmap fst s1 `intersect` fmap fst s2)

match :: Type -> Type -> Either String Subst
match (TApp l1 r1) (TApp l2 r2) = do
  sl <- match l1 l2
  sr <- match r1 r2
  sl `merge` sr
match (TVar v) t | kind v == kind t = return $ v +-> t
match (TCon c1) (TCon c2) | c1 == c2 = return []
match _ _ = Left "match: fail"

mguPred :: Pred -> Pred -> Either String Subst
mguPred (Constraint i1 t1) (Constraint i2 t2)
  | i1 == i2 = mgu t1 t2
  | otherwise = Left $ show i1 ++ " and " ++ show i2 ++ " is different class"

super :: Id -> ClassEnv -> Either String [Id]
super i ce = 
  case M.lookup i (classes ce) of
    Just  (is, _) -> Right is
    Nothing -> Left "super class not found"

insts :: Id -> ClassEnv -> Either String [Inst]
insts i ce = 
  case M.lookup i (classes ce) of
    Just (_, its) -> Right its
    Nothing -> Left "instance not found"

addClass :: Id -> [Id] -> ClassEnvTransformer
addClass i is ce
  | defined i ce = Left $ "class " ++ show i ++ " is already defined."
  | (not . all (`defined` ce)) is = 
      case find (not . (`defined` ce)) is of
        Just s -> Left $ "super class " ++ show s ++ " is not defined."
  | otherwise = return ce { classes = M.insert i (is, []) $ classes ce }

addInst :: [Pred] -> Pred -> ClassEnvTransformer
addInst ps p@(Constraint i _) ce = do
  its <- insts i ce
  super' <- super i ce
  let c = (super', (ps :=> p) : its)
  let qs = [ q | (_ :=> q) <- its]
  if not (defined i ce) then
    Left $ "no class for instance " ++ show i 
  else if any (overlap p) qs then
    Left $ "class " ++ show p ++ " is overlap"
  else
    return (ce { classes = M.insert i c (classes ce) })

overlap :: Pred -> Pred -> Bool
overlap p q = isRight (mguPred p q)

defined :: Id -> ClassEnv -> Bool
defined i ce = isJust . M.lookup i $ classes ce

-- あるクラスのインスタンス宣言からスーパークラスをRollup抽出
bySuper :: Pred -> ClassEnv -> [Pred]
bySuper p@(Constraint i t) ce = do
  case super i ce of
    Right is -> p : concat [ bySuper (Constraint i' t) ce | i' <- is ]
    Left _ -> [p]

byInst :: Pred -> ClassEnv -> Either String [Pred]
byInst p@(Constraint i _) ce = do
   its <- insts i ce
   concat <$> mapM tryInst its
  where
    tryInst :: Inst -> Either String [Pred]
    tryInst (ps :=> h) = do
      case mguPred h p of
        Right u -> Right $ map (apply u) ps
        Left _ -> Right []
    -- これ罠
    -- 型代入がないということは、型が成り立つためにこれ以上証明するべきものがないということ

entail :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (p `elem`) (map (`bySuper` ce) ps) ||
  case byInst p ce of
    Left _ -> False
    Right qs -> all (entail ce ps) qs

infixr 0 <#>
(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip (<$>)