module TypeSpec (spec) where

-- import Test.Hspec (it, describe, Spec, Expectation, shouldBe, shouldSatisfy)
-- import Text.Parsec
-- import Text.Parsec.String


import Type
import Data.Either (isLeft, fromRight)
import Control.Monad ((>=>))


spec :: Spec
spec = do
  mapM_ (\(n, p) ->
            describe n $ do
              mapM_ (uncurry it) p
    ) tests

tests :: [(String, [(String, Expectation)])]
tests = [
    ("Subst application", [
      ("", apply [(a, tPrim)] (TVar a) `shouldBe` tPrim)
      , ("", apply [(a, TVar b), (b, tPrim)] (TVar a) `shouldBe` TVar b)
    ])
    , ("Subst composition", [
        ("", [(a, tPrim)] @@ [(b, TVar a)] `shouldBe` [(b, tPrim), (a, tPrim)])
        , ("", [(b, TVar a)] @@ [(a, tPrim)] `shouldBe` [(a, tPrim), (b, TVar a)])
    ])
    , ("Most general unification", [
        ("", mgu (TVar a) tPrim `shouldBe` Right (a +-> tPrim))
        , ("", mgu (t (TVar a)) (t tPrim) `shouldBe` Right (a +-> tPrim))
        , ("", shouldErr $ mgu (TCon (TyCon "u" Star)) (TCon (TyCon "u" (Kfun Star Star))))
        , ("occur check: unification 'a' and 't a' is occurency case", shouldErr $ mgu (TVar a) (t (TVar a)))
    ])
    , ("Class", [
        ("Super class defination", 
            shouldErr $ (
                addClass "Eq" [] 
                >=> addClass "Int" ["Eq", "Show"]
            ) emptyClass)
        , ("Duplicate class declaration", 
            shouldErr $ (
                addClass "Eq" [] 
                >=> addClass "Eq" []
            ) emptyClass)
        , ("Fetch Super Class", 
            (super "Int" <$> (
                addClass "Eq" [] 
                >=> addClass "Int" ["Eq"]) 
            emptyClass) `shouldBe` Right (Right ["Eq"]))
    ])
    , ("Instance", [
        ("No Class For Instance", 
            shouldErr $ addInst [Constraint "Eq" tPrim] (Constraint "Ord" tPrim) emptyClass)
        , ("Overlap Instance", shouldErr $ (addClass "Eq" [] >=> addClass "Ord" [] >=> addInst [Constraint "Eq" tPrim] (Constraint "Ord" tPrim) >=> addInst [Constraint "Eq" (TVar a)] (Constraint "Ord" (TVar a))) emptyClass)
    ])
    , ("Fetch Super Class", [
        ("", (bySuper <$> pure (Constraint "Ord" tPrim) <*> ((addClass "Eq" [] >=> addClass "Ord" ["Eq"]) emptyClass)) `shouldBe` Right [Constraint "Ord" (TCon (TyCon "prim" Star)),Constraint "Eq" (TCon (TyCon "prim" Star))])
    ])
    , ("Fetch Instance", [
        ("", byInst (Constraint "Eq" (t tPrim)) (unsafeRunClass (addClass "Eq" [] >=> addInst [Constraint "Eq" (TVar a)] (Constraint "Eq" (t $ TVar a)))) `shouldBe` Right [Constraint "Eq" tPrim])
    ])
    , ("Class Entailment", [
        ("", (entail (unsafeRunClass $ tClassEnv) [] (Constraint "Eq" tPrim)) `shouldBe` True)
        , ("", entail (unsafeRunClass (addClass "Eq" [] >=> addInst [] (Constraint "Eq" tPrim) >=> addInst [Constraint "Eq" (TVar a)] (Constraint "Eq" (t (TVar a))))) [] (Constraint "Eq" (t tPrim)) `shouldBe` True)
    ])
  ]

unsafeRunClass ce = case ce emptyClass of Right ce' -> ce'

tClassEnv = (addClass "Eq" [] >=> addClass "Ord" ["Eq"])

-- tPrim :: Type
tPrim = TCon (TyCon "prim" Star)

t :: Type -> Type
t = TApp (TCon (TyCon "t" (Kfun Star Star)))

tyv :: Id -> TyVar
tyv u = TyVar u Star 

a :: TyVar
a = tyv "a"

b :: TyVar
b = tyv "b"

emptyClass = ClassEnv { classes = mempty }

shouldErr :: (Show a, Show b) => Either a b -> Expectation
shouldErr v = v `shouldSatisfy` isLeft

-- parseEnv =
--   parseClass

-- -- parseClass :: Parser String
-- parseClass = do 
--   _ <- string "Class"
--   lift $ addClass "" []