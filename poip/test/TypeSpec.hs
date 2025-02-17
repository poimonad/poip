module TypeSpec (spec) where

import Test.Hspec (it, describe, Spec, Expectation, shouldBe, shouldSatisfy)
import Type
import Data.Either (isLeft)
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
      ("Super class defination", shouldErr $ (addClass "Eq" [] >=> addClass "Int" ["Eq", "Show"]) emptyClass)
      , ("Duplicate class declaration", shouldErr $ (addClass "Eq" [] >=> addClass "Eq" []) emptyClass)
    ])
  ]

tPrim :: Type
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