module TypeSpec (spec) where

import Test.Hspec (it, describe, Spec, Expectation, shouldBe, shouldSatisfy)
import Type
import Data.Either (isLeft)

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
  ]

tPrim = TCon (TyCon "prim" Star)

-- a -> 't a'
t = TApp (TCon (TyCon "t" (Kfun Star Star)))

tyv u = TyVar u Star 

a = tyv "a"
b = tyv "b"

shouldErr a = a `shouldSatisfy` isLeft
