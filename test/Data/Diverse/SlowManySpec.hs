module Data.Diverse.SlowManySpec (main, spec) where

import Data.Diverse
import Test.Hspec

-- `main` is here so that this module can be run from GHCi on its own.  It is
-- not needed for automatic spec discovery.
main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "Many" $ do

        it "is a Eq" $ do
            let a = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                b = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil

            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b
            a `shouldBe` b