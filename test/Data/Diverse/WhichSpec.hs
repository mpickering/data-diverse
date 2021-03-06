{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Diverse.WhichSpec (main, spec) where

import Data.Diverse
import Data.Tagged
import Data.Typeable
import Test.Hspec

data Foo
data Bar
data Hi
data Bye

-- `main` is here so that this module can be run from GHCi on its own.  It is
-- not needed for automatic spec discovery.
main :: IO ()
main = hspec spec

-- | Utility to convert Either to Maybe
hush :: Either a b -> Maybe b
hush = either (const Nothing) Just

spec :: Spec
spec = do
    describe "Which" $ do

        it "is a Show" $ do
            let x = pickN @0 Proxy 5 :: Which '[Int, Bool]
            show x `shouldBe` "pickN @0 Proxy 5"

        it "is a Read and Show" $ do
            let s = "pickN @0 Proxy 5"
                x = read s :: Which '[Int, Bool]
            show x `shouldBe` s
            "impossible" `shouldBe` show impossible
            "impossible" `shouldBe` show (read "impossible" :: Which '[])

        it "is an Eq" $ do
            let y = pick (5 :: Int) :: Which '[Int, Bool]
            let y' = pick (5 :: Int) :: Which '[Int, Bool]
            y `shouldBe` y'
            read (show impossible) `shouldBe` impossible

        it "is an Ord" $ do
            let y5 = pick (5 :: Int) :: Which '[Int, Bool]
            let y6 = pick (6 :: Int) :: Which '[Int, Bool]
            compare y5 y5 `shouldBe` EQ
            compare y5 y6 `shouldBe` LT
            compare y6 y5 `shouldBe` GT
            compare impossible impossible `shouldBe` EQ

        it "can be constructed by type with 'pick' and destructed with 'trial'" $ do
            let y = pick (5 :: Int) :: Which '[Bool, Int, Char]
                x = hush $ trial @Int y
            x `shouldBe` (Just 5)

        it "can be constructed by label with 'pickL' and destructed with 'trialL'" $ do
            let y = pickL @Foo Proxy (Tagged (5 :: Int)) :: Which '[Bool, Tagged Foo Int, Tagged Bar Char]
                x = hush $ trialL @Foo Proxy y
            x `shouldBe` (Just (Tagged 5))

        it "may contain possiblities of duplicate types" $ do
            let y = pick (5 :: Int) :: Which '[Bool, Int, Char, Bool, Char]
                x = hush $ trial @Int y
            x `shouldBe` (Just 5)

        it "can be constructed conveniently with 'pick'' and destructed with 'trial0'" $ do
            let y = pickOnly (5 :: Int)
                x = hush $ trial0 y
            x `shouldBe` (Just 5)

        it "can be constructed by index with 'pickN' and destructed with 'trialN" $ do
            let y = pickN (Proxy @4) (5 :: Int) :: Which '[Bool, Int, Char, Bool, Int, Char]
                x = hush $ trialN (Proxy @4) y
            x `shouldBe` (Just 5)

        it "can be 'trial'led until its final 'obvious' value" $ do
            let a = pick @'[Char, Int, Bool, String] (5 :: Int)
                b = pick @'[Char, Int, String] (5 :: Int)
                c = pick @'[Int, String] (5 :: Int)
                d = pick @'[Int] (5 :: Int)
            trial @Int a `shouldBe` Right 5
            trial @Bool a `shouldBe` Left b
            trial @Int b `shouldBe` Right 5
            trial @Char b `shouldBe` Left c
            trial @Int c `shouldBe` Right 5
            trial @String c `shouldBe` Left d
            trial @Int d `shouldBe` Right 5
            trial @Int d `shouldNotBe` Left impossible
            obvious d `shouldBe` 5

        it "can be 'trialN'led until its final 'obvious' value" $ do
            let a = pickN @2 @'[Char, Bool, Int, Bool, Char, String] Proxy (5 :: Int)
                b = pickN @2 @'[Char, Bool, Int, Char, String] Proxy (5 :: Int)
                c = pickN @2 @'[Char, Bool, Int, String] Proxy (5 :: Int)
                d = pickN @1 @'[Bool, Int, String] Proxy (5 :: Int)
                e = pickN @1 @'[Bool, Int] Proxy (5 :: Int)
                f = pickN @0 @'[Int] Proxy (5 :: Int)
            trial @Int a `shouldBe` Right 5
            trialN @2 Proxy a `shouldBe` Right 5
            trialN @3 Proxy a `shouldBe` Left b

            trial @Int b `shouldBe` Right 5
            trialN @2 Proxy b `shouldBe` Right 5
            trialN @3 Proxy b `shouldBe` Left c

            trial @Int c `shouldBe` Right 5
            trialN @2 Proxy c `shouldBe` Right 5
            trial0 c `shouldBe` Left d
            trialN @0 Proxy c `shouldBe` Left d

            trial @Int d `shouldBe` Right 5
            trialN @1 Proxy d `shouldBe` Right 5
            trialN @2 Proxy d `shouldBe` Left e

            trial @Int e `shouldBe` Right 5
            trialN @1 Proxy e `shouldBe` Right 5
            trialN @0 Proxy e `shouldBe` Left f
            trial0 e `shouldBe` Left f

            trial @Int f `shouldBe` Right 5
            trial @Int f `shouldNotBe` Left impossible
            trial0 f `shouldBe` Right 5
            obvious f `shouldBe` 5

        it "can be extended and rearranged by type with 'diversify'" $ do
            let y = pickOnly (5 :: Int)
                y' = diversify @[Int, Bool] y
                y'' = diversify @[Bool, Int] y'
            switch y'' (CaseTypeable (show . typeRep . (pure @Proxy))) `shouldBe` "Int"

        it "can be extended and rearranged by type with 'diversify'" $ do
            let y = pickOnly (5 :: Tagged Bar Int)
                y' = diversifyL @'[Bar] Proxy y :: Which '[Tagged Bar Int, Tagged Foo Bool]
                y'' = diversifyL @'[Bar, Foo] Proxy y' :: Which '[Tagged Foo Bool, Tagged Bar Int]
            switch y'' (CaseTypeable (show . typeRep . (pure @Proxy))) `shouldBe` "Tagged * Bar Int"

        it "can be extended and rearranged by index with 'diversifyN'" $ do
            let y = pickOnly (5 :: Int)
                y' = diversifyN @'[0] @[Int, Bool] Proxy y
                y'' = diversifyN @[1,0] @[Bool, Int] Proxy y'
            switch y'' (CaseTypeable (show . typeRep . (pure @Proxy))) `shouldBe` "Int"

        it "the 'diversify'ed type can contain multiple fields if they aren't in the original 'Many'" $ do
            let y = pick @[Int, Char] (5 :: Int)
                x = diversify @[String, String, Char, Bool, Int] y
                -- Compile error: Char is a duplicate
                -- z = diversify @[String, String, Char, Bool, Int, Char] y
            x `shouldBe` pick (5 :: Int)

        it "the 'diversify'ed type can't use indistinct fields from the original 'Many'" $ do
            let y = pickN @0 @[Int, Char, Int] Proxy (5 :: Int) -- duplicate Int
                -- Compile error: Int is a duplicate
                -- x = diversify @[String, String, Char, Bool, Int] y
            y `shouldBe` y

        it "can be 'reinterpret'ed by type into a totally different Which" $ do
            let y = pick @[Int, Char] (5 :: Int)
                a = reinterpret @[String, Bool] y
            a `shouldBe` Left y
            let  b = reinterpret @[String, Char] y
            b `shouldBe` Left (pick (5 :: Int))
            let c = reinterpret @[String, Int] y
            c `shouldBe` Right (pick (5 :: Int))

        it "can be 'reinterpretL'ed by label into a totally different Which" $ do
            let y = pick @[Tagged Bar Int, Tagged Foo Bool, Tagged Hi Char, Tagged Bye Bool] (5 :: Tagged Bar Int)
                y' = reinterpretL @[Foo, Bar] Proxy y
                x = pick @[Tagged Foo Bool, Tagged Bar Int] (5 :: Tagged Bar Int)
            y' `shouldBe` Right x

        it "the 'reinterpret' type can contain indistinct fields if they aren't in the original 'Many'" $ do
            let y = pick @[Int, Char] (5 :: Int)
                x = reinterpret @[String, String, Char, Bool] y
                -- Compile error: Char is a duplicate
                -- z = reinterpret @[String, Char, Char, Bool] y
            x `shouldBe` Left (pick (5 :: Int))

        it "the 'reinterpret'ed from type can't indistinct fields'" $ do
            let y = pickN @0 @[Int, Char, Int] Proxy (5 :: Int) -- duplicate Int
                -- Compile error: Int is a duplicate
                -- x = reinterpret @[String, String, Char, Bool] y
            y `shouldBe` y

        it "the 'reinterpret' type can't use indistinct fields from the original 'Many'" $ do
            let y = pickN @0 @[Int, Char, Int] Proxy (5 :: Int) -- duplicate Int
                -- Compile error: Int is a duplicate
                -- x = reinterpret @[String, String, Char, Bool, Int] y
            y `shouldBe` y

        it "can be 'reinterpretN'ed by index into a subset Which" $ do
            let y = pick @[Char, String, Int, Bool] (5 :: Int)
                a = reinterpretN @[2, 0] @[Int, Char] Proxy y
                a' = reinterpretN @[3, 0] @[Bool, Char] Proxy y
            a `shouldBe` Just (pick (5 :: Int))
            a' `shouldBe` Nothing

        it "can be 'switch'ed with 'Many' handlers in any order" $ do
            let y = pickN @0 Proxy (5 :: Int) :: Which '[Int, Bool, Bool, Int]
            switch y (
                cases (show @Bool
                    ./ show @Int
                    ./ nil)) `shouldBe` "5"

        it "can be 'switch'ed with 'Many' handlers with extraneous content" $ do
            let y = pick (5 :: Int) :: Which '[Int, Bool]
            switch y (
                -- contrast with lowercase 'cases' which disallows extraneous content
                Cases (show @Int
                    ./ show @Bool
                    ./ show @Char
                    ./ 'X'
                    ./ False
                    ./ nil
                )) `shouldBe` "5"

        it "can be 'switchN'ed with 'Many' handlers in index order" $ do
            let y = pickN @0 Proxy (5 :: Int) :: Which '[Int, Bool, Bool, Int]
            switchN y (
                casesN (show @Int
                    ./ show @Bool
                    ./ show @Bool
                    ./ show @Int
                    ./ nil)) `shouldBe` "5"

        it "can be switched with a single 'CaseTypeable' handler" $ do
            let y = pick (5 :: Int) :: Which '[Int, Bool]
            switch y (CaseTypeable (show . typeRep . (pure @Proxy))) `shouldBe` "Int"
            (show . typeRep . (pure @Proxy) $ y) `shouldBe` "Which (': * Int (': * Bool '[]))"

        it "is a compile error to 'trial', 'diversify', 'reinterpret 'impossible'" $ do
            -- let a = diversify @[Int, Bool] impossible
            -- let a = trial @Int impossible
            -- let a = trialN (Proxy @0) impossible
            -- let a = reinterpret @[Int, Bool] impossible
            -- let a = reinterpretN (Proxy @'[0]) impossible
            impossible `shouldBe` impossible
