{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Diverse.ManySpec (main, spec) where

import Data.Diverse
import Data.Tagged
import Data.Typeable
import Test.Hspec

-- `main` is here so that this module can be run from GHCi on its own.  It is
-- not needed for automatic spec discovery.
main :: IO ()
main = hspec spec

data Foo
data Bar

spec :: Spec
spec = do
    describe "Many" $ do
        it "is a Typeable" $ do
            let x = (5 :: Int) ./ False ./ nil
                y = cast x :: Maybe (Many '[Int, String])
                z = cast x :: Maybe (Many '[Int, Bool])
            y `shouldBe` Nothing
            z `shouldBe` Just x
            (show . typeRep . (pure @Proxy) $ x) `shouldBe` "Many (': * Int (': * Bool '[]))"

        it "is a Read and Show" $ do
            let s = "5 ./ False ./ 'X' ./ Just 'O' ./ nil"
                s' = "5 ./ False ./ 'X' ./ (Just 'O' ./ (nil))"
                x = read s :: Many '[Int, Bool, Char, Maybe Char]
                x' = read s' :: Many '[Int, Bool, Char, Maybe Char]
            show x `shouldBe` s
            show x' `shouldBe` s

        it "is a Eq" $ do
            let s = "5 ./ False ./ 'X' ./ Just 'O' ./ nil"
                x = read s :: Many '[Int, Bool, Char, Maybe Char]
                y = 5 ./ False ./ 'X' ./ Just 'O' ./ nil
            x `shouldBe` y

        it "is an Ord" $ do
            let s = "5 ./ False ./ 'X' ./ Just 'O' ./ nil"
                x = read s :: Many '[Int, Bool, Char, Maybe Char]
                y5o = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                y4o = (4 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                y5p = (5 :: Int) ./ False ./ 'X' ./ Just 'P' ./ nil
            compare x y5o `shouldBe` EQ
            compare y4o y5o `shouldBe` LT
            compare y5o y4o `shouldBe` GT
            compare y5o y5p `shouldBe` LT
            compare y5p y5o `shouldBe` GT

        it "can converted to and from a tuple" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                t = ((5 :: Int), False, 'X', Just 'O')
            x `shouldBe` toMany' t
            t `shouldBe` fromMany' x

        it "can construct using 'single', 'nil', 'prefix', 'postfix', 'append'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                x' = (5 :: Int) `prefix` False `prefix` 'X' `prefix` Just 'O' `prefix` nil
                y = single (5 :: Int) \. False \. 'X' \. Just 'O'
                y' = single (5 :: Int) `postfix` False `postfix` 'X' `postfix` Just 'O'
                a = single (5 :: Int) `postfix` False
                b = single 'X' `postfix` Just 'O'
            x `shouldBe` y
            x `shouldBe` x'
            y `shouldBe` y'
            a /./ b `shouldBe` x
            a `append` b `shouldBe` x

        it "can contain multiple fields of the same type" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
                y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            (x /./ (6 :: Int) ./ Just 'A' ./ nil) `shouldBe` y

        it "can destruct using 'front', 'back', 'aft', 'fore'" $ do
            let a = (x ./ y) \. z
                x = 5 :: Int
                y = single False ./ 'X' ./ nil
                z = Just 'O'
            front a `shouldBe` x
            back a `shouldBe` z
            aft a `shouldBe` (y \. z)
            fore a `shouldBe` x ./ y

        it "has getter for unique fields using 'fetch'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            fetch @Int x `shouldBe` 5
            fetch @Bool x `shouldBe` False
            fetch @Char x `shouldBe` 'X'
            fetch @(Maybe Char) x `shouldBe` Just 'O'

        it "has getter for for unique fields using 'fetchN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            fetchN @0 Proxy x `shouldBe` 5
            fetchN @1 Proxy x `shouldBe` False
            fetchN @2 Proxy x `shouldBe` 'X'
            fetchN @3 Proxy x `shouldBe` Just 'O'

        it "has getter for duplicate fields using 'fetchN'" $ do
            let y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            fetchN @0 Proxy y `shouldBe` 5
            fetchN @1 Proxy y `shouldBe` False
            fetchN @2 Proxy y `shouldBe` 'X'
            fetchN @3 Proxy y `shouldBe` Just 'O'
            fetchN @4 Proxy y `shouldBe` 6
            fetchN @5 Proxy y `shouldBe` Just 'A'

        it "with duplicate fields can still use 'fetch' for unique fields" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            fetch @Bool x `shouldBe` False
            fetch @Char x `shouldBe` 'X'

        it "has getter for unique labels using 'fetchL'" $ do
            let y = (5 :: Int) ./ False ./ Tagged @Foo 'X' ./ Tagged @"Hello" (6 :: Int) ./ nil
            fetch @(Tagged Foo _) y `shouldBe` Tagged @Foo 'X'
            fetchL @Foo Proxy y `shouldBe` Tagged @Foo 'X'
            fetchL @"Hello" Proxy y `shouldBe` Tagged @"Hello" (6 :: Int)

        it "has setter for unique fields using 'replace'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replace @Int x 6 `shouldBe` (6 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replace x True `shouldBe` (5 :: Int) ./ True ./ 'X' ./ Just 'O' ./ nil
            replace x 'O' `shouldBe` (5 :: Int) ./ False ./ 'O' ./ Just 'O' ./ nil
            replace x (Just 'P') `shouldBe` (5 :: Int) ./ False ./ 'X' ./ Just 'P' ./ nil

        it "has polymorphic setter for unique fields using 'replace'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replace' @Int Proxy x 'Z' `shouldBe` 'Z' ./ False ./ 'X' ./ Just 'O' ./ nil
            replace' @Bool Proxy x 'Z' `shouldBe` (5 :: Int) ./ 'Z' ./ 'X' ./ Just 'O' ./ nil
            replace' @(Maybe Char) Proxy x 'Z' `shouldBe` (5 :: Int) ./ False ./ 'X' ./ 'Z' ./ nil

        it "has setter for unique labels using 'replaceL'" $ do
            let y = (5 :: Int) ./ False ./ Tagged @Foo 'X' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replace @(Tagged Foo _) y (Tagged @Foo 'Y') `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Foo 'Y' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replaceL @Foo Proxy y (Tagged @Foo 'Y') `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Foo 'Y' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replaceL @"Hello" Proxy y (Tagged @"Hello" 7) `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Foo 'X' ./ Tagged @"Hello" (7 :: Int) ./ nil

        it "has polymorphic setter for unique labels using 'replaceL'" $ do
            let y = (5 :: Int) ./ False ./ Tagged @Foo 'X' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replace' @(Tagged Foo Char) Proxy y (Tagged @Bar 'Y') `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Bar 'Y' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replaceL' @Foo Proxy y (Tagged @Bar 'Y') `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Bar 'Y' ./ Tagged @"Hello" (6 :: Int) ./ nil
            replaceL' @"Hello" Proxy y (Tagged @"Hello" False) `shouldBe`
                (5 :: Int) ./ False ./ Tagged @Foo 'X' ./ Tagged @"Hello" False ./ nil

        it "has setter for unique fields using 'replaceN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replaceN @0 Proxy x (7 :: Int) `shouldBe`
                (7 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replaceN @1 Proxy x True `shouldBe`
                (5 :: Int) ./ True ./ 'X' ./ Just 'O' ./ nil
            replaceN @2 Proxy x 'Y' `shouldBe`
                (5 :: Int) ./ False ./ 'Y' ./ Just 'O' ./ nil
            replaceN @3 Proxy x (Just 'P') `shouldBe`
                (5 :: Int) ./ False ./ 'X' ./ Just 'P' ./ nil

        it "has polymorphic setter using 'replaceN''" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            replaceN' @0 Proxy x True `shouldBe`
                True ./ False ./ 'X' ./ Just 'O' ./ nil
            let y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN' @1 Proxy y 'Y' `shouldBe`
                (5 :: Int) ./ 'Y' ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN' @5 Proxy y 'Y' `shouldBe`
                (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ 'Y' ./ nil

        it "has setter for duplicate fields using 'replaceN'" $ do
            let y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN @0 Proxy y (7 :: Int) `shouldBe`
                (7 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN @1 Proxy y True `shouldBe`
                (5 :: Int) ./ True ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN @2 Proxy y 'Y' `shouldBe`
                (5 :: Int) ./ False ./ 'Y' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN @3 Proxy y (Just 'P') `shouldBe`
                (5 :: Int) ./ False ./ 'X' ./ Just 'P' ./ (6 :: Int) ./ Just 'A' ./ nil
            replaceN @4 Proxy y (8 :: Int) `shouldBe`
                (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (8 :: Int) ./ Just 'A' ./ nil
            replaceN @5 Proxy y (Just 'B') `shouldBe`
                (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'B' ./ nil

        it "has setter for unique fields using 'replace' (even if there are other duplicate fields)" $ do
            let y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replace @Bool y True `shouldBe`
                (5 :: Int) ./ True ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            replace @Char y 'Y' `shouldBe`
                (5 :: Int) ./ False ./ 'Y' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil

        it "has getter for multiple fields using 'select'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            select @'[Int, Maybe Char] x `shouldBe` (5 :: Int) ./ Just 'O' ./ nil

        it "has getter for multiple labelled fields using 'selectL'" $ do
            let x = False ./ Tagged @"Hi" (5 :: Int) ./ Tagged @Foo False ./ Tagged @Bar 'X' ./ Tagged @"Bye" 'O' ./ nil
            selectL @'[Foo, Bar] Proxy x `shouldBe` Tagged @Foo False ./ Tagged @Bar 'X' ./ nil
            selectL @'["Hi", "Bye"] Proxy x `shouldBe` Tagged @"Hi" (5 :: Int) ./ Tagged @"Bye" 'O' ./ nil
            -- below won't compile because the type of labels must match
            -- selectL @'["Hi", 'Foo, "Bye"] Proxy x `shouldBe` Tagged @"Hi" (5 :: Int) ./ Tagged @Foo False ./ Tagged @"Bye" 'O' ./ nil

        it "can reorder fields using 'select' or 'selectN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            select @'[Bool, Int, Maybe Char] x `shouldBe` False ./ (5 :: Int) ./ Just 'O' ./ nil
            let y = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            selectN (Proxy @'[5, 4, 0, 1, 3, 2]) y `shouldBe`
                Just 'A' ./ (6 :: Int) ./ (5 ::Int) ./ False ./ Just 'O' ./ 'X' ./ nil

        it "has getter for multiple fields with duplicates using 'selectN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            selectN (Proxy @'[5, 4, 0]) x `shouldBe` Just 'A' ./ (6 :: Int) ./ (5 ::Int) ./ nil

        it "can't select into types from indistinct fields" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            -- Compile error: Int is a duplicate
            -- select @[Bool, Char, Int] x `shouldBe` False ./ 'X' ./ (5 :: Int) ./ nil
            x `shouldBe` x

        it "with duplicate fields has getter for multiple unique fields 'select'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            select @'[Bool, Char] x `shouldBe` False ./ 'X' ./ nil

        it "has setter for multiple fields using 'amend'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            amend @'[Int, Maybe Char] x ((6 :: Int) ./ Just 'P' ./ nil) `shouldBe` (6 :: Int) ./ False ./ 'X' ./ Just 'P' ./ nil

        it "has polymorphc setter for multiple fields using 'amend'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ nil
            amend' @'[Int, Maybe Char] Proxy x ("Foo" ./ "Bar" ./ nil) `shouldBe` "Foo" ./ False ./ 'X' ./ "Bar" ./ nil

        it "has setter for multiple labelled fields using 'amendL'" $ do
            let x = False ./ Tagged @"Hi" (5 :: Int) ./ Tagged @Foo False ./ Tagged @Bar 'X' ./ Tagged @"Bye" 'O' ./ nil
            amendL @'[Foo, Bar] Proxy x (Tagged @Foo True ./ Tagged @Bar 'Y' ./ nil) `shouldBe`
                False ./ Tagged @"Hi" (5 :: Int) ./ Tagged @Foo True ./ Tagged @Bar 'Y' ./ Tagged @"Bye" 'O' ./ nil
            amendL @'["Hi", "Bye"] Proxy x (Tagged @"Hi" (6 :: Int) ./ Tagged @"Bye" 'P' ./ nil) `shouldBe`
                False ./ Tagged @"Hi" (6 :: Int) ./ Tagged @Foo False ./ Tagged @Bar 'X' ./ Tagged @"Bye" 'P' ./ nil

        it "has polymorphic setter for multiple labelled fields using 'amendL'" $ do
            let x = False ./ Tagged @"Hi" (5 :: Int) ./ Tagged @Foo False ./ Tagged @Bar 'X' ./ Tagged @"Bye" 'O' ./ nil
            amendL' @'[Foo, Bar] Proxy x ('Y' ./ True ./ nil) `shouldBe`
                False ./ Tagged @"Hi" (5 :: Int) ./ 'Y' ./ True ./ Tagged @"Bye" 'O' ./ nil
            amendL' @'["Hi", "Bye"] Proxy x (True ./ Tagged @"Changed" True ./ nil) `shouldBe`
                False ./ True ./ Tagged @Foo False ./ Tagged @Bar 'X' ./ Tagged @"Changed" True ./ nil

        it "has setter for multiple fields with duplicates using 'amendN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            amendN (Proxy @'[5, 4, 0]) x (Just 'B' ./ (8 :: Int) ./ (4 ::Int) ./ nil) `shouldBe`
                (4 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (8 :: Int) ./ Just 'B' ./ nil

        it "has polymorphic setter for multiple fields with duplicates using 'amendN''" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            amendN' @'[5, 4, 0] Proxy x ("Foo" ./ Just 'B' ./ 'Z' ./ nil) `shouldBe`
                'Z' ./ False ./ 'X' ./ Just 'O' ./ Just 'B' ./ "Foo" ./ nil

        it "can't amend into types from indistinct fields" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            -- Compile error: Int is a duplicate
            -- amend @ '[Bool, Char, Int] x (True ./ 'B' ./ (8 :: Int) ./ nil) `shouldBe`
            --     (5 :: Int) ./ True ./ 'B' ./ Just 'O' ./ (8 :: Int) ./ Just 'A' ./ nil
            x `shouldBe` x

        it "with duplicate fields has setter for unique fields 'amend'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            amend @ '[Bool, Char] x (True ./ 'B' ./ nil) `shouldBe`
                (5 :: Int) ./ True ./ 'B' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil

        it "can be folded with 'Many' handlers using 'forMany' or 'collect'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
                y = show @Int ./ show @Char ./ show @(Maybe Char) ./ show @Bool ./ nil
                ret = ["5", "False", "'X'", "Just 'O'", "6", "Just 'A'"]
            afoldr (:) [] (collect x (cases y)) `shouldBe` ret
            afoldr (:) [] (forMany (cases y) x) `shouldBe` ret
            afoldr (:) [] (forMany (cases y) x) `shouldBe` ret

        it "can be folded with single 'CaseTypeable' handlers using 'forMany' or 'collect'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
            afoldr (:) [] (forMany (CaseTypeable (show . typeRep . (pure @Proxy))) x) `shouldBe` ["Int", "Bool", "Char", "Maybe Char", "Int", "Maybe Char"]

        it "can be folded with 'Many' handlers in index order using 'forManyN' or 'collectN'" $ do
            let x = (5 :: Int) ./ False ./ 'X' ./ Just 'O' ./ (6 :: Int) ./ Just 'A' ./ nil
                y = show @Int ./ show @Bool ./ show @Char ./ show @(Maybe Char) ./ show @Int ./ show @(Maybe Char) ./ nil
                ret = ["5", "False", "'X'", "Just 'O'", "6", "Just 'A'"]
            afoldr (:) [] (collectN x (casesN y)) `shouldBe` ret
            afoldr (:) [] (forManyN (casesN y) x) `shouldBe` ret
