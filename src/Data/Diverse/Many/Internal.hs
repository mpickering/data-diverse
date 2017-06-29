{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Diverse.Many.Internal (
    -- * 'Many' type
      Many(..) -- Exporting constructor unsafely!

      -- * Isomorphism
    , IsMany(..)
    , fromMany'
    , toMany'
    , _Many
    , _Many'

      -- * Construction
    , nul
    , single
    , prefix
    , (./)
    , postfix
    , (\.)
    , append
    , (/./)

    -- * Simple queries
    , front
    , back
    , aft
    , fore

    -- * Single field
    -- ** Getter for single field
    , fetch
    , fetchN
    -- ** Setter for single field
    , replace
    , replace'
    , replaceN
    , replaceN'
    -- ** Lens for a single field
    , item
    , item'
    , itemN
    , itemN'

    -- * Multiple fields
    -- ** Getter for multiple fields
    , Select
    , select
    , SelectN
    , selectN
    -- ** Setter for multiple fields
    , Amend
    , amend
    , Amend'
    , amend'
    , AmendN
    , amendN
    , AmendN'
    , amendN'
    -- ** Lens for multiple fields
    , project
    , project'
    , projectN
    , projectN'

    -- * Destruction
    -- ** By type
    , Via -- no constructor
    , via -- safe construction
    , forMany
    , collect
    -- ** By Nat index offset
    , ViaN -- no constructor
    , viaN -- safe construction
    , forManyN
    , collectN
    ) where

import Control.Applicative
import Control.Lens
import Data.Bool
import Data.Diverse.AFoldable
import Data.Diverse.Case
import Data.Diverse.Collector
import Data.Diverse.Emit
import Data.Diverse.Reiterate
import Data.Diverse.Type
import Data.Foldable
import Data.Kind
import qualified Data.Map.Strict as M
import Data.Proxy
import Data.Tagged
import qualified GHC.Generics as G
import GHC.Prim (Any, coerce)
import GHC.TypeLits
import Text.ParserCombinators.ReadPrec
import Text.Read
import qualified Text.Read.Lex as L
import Unsafe.Coerce

-- This module uses the partial 'head', 'tail' from Prelude.
-- I like to highlight them as partial by using them in the namespace Partial.head
-- These usages in this module are safe due to size guarantees provided by the typelist.
import Prelude as Partial

-- | A Many is an anonymous product type (also know as polymorphic record), with no limit on the number of fields.
--
-- The following functions are available can be used to manipulate unique fields
--
-- * getter/setter for single field: 'fetch' and 'replace'
-- * getter/setter for multiple fields: 'select' and 'amend'
-- * folds: 'forMany' or 'collect'
--
-- These functions are type specified. This means labels are not required because the types themselves can be used to access the 'Many.
-- It is a compile error to use those functions for duplicate fields.
--
-- For duplicate fields, Nat-indexed versions of the functions are available:
--
-- * getter/setter for single field: 'fetchN' and 'replaceN'
-- * getter/setter for multiple fields: 'selectN' and 'amendN'
-- * folds: 'forManyN' or 'collectN'
--
-- Encoding: The record is encoded as (Offset, Map Int Any).
-- This encoding should reasonabily efficient for any number of fields.
--
-- The map Key is index + offset of the type in the typelist.
-- The Offset is used to allow efficient cons 'prefix'.
--
-- @Key = Index of type in typelist + Offset@
--
-- The constructor will guarantee the correct number and types of the elements.
-- The constructor is only exported in the "Data.Diverse.Many.Internal" module
data Many (xs :: [Type]) = Many {-# UNPACK #-} !Int (M.Map Int Any)
{-# NOINLINE Many #-}

-- | Inferred role is phantom which is incorrect
type role Many representational

-- | Many stored as a list. This is useful when folding over 'Many' efficienty
-- so that the conversion to List is only done once
data ManyList (xs :: [Type]) = ManyList [Any]

toManyList :: Many xs -> ManyList xs
toManyList (Many _ m) = ManyList (snd <$> M.toAscList m)

fromManyList :: ManyList xs -> Many xs
fromManyList (ManyList xs) = Many 0 (M.fromList (zip [(0 :: Int)..] xs))
-----------------------------------------------------------------------

-- | A terminating 'G.Generic' instance encoded as a 'nul'.
instance G.Generic (Many '[]) where
    type Rep (Many '[]) =  G.U1
    from _ = {- G.U1 -} G.U1
    to G.U1 = nul

-- | A 'G.Generic' instance encoded as the 'front' value 'G.:*:' with the 'aft' 'Many'.
-- The 'G.C1' and 'G.S1' metadata are not encoded.
instance G.Generic (Many (x ': xs)) where
    type Rep (Many (x ': xs)) = (G.Rec0 x) G.:*: (G.Rec0 (Many xs))
    from r = ({- G.Rec0 -} G.K1 (front r)) G.:*: ({- G.Rec0 -} G.K1 (aft r))
    to (({- G.Rec0 -} G.K1 a) G.:*: ({- G.Rec0 -} G.K1 b)) = a ./ b

-----------------------------------------------------------------------

-- | This instance allows converting to and from Many
-- There are instances for converting tuples of up to size 15.
class IsMany t xs a where
    toMany :: t xs a -> Many xs
    fromMany :: Many xs -> t xs a

-- | Converts from a value (eg a tuple) to a 'Many', via a 'Tagged' wrapper
toMany' :: IsMany Tagged xs a => a -> Many xs
toMany' a = toMany (Tagged a)

-- | Converts from a Many to a value (eg a tuple), via a Tagged wrapper
fromMany' :: IsMany Tagged xs a => Many xs -> a
fromMany' = unTagged . fromMany

-- | @_Many = iso fromMany toMany@
_Many :: IsMany t xs a => Iso' (Many xs) (t xs a)
_Many = iso fromMany toMany

-- | @_Many' = iso fromMany' toMany'@
_Many' :: IsMany Tagged xs a => Iso' (Many xs) a
_Many' = iso fromMany' toMany'

-- | These instances add about 7 seconds to the compile time!
instance IsMany Tagged '[] () where
    toMany _ = nul
    fromMany _ = Tagged ()

-- | This single field instance is the reason for 'Tagged' wrapper.
-- Otherwise this instance will overlap.
instance IsMany Tagged '[a] a where
    toMany (Tagged a) = single a
    fromMany r = Tagged (fetch @a r)

instance IsMany Tagged '[a,b] (a,b) where
    toMany (Tagged (a,b)) = a./b./nul
    fromMany r = Tagged (fetchN (Proxy @0) r, fetchN (Proxy @1) r)

instance IsMany Tagged '[a,b,c] (a,b,c) where
    toMany (Tagged (a,b,c)) = a./b./c./nul
    fromMany r = Tagged (fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r)

instance IsMany Tagged '[a,b,c,d] (a,b,c,d) where
    toMany (Tagged (a,b,c,d)) = a./b./c./d./nul
    fromMany r = Tagged (fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r)

instance IsMany Tagged '[a,b,c,d,e] (a,b,c,d,e) where
    toMany (Tagged (a,b,c,d,e)) = a./b./c./d./e./nul
    fromMany r = Tagged (fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r)

instance IsMany Tagged '[a,b,c,d,e,f] (a,b,c,d,e,f) where
    toMany (Tagged (a,b,c,d,e,f)) = a./b./c./d./e./f./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r)

instance IsMany Tagged '[a,b,c,d,e,f,g] (a,b,c,d,e,f,g) where
    toMany (Tagged (a,b,c,d,e,f,g)) = a./b./c./d./e./f./g./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h] (a,b,c,d,e,f,g,h) where
    toMany (Tagged (a,b,c,d,e,f,g,h)) = a./b./c./d./e./f./g./h./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i] (a,b,c,d,e,f,g,h,i) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i)) = a./b./c./d./e./f./g./h./i./ nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j] (a,b,c,d,e,f,g,h,i,j) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j)) = a./b./c./d./e./f./g./h./i./j./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j,k] (a,b,c,d,e,f,g,h,i,j,k) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j,k)) = a./b./c./d./e./f./g./h./i./j./k./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r
                        , fetchN (Proxy @10) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j,k,l] (a,b,c,d,e,f,g,h,i,j,k,l) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j,k,l)) = a./b./c./d./e./f./g./h./i./j./k./l./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r
                        , fetchN (Proxy @10) r, fetchN (Proxy @11) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j,k,l,m] (a,b,c,d,e,f,g,h,i,j,k,l,m) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j,k,l,m)) = a./b./c./d./e./f./g./h./i./j./k./l./m./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r
                        , fetchN (Proxy @10) r, fetchN (Proxy @11) r, fetchN (Proxy @12) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j,k,l,m,n] (a,b,c,d,e,f,g,h,i,j,k,l,m,n) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j,k,l,m,n)) = a./b./c./d./e./f./g./h./i./j./k./l./m./n./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r
                        , fetchN (Proxy @10) r, fetchN (Proxy @11) r, fetchN (Proxy @12) r, fetchN (Proxy @13) r)

instance IsMany Tagged '[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o] (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) where
    toMany (Tagged (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)) = a./b./c./d./e./f./g./h./i./j./k./l./m./n./o./nul
    fromMany r = Tagged ( fetchN (Proxy @0) r, fetchN (Proxy @1) r, fetchN (Proxy @2) r, fetchN (Proxy @3) r, fetchN (Proxy @4) r
                        , fetchN (Proxy @5) r, fetchN (Proxy @6) r, fetchN (Proxy @7) r, fetchN (Proxy @8) r, fetchN (Proxy @9) r
                        , fetchN (Proxy @10) r, fetchN (Proxy @11) r, fetchN (Proxy @12) r, fetchN (Proxy @13) r, fetchN (Proxy @14) r)

-----------------------------------------------------------------------

-- | When appending two maps together, get the function to 'M.mapKeys' the RightMap
-- when adding RightMap into LeftMap.
-- The existing contents of LeftMap will not be changed.
-- LeftMap Offset will also not change.
-- The desired key for element from the RightMap = RightIndex (of the element) + LeftOffset + LeftSize
-- OldRightKey = RightIndex + RightOffset, therefore RightIndex = OldRightKey - RightOffset
-- So we need to adjust the existing index on the RightMap by
-- \OldRightKey -> RightIndex + LeftOffset + LeftSize (as above)
-- \OldRightKey -> OldRightKey - RightOffset + LeftOffset + LeftSize
rightKeyForSnoc :: Int -> Int -> Int -> Int -> Int
rightKeyForSnoc lo ld ro rk = rk - ro + lo + ld

-- | When appending two maps together, get the function to modify the RightMap's offset
-- when adding LeftMap into RightMap.
-- The existing contents of RightMap will not be changed.
-- NewRightOffset = OldRightOffset - LeftSize
rightOffsetForCons :: Int -> Int -> Int
rightOffsetForCons ld ro = ro - ld

-- | When appending two maps together, get the function to 'M.mapKeys' the LeftMap
-- when adding LeftMap into RightMap.
-- The existing contents of RightMap will not be changed.
-- The RightMap's offset will be adjusted using 'rightOffsetWithRightMapUnchanged'
-- The desired key for the elements in the the LeftMap = LeftIndex (of the element) + NewRightOffset
-- OldLeftKey = LeftIndex + LeftOffset, therefore LeftIndex = OldLeftKey - LeftOffset
-- So we need to adjust the existing index on the LeftMap by
-- \OldLeftKey -> LeftIndex + NewRightOffset (as above)
-- \OldLeftKey -> OldLeftKey - LeftOffset + NewRightOffset (as above)
leftKeyForCons :: Int -> Int -> Int -> Int
leftKeyForCons lo ro lk = lk - lo + ro

-- | Analogous to 'Prelude.null'. Named 'nul' to avoid conflicting with 'Prelude.null'.
nul :: Many '[]
nul = Many 0 M.empty
infixr 5 `nul` -- to be the same as 'prefix'

-- | Create a Many from a single value. Analogous to 'M.singleton'
single :: x -> Many '[x]
single v = Many 0 (M.singleton 0 (unsafeCoerce v))

-- | Add an element to the left of a Many.
-- Not named @cons@ to avoid conflict with 'Control.Lens.cons'
prefix :: x -> Many xs -> Many (x ': xs)
prefix x (Many ro rm) = Many nro
    (M.insert
        (leftKeyForCons 0 nro 0)
        (unsafeCoerce x)
        rm)
  where
    nro = rightOffsetForCons 1 ro
infixr 5 `prefix`

-- | Infix version of 'prefix'.
--
-- Mnemonic: Element on the left is smaller './' than the larger 'Many' to the right.
(./) :: x -> Many xs -> Many (x ': xs)
(./) = prefix
infixr 5 ./ -- like Data.List.(:)

-- | Add an element to the right of a Many
-- Not named 'snoc' to avoid conflict with 'Control.Lens.snoc'
postfix :: Many xs -> y -> Many (Append xs '[y])
postfix (Many lo lm) y = Many lo
    (M.insert (rightKeyForSnoc lo (M.size lm) 0 0)
        (unsafeCoerce y)
        lm)
infixl 5 `postfix`

-- | 'snoc' mnemonic: Many is larger '\.' than the smaller element
(\.) :: Many xs -> y -> Many (Append xs '[y])
(\.) = postfix
infixl 5 \.

-- | 'append' mnemonic: 'cons' './' with an extra slash (meaning 'Many') in front.
(/./) :: Many xs -> Many ys -> Many (Append xs ys)
(/./) = append
infixr 5 /./ -- like (++)

-- | Appends two Manys together
append :: Many xs -> Many ys -> Many (Append xs ys)
append (Many lo lm) (Many ro rm) = if ld >= rd
    then Many
         lo
         (lm `M.union` (M.mapKeys (rightKeyForSnoc lo ld ro) rm))
    else Many
         nro
         ((M.mapKeys (leftKeyForCons lo nro) lm) `M.union` rm)
  where
    ld = M.size lm
    rd = M.size rm
    nro = rightOffsetForCons ld ro
infixr 5 `append` -- like Data.List (++)

-----------------------------------------------------------------------

-- | Extract the first element of a Many, which guaranteed to be non-empty.
-- Analogous to 'Partial.head'
front :: Many (x ': xs) -> x
front (Many _ m) = unsafeCoerce (snd . Partial.head $ M.toAscList m)

front' :: ManyList (x ': xs) -> x
front' (ManyList xs) = unsafeCoerce (Partial.head xs)

-- | Extract the 'back' element of a Many, which guaranteed to be non-empty.
-- Analogous to 'Prelude.last'
back :: Many (x ': xs) -> Last (x ': xs)
back (Many _ m) = unsafeCoerce (snd . Partial.head $ M.toDescList m)

-- | Extract the elements after the front of a Many, which guaranteed to be non-empty.
-- Analogous to 'Partial.tail'
aft :: Many (x ': xs) -> Many xs
aft (Many o m) = Many (o + 1) (M.delete o m)

aft' :: ManyList (x ': xs) -> ManyList xs
aft' (ManyList xs) = ManyList (Partial.tail xs)

-- | Return all the elements of a Many except the 'back' one, which guaranteed to be non-empty.
-- Analogous to 'Prelude.init'
fore :: Many (x ': xs) -> Many (Init (x ': xs))
fore (Many o m) = Many o (M.delete (o + M.size m - 1) m)

--------------------------------------------------

-- | Getter by unique type. Get the field with type @x@.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- 'fetch' \@Int x \`shouldBe` 5
-- @
fetch :: forall x xs. UniqueMember x xs => Many xs -> x
fetch (Many o m) = unsafeCoerce (m M.! (o + i))
  where i = fromInteger (natVal @(IndexOf x xs) Proxy)

--------------------------------------------------

-- | Getter by index. Get the value of the field at index type-level Nat @n@
--
-- @getchN (Proxy \@2) t@
fetchN :: forall n x xs proxy. MemberAt n x xs => proxy n -> Many xs -> x
fetchN p (Many o m) = unsafeCoerce (m M.! (o + i))
  where i = fromInteger (natVal p)

--------------------------------------------------

-- | Setter by unique type. Set the field with type @x@.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- 'replace' \@Int x 6 \`shouldBe` (6 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- @
replace :: forall x xs. UniqueMember x xs => Many xs -> x -> Many xs
replace (Many o m) v = Many o (M.insert (o + i) (unsafeCoerce v) m)
  where i = fromInteger (natVal @(IndexOf x xs) Proxy)

-- | Polymorphic setter by unique type. Set the field with type @x@, and replace with type @y@
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- 'replace'' \@Int Proxy x (Just True) \`shouldBe` Just True './' False './' \'X' './' Just \'O' './' 'nul'
-- @
replace' :: forall x y xs. UniqueMember x xs => Proxy x -> Many xs -> y -> Many (Replace x y xs)
replace' _ (Many o m) v = Many o (M.insert (o + i) (unsafeCoerce v) m)
  where i = fromInteger (natVal @(IndexOf x xs) Proxy)

--------------------------------------------------

-- | Setter by index. Set the value of the field at index type-level Nat @n@
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- 'replaceN' \@0 Proxy x 7 `shouldBe`
-- @
replaceN :: forall n x y xs proxy. MemberAt n x xs => proxy n -> Many xs -> y -> Many xs
replaceN p (Many o m) v = Many o (M.insert (o + i) (unsafeCoerce v) m)
  where i = fromInteger (natVal p)

-- | Polymorphic version of 'replaceN'
replaceN' :: forall n x y xs proxy. MemberAt n x xs => proxy n -> Many xs -> y -> Many (ReplaceIndex n y xs)
replaceN' p (Many o m) v = Many o (M.insert (o + i) (unsafeCoerce v) m)
  where i = fromInteger (natVal p)

-----------------------------------------------------------------------

-- | 'fetch' ('view' 'item') and 'replace' ('set' 'item') in 'Lens'' form.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- x '^.' 'item' \@Int \`shouldBe` 5
-- (x '&' 'item' \@Int .~ 6) \`shouldBe` (6 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- @
item :: forall x xs. UniqueMember x xs => Lens' (Many xs) x
item = lens fetch replace
{-# INLINE item #-}

-- | Polymorphic version of 'item'
item' :: forall x y xs. UniqueMember x xs => Lens (Many xs) (Many (Replace x y xs)) x y
item' = lens fetch (replace' @x @y Proxy)
{-# INLINE item' #-}

-- | 'fetchN' ('view' 'item') and 'replaceN' ('set' 'item') in 'Lens'' form.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' ./ nul
-- x '^.' 'itemN' (Proxy \@0) \`shouldBe` 5
-- (x '&' 'itemN' (Proxy @0) '.~' 6) \`shouldBe` (6 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
-- @
itemN ::  forall n x xs proxy. MemberAt n x xs => proxy n -> Lens' (Many xs) x
itemN p = lens (fetchN p) (replaceN p)
{-# INLINE itemN #-}


-- | Polymorphic version of 'itemN'
itemN' ::  forall n x y xs proxy. MemberAt n x xs => proxy n -> Lens (Many xs) (Many (ReplaceIndex n y xs)) x y
itemN' p = lens (fetchN p) (replaceN' @n @x @y p)
{-# INLINE itemN' #-}

-----------------------------------------------------------------------

-- | Internal function for construction - do not expose!
fromList' :: Ord k => [(k, WrappedAny)] -> M.Map k Any
fromList' xs = M.fromList (coerce xs)

-----------------------------------------------------------------------

-- | Wraps a 'Case' into an instance of 'Emit', 'reiterate'ing and feeding 'Case' with the value from the 'Many'
-- and 'emit'ting the results.
--
-- Internally, this holds the left-over [(k, v)] from the original 'Many' for the remaining typelist @xs@.
--
-- That is the first v in the (k, v) is of type @x@, and the length of the list is equal to the length of @xs@.
newtype Via c (xs :: [Type]) r = Via (c xs r, [Any])

-- | Creates an 'Via' safely, so that the invariant of \"typelist to the value list type and size\" holds.
via :: c xs r -> Many xs -> Via c xs r
via c (Many _ m) = Via (c, snd <$> M.toAscList m)

instance Reiterate c (x ': xs) => Reiterate (Via c) (x ': xs) where
    -- use of tail here is safe as we are guaranteed the length from the typelist
    reiterate (Via (c, xxs)) = Via (reiterate c, Partial.tail xxs)

instance (Case c (x ': xs) r) => Emit (Via c) (x ': xs) r where
    emit (Via (c, xxs)) = caseAny c v
      where
       -- use of front here is safe as we are guaranteed the length from the typelist
       v = Partial.head xxs

-----------------------------------------------------------------------

-- | Folds any 'Many', even with indistinct types.
-- Given __distinct__ handlers for the fields in 'Many', create a 'Collector'
-- of the results of running the handlers over the fields in 'Many'.
--
-- The 'Collector' is 'AFoldable' to combine the results.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
--     y = show \@Int './' show \@Char './' show \@(Maybe Char) './' show \@Bool './' 'nul'
-- 'afoldr' (:) [] ('forMany' ('Data.Diverse.Cases.cases' y) x) \`shouldBe`
--     [\"5", \"False", \"\'X'", \"Just \'O'", \"6", \"Just \'A'"]
-- @
forMany :: c xs r -> Many xs -> Collector (Via c) xs r
forMany c x = Collector (via c x)

-- | This is @flip 'forMany'@
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
--     y = show \@Int './' show \@Char './' show \@(Maybe Char) './' show \@Bool './' 'nul'
-- 'afoldr' (:) [] ('collect' x ('Data.Diverse.Cases.cases' y)) \`shouldBe`
--     [\"5", \"False", \"\'X'", \"Just \'O'", \"6", \"Just \'A'"]
-- @
collect :: Many xs -> c xs r -> Collector (Via c) xs r
collect = flip forMany

-----------------------------------------------------------------------

-- | A variation of 'Via' which __'reiterateN'__ instead.
newtype ViaN c (n :: Nat) (xs :: [Type]) r = ViaN (c n xs r, [Any])

-- | Creates an 'ViaN' safely, so that the invariant of \"typelist to the value list type and size\" holds.
viaN :: c n xs r -> Many xs -> ViaN c n xs r
viaN c (Many _ m) = ViaN (c, snd <$> M.toAscList m)

instance ReiterateN c n (x ': xs) => ReiterateN (ViaN c) n (x ': xs) where
    -- use of tail here is safe as we are guaranteed the length from the typelist
    reiterateN (ViaN (c, xxs)) = ViaN (reiterateN c, Partial.tail xxs)

instance (Case (c n) (x ': xs) r) => Emit (ViaN c n) (x ': xs) r where
    emit (ViaN (c, xxs)) = caseAny c v
      where
       -- use of front here is safe as we are guaranteed the length from the typelist
       v = Partial.head xxs

-- | Folds any 'Many', even with indistinct types.
-- Given __index__ handlers for the fields in 'Many', create a 'CollectorN'
-- of the results of running the handlers over the fields in 'Many'.
--
-- The 'CollectorN' is 'AFoldable' to combine the results.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
--     y = show \@Int './' show \@Bool './' show \@Char './' show \@(Maybe Char) './' show \@Int './' show \@(Maybe Char) './' 'nul'
-- 'afoldr' (:) [] ('forManyN' ('Data.Diverse.Cases.casesN' y) x) \`shouldBe`
--     [\"5", \"False", \"\'X'", \"Just \'O'", \"6", \"Just \'A'"]
-- @
forManyN :: c n xs r -> Many xs -> CollectorN (ViaN c) n xs r
forManyN c x = CollectorN (viaN c x)

-- | This is @flip 'forManyN'@
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
--     y = show \@Int './' show \@Bool './' show \@Char './' show \@(Maybe Char) './' show \@Int './' show \@(Maybe Char) './' 'nul'
-- 'afoldr' (:) [] ('collectN' x ('Data.Diverse.Cases.casesN' y)) \`shouldBe`
--     [\"5", \"False", \"\'X'", \"Just \'O'", \"6", \"Just \'A'"]
-- @
collectN :: Many xs -> c n xs r -> CollectorN (ViaN c) n xs r
collectN = flip forManyN

-----------------------------------------------------------------------

-- | A friendlier type constraint synomyn for 'select'
type Select (smaller :: [Type]) (larger :: [Type]) =
    (AFoldable
        ( Collector (Via (CaseSelect smaller larger)) larger) [(Int, WrappedAny)])

-- | Construct a 'Many' with a smaller number of fields than the original.
-- Analogous to 'fetch' getter but for multiple fields.
--
-- This can also be used to reorder fields in the original 'Many'.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
-- 'select' \@'[Bool, Char] x \`shouldBe` False './' \'X' './' 'nul'
-- @
select :: forall smaller larger. Select smaller larger => Many larger -> Many smaller
select t = Many 0 (fromList' xs')
  where
    xs' = afoldr (++) [] (Collector (via (CaseSelect @smaller @larger @larger) t))

-- | For each type x in @larger@, generate the (k, v) in @smaller@ (if it exists)
data CaseSelect (smaller :: [Type]) (larger :: [Type]) (xs :: [Type]) r = CaseSelect

instance Reiterate (CaseSelect smaller larger) (x ': xs) where
    reiterate CaseSelect = CaseSelect

-- | For each type x in larger, find the index in ys, and create an (incrementing key, value)
instance forall smaller larger x xs. (UniqueIfExists smaller x larger, MaybeUniqueMember x smaller) =>
         Case (CaseSelect smaller larger) (x ': xs) [(Int, WrappedAny)] where
    caseAny _ v =
        case i of
            0 -> []
            i' -> [(i' - 1, WrappedAny v)]
      where
        i = fromInteger (natVal @(PositionOf x smaller) Proxy)

-----------------------------------------------------------------------

-- | A friendlier type constraint synomyn for 'selectN'
type SelectN (ns :: [Nat]) (smaller ::[Type]) (larger :: [Type]) =
    ( AFoldable (CollectorN (ViaN (CaseSelectN ns smaller)) 0 larger) [(Int, WrappedAny)]
    , smaller ~ KindsAtIndices ns larger
    , IsDistinct ns)

-- | A variation of 'select' which uses a Nat list @n@ to specify how to reorder the fields, where
--
-- @
-- indices[branch_idx] = tree_idx@
-- @
--
-- This variation allows @smaller@ or @larger@ to contain indistinct since
-- the mapping is specified by @indicies@.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
-- 'selectN' (Proxy @'[5, 4, 0]) x \`shouldBe` Just \'A' './' (6 :: Int) './' (5 ::Int) './' 'nul'
-- @
selectN
    :: forall ns smaller larger proxy.
       SelectN ns smaller larger
    => proxy ns -> Many larger -> Many smaller
selectN _ xs = Many 0 (fromList' xs')
  where
    xs' = afoldr (++) [] (forManyN (CaseSelectN @ns @smaller @0 @larger) xs)

data CaseSelectN (indices :: [Nat]) (smaller :: [Type]) (n :: Nat) (xs :: [Type]) r = CaseSelectN

instance ReiterateN (CaseSelectN indices smaller) n (x ': xs) where
    reiterateN CaseSelectN = CaseSelectN

-- | For each type x in @larger@, find the index in ys, and create an (incrementing key, value)
instance forall indices smaller n x xs. MaybeMemberAt (PositionOf n indices) x smaller =>
         Case (CaseSelectN indices smaller n) (x ': xs) [(Int, WrappedAny)] where
    caseAny _ v =
        case i of
            0 -> []
            i' -> [(i' - 1, WrappedAny v)]
      where
        i = fromInteger (natVal @(PositionOf n indices) Proxy)

-----------------------------------------------------------------------

-- | A friendlier type constraint synomyn for 'amend'
type Amend smaller larger = (AFoldable (Collector (Via (CaseAmend larger)) smaller) (Int, WrappedAny)
       , IsDistinct smaller)

-- | Sets the subset of 'Many' in the larger 'Many'.
-- Analogous to 'replace' setter but for multiple fields.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- 'amend' \@'[Int, Maybe Char] x ((6 :: Int) './' Just \'P' './' 'nul') \`shouldBe`
--     (6 :: Int) './' False './' \'X' './' Just \'P' './' 'nul'
-- @
amend :: forall smaller larger. Amend smaller larger => Many larger -> Many smaller -> Many larger
amend (Many lo lm) t = Many lo (fromList' xs' `M.union` lm)
  where
    xs' = afoldr (:) [] (forMany (CaseAmend @larger @smaller lo) t)

newtype CaseAmend (larger :: [Type]) (xs :: [Type]) r = CaseAmend Int

instance Reiterate (CaseAmend larger) (x ': xs) where
    reiterate (CaseAmend lo) = CaseAmend lo

-- | for each x in @smaller@, convert it to a (k, v) to insert into the x in @Many larger@
instance UniqueMember x larger => Case (CaseAmend larger) (x ': xs) (Int, WrappedAny) where
    caseAny (CaseAmend lo) v = (lo + i, WrappedAny v)
      where
        i = fromInteger (natVal @(IndexOf x larger) Proxy)

-----------------------------------------------------------------------

-- | A friendlier type constraint synomyn for 'amend''
type Amend' smaller smaller' larger = (AFoldable (Collector (Via (CaseAmend' larger)) (Zip smaller smaller')) (Int, WrappedAny), IsDistinct smaller)

amend' :: forall smaller smaller' larger. Amend' smaller smaller' larger
    => Proxy smaller -> Many larger -> Many smaller' -> Many (Replaces smaller smaller' larger)
amend' _ (Many lo lm) t = Many lo (fromList' xs' `M.union` lm)
  where
    xs' = afoldr (:) [] (Collector (via' @smaller Proxy (CaseAmend' @larger @(Zip smaller smaller') lo) t))

-- | We are cheating here and saying that the @y@ can be unsafeCoerced into a type of @(x, y)@
-- but we only every coerce from 'Any' back into @y@in the @caseAny (CaseAmend' lo) v@ below.
via' :: Proxy xs -> c (Zip xs ys) r -> Many ys -> Via c (Zip xs ys) r
via' _ c (Many _ m) = Via (c, snd <$> M.toAscList m)

newtype CaseAmend' (larger :: [Type]) (zs :: [Type]) r = CaseAmend' Int

instance Reiterate (CaseAmend' larger) (z ': zs) where
    reiterate (CaseAmend' lo) = CaseAmend' lo

-- | for each y in @smaller@, convert it to a (k, v) to insert into the x in @Many larger@
instance UniqueMember x larger => Case (CaseAmend' larger) ((x, y) ': zs) (Int, WrappedAny) where
    caseAny (CaseAmend' lo) v = (lo + i, WrappedAny v)
      where
        i = fromInteger (natVal @(IndexOf x larger) Proxy)

-----------------------------------------------------------------------
-- | A friendlier type constraint synomyn for 'amendN'
type AmendN ns smaller larger =
    ( AFoldable (CollectorN (ViaN (CaseAmendN ns larger)) 0 smaller) (Int, WrappedAny)
    , smaller ~ KindsAtIndices ns larger
    , IsDistinct ns)

-- | A variation of 'amend' which uses a Nat list @n@ to specify how to reorder the fields, where
--
-- @
-- indices[branch_idx] = tree_idx@
-- @
--
-- This variation allows @smaller@ or @larger@ to contain indistinct since
-- the mapping is specified by @indicies@.
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
-- 'amendN' (Proxy \@'[5, 4, 0]) x (Just \'B' './' (8 :: Int) './' (4 ::Int) './' 'nul') \`shouldBe`
--     (4 :: Int) './' False './' \'X' './' Just \'O' './' (8 :: Int) './' Just \'B' './' 'nul'
-- @
amendN :: forall ns smaller larger proxy.
       (AmendN ns smaller larger)
    => proxy ns -> Many larger -> Many smaller -> Many larger
amendN _ (Many lo lm) t = Many lo (fromList' xs' `M.union` lm)
  where
    xs' = afoldr (:) [] (forManyN (CaseAmendN @ns @larger @0 @smaller lo) t)

-----------------------------------------------------------------------

newtype CaseAmendN (indices :: [Nat]) (larger :: [Type]) (n :: Nat) (xs :: [Type]) r = CaseAmendN Int

instance ReiterateN (CaseAmendN indices larger) n (x ': xs) where
    reiterateN (CaseAmendN lo) = CaseAmendN lo

-- | for each x in @smaller@, convert it to a (k, v) to insert into the x in @larger@
instance (MemberAt (KindAtIndex n indices) x larger) =>
         Case (CaseAmendN indices larger n) (x ': xs) (Int, WrappedAny) where
    caseAny (CaseAmendN lo) v = (lo + i, WrappedAny v)
      where
        i = fromInteger (natVal @(KindAtIndex n indices) Proxy)

-- | A friendlier type constraint synomyn for 'amendN'
type AmendN' ns smaller smaller' larger =
    ( AFoldable (CollectorN (ViaN (CaseAmendN' ns larger)) 0 (Zip smaller smaller')) (Int, WrappedAny)
    , smaller ~ KindsAtIndices ns larger
    , IsDistinct ns)

-- | A polymorphic variation of 'amendN'
amendN' :: forall ns smaller smaller' larger proxy.
       (AmendN' ns smaller smaller' larger)
    => proxy ns -> Many larger -> Many smaller' -> Many (ReplacesIndex ns smaller' larger)
amendN' _ (Many lo lm) t = Many lo (fromList' xs' `M.union` lm)
  where
    xs' = afoldr (:) [] (CollectorN (viaN' @smaller Proxy (CaseAmendN' @ns @larger @0 @(Zip smaller smaller') lo) t))

-- | We are cheating here and saying that the @y@ can be unsafeCoerced into a type of @(x, y)@
-- but we only every coerce from 'Any' back into @y@in the @caseAny (CaseAmend' lo) v@ below.
viaN' :: Proxy xs -> c n (Zip xs ys) r -> Many ys -> ViaN c n (Zip xs ys) r
viaN' _ c (Many _ m) = ViaN (c, snd <$> M.toAscList m)

newtype CaseAmendN' (indices :: [Nat]) (larger :: [Type]) (n :: Nat) (zs :: [Type]) r = CaseAmendN' Int

instance ReiterateN (CaseAmendN' indices larger) n (z ': zs) where
    reiterateN (CaseAmendN' lo) = CaseAmendN' lo

-- | for each x in @smaller@, convert it to a (k, v) to insert into the x in @larger@
instance (MemberAt (KindAtIndex n indices) x larger) =>
         Case (CaseAmendN' indices larger n) ((x, y) ': zs) (Int, WrappedAny) where
    caseAny (CaseAmendN' lo) v = (lo + i, WrappedAny v)
      where
        i = fromInteger (natVal @(KindAtIndex n indices) Proxy)

-----------------------------------------------------------------------

-- | 'select' ('view' 'project') and 'amend' ('set' 'project') in 'Lens'' form.
--
-- @
-- 'project' = 'lens' 'select' 'amend'
-- @
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'
-- x '^.' ('project' \@'[Int, Maybe Char]) \`shouldBe` (5 :: Int) './' Just \'O' './' 'nul'
-- (x '&' ('project' \@'[Int, Maybe Char]) '.~' ((6 :: Int) './' Just 'P' './' 'nul')) \`shouldBe`
--     (6 :: Int) './' False './' \'X' './' Just \'P' './' 'nul'
-- @
project
    :: forall smaller larger.
       (Select smaller larger, Amend smaller larger)
    => Lens' (Many larger) (Many smaller)
project = lens select amend
{-# INLINE project #-}

-- | Polymorphic version of project'
project'
    :: forall smaller smaller' larger.
       (Select smaller larger, Amend' smaller smaller' larger)
    => Lens (Many larger) (Many (Replaces smaller smaller' larger)) (Many smaller) (Many smaller')
project' = lens select (amend' @smaller @smaller' Proxy)
{-# INLINE project' #-}

-- | 'selectN' ('view' 'projectN') and 'amendN' ('set' 'projectN') in 'Lens'' form.
--
-- @
-- 'projectN' = 'lens' 'selectN' 'amendN'
-- @
--
-- @
-- let x = (5 :: Int) './' False './' \'X' './' Just \'O' './' (6 :: Int) './' Just \'A' './' 'nul'
-- x '^.' ('projectN' \@'[5, 4, 0] Proxy) \`shouldBe` Just \'A' './' (6 :: Int) './' (5 ::Int) './' 'nul'
-- (x '&' ('projectN' \@'[5, 4, 0] Proxy) '.~' (Just \'B' './' (8 :: Int) './' (4 ::Int) './' nul)) \`shouldBe`
--     (4 :: Int) './' False './' \'X' './' Just \'O' './' (8 :: Int) './' Just \'B' './' 'nul'
-- @
projectN
    :: forall ns smaller larger proxy.
       (SelectN ns smaller larger, AmendN ns smaller larger)
    => proxy ns -> Lens' (Many larger) (Many smaller)
projectN p = lens (selectN p) (amendN p)
{-# INLINE projectN #-}

-- | Polymorphic version of 'projectN'
projectN'
    :: forall ns smaller smaller' larger proxy.
       (SelectN ns smaller larger, AmendN' ns smaller smaller' larger)
    => proxy ns -> Lens (Many larger) (Many (ReplacesIndex ns smaller' larger)) (Many smaller) (Many smaller')
projectN' p = lens (selectN p) (amendN' p)
{-# INLINE projectN' #-}

-----------------------------------------------------------------------

-- -- | Stores the left & right Many and a list of Any which must be the same length and types in xs typelist.
-- newtype EmitEqMany (xs :: [Type]) r = EmitEqMany ([Any], [Any])

-- instance Reiterate EmitEqMany (x ': xs) where
--     -- use of tail here is safe as we are guaranteed the length from the typelist
--     reiterate (EmitEqMany (ls, rs)) = EmitEqMany (Partial.tail ls, Partial.tail rs)

-- instance Eq x => Emit EmitEqMany (x ': xs) Bool where
--     emit (EmitEqMany (ls, rs)) = l == r
--       where
--         -- use of front here is safe as we are guaranteed the length from the typelist
--         l = unsafeCoerce (Partial.head ls) :: x
--         r = unsafeCoerce (Partial.head rs) :: x

-- -- This version take too long to compile
-- eqMany
--     :: forall xs.
--        AFoldable (Collector EmitEqMany xs) Bool
--     => Many xs -> Many xs -> [Bool]
-- eqMany (Many _ lm) (Many _ rm) = afoldr (:) []
--     (Collector (EmitEqMany @xs (snd <$> M.toAscList lm, snd <$> M.toAscList rm)))

-- -- | Two 'Many's are equal if all their fields equal
-- instance AFoldable (Collector EmitEqMany xs) Bool => Eq (Many xs) where
--     lt == rt = foldl' (\e z -> bool False z e) True eqs
--       where
--         eqs = eqMany lt rt

-- This version is 9 seconds to compile
instance Eq (ManyList '[]) where
    _ == _ = True
    {-# NOINLINE (==) #-}

instance (Eq x, Eq (ManyList xs)) => Eq (ManyList (x ': xs)) where
    ls == rs = case front' ls == front' rs of
        False -> False
        _ -> (aft' ls) == (aft' rs)
    -- GHC compilation is SLOW if INLINE is on... too many type instances?
    {-# NOINLINE (==) #-}


-- | Two 'Many's are equal if all their fields equal
instance Eq (ManyList xs) => Eq (Many xs) where
    lt == rt = toManyList lt == toManyList rt
    {-# NOINLINE (==) #-}


instance Show (ManyList '[]) where
    showsPrec d _ = showParen (d > cons_prec) $ showString "nul"
      where
        cons_prec = 5 -- infixr 5 prefix

instance (Show x, Show (ManyList xs)) => Show (ManyList (x ': xs)) where
    showsPrec d ls@(ManyList xs) =
        showParen (d > cons_prec) $
        showsPrec (cons_prec + 1) v .
        showString " ./ " .
        showsPrec cons_prec (aft' ls)
      where
        cons_prec = 5 -- infixr 5 prefix
        -- use of front here is safe as we are guaranteed the length from the typelist
        v = unsafeCoerce (Partial.head xs) :: x
    -- GHC compilation is SLOW if INLINE is on... too many type instances?
    {-# NOINLINE showsPrec #-}

-- | Two 'Many's are equal if all their fields equal
instance Show (ManyList xs) => Show (Many xs) where
    showsPrec d xs = showsPrec d (toManyList xs)
    {-# NOINLINE showsPrec #-}



-- The below version is twice as slow to compile!
-- eqMany
--     :: forall xs. Many xs -> Many xs -> Collector EmitEqMany xs Bool
-- eqMany (Many _ lm) (Many _ rm) = Collector (EmitEqMany @xs (snd <$> M.toAscList lm, snd <$> M.toAscList rm))

-- -- | Two 'Many's are equal if all their fields equal
-- instance AFoldable (Collector EmitEqMany xs) Bool => Eq (Many xs) where
--     lt == rt = afoldr (\e z -> bool False z e) True eqs
--       where
--         eqs = eqMany lt rt
-----------------------------------------------------------------------

-- | Stores the left & right Many and a list of Any which must be the same length and types in xs typelist.
newtype EmitOrdMany (xs :: [Type]) r = EmitOrdMany ([Any], [Any])

instance Reiterate EmitOrdMany (x ': xs) where
    -- use of tail here is safe as we are guaranteed the length from the typelist
    reiterate (EmitOrdMany (ls, rs)) = EmitOrdMany (Partial.tail ls, Partial.tail rs)

instance Ord x => Emit EmitOrdMany (x ': xs) Ordering where
    emit (EmitOrdMany (ls, rs)) = compare l r
      where
        -- use of front here is safe as we are guaranteed the length from the typelist
        l = unsafeCoerce (Partial.head ls) :: x
        r = unsafeCoerce (Partial.head rs) :: x

ordMany
    :: forall xs.
       AFoldable (Collector EmitOrdMany xs) Ordering
    => Many xs -> Many xs -> [Ordering]
ordMany (Many _ lm) (Many _ rm) = afoldr (:) []
    (Collector (EmitOrdMany @xs (snd <$> M.toAscList lm, snd <$> M.toAscList rm)))

-- | Two 'Many's are ordered by 'compare'ing their fields in index order
instance (Eq (Many xs), AFoldable (Collector EmitOrdMany xs) Ordering) => Ord (Many xs) where
    compare lt rt = foldr (\o z -> case o of
                                       EQ -> z
                                       o' -> o') EQ ords
      where
        ords = ordMany lt rt

-----------------------------------------------------------------------

-- -- | Internally uses [Any] like Via, except also handle the empty type list.
-- newtype EmitShowMany (xs :: [Type]) r = EmitShowMany [Any]

-- instance Reiterate EmitShowMany (x ': xs) where
--     -- use of tail here is safe as we are guaranteed the length from the typelist
--     reiterate (EmitShowMany xxs) = EmitShowMany (Partial.tail xxs)

-- instance Emit EmitShowMany '[] ShowS where
--     emit _ = showString "nul"


-- instance Show x => Emit EmitShowMany (x ': xs) ShowS where
--     emit (EmitShowMany xxs) = showsPrec (cons_prec + 1) v . showString " ./ "
--       where
--         -- use of front here is safe as we are guaranteed the length from the typelist
--         v = unsafeCoerce (Partial.head xxs) :: x
--         cons_prec = 5 -- infixr 5 cons

-- showMany
--     :: forall xs.
--        AFoldable (Collector0 EmitShowMany xs) ShowS
--     => Many xs -> ShowS
-- showMany (Many _ m) = afoldr (.) id (Collector0 (EmitShowMany @xs (snd <$> M.toAscList m)))

-- -- | @read "5 ./ False ./ 'X' ./ Just 'O' ./ nul" == (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'@
-- instance AFoldable (Collector0 EmitShowMany xs) ShowS => Show (Many xs) where
--     showsPrec d t = showParen (d > cons_prec) $ showMany t
--       where
--         cons_prec = 5 -- infixr 5 cons

-----------------------------------------------------------------------

newtype EmitReadMany (xs :: [Type]) r = EmitReadMany Int

instance Reiterate EmitReadMany (x ': xs) where
    reiterate (EmitReadMany i) = EmitReadMany (i + 1)

instance Emit EmitReadMany '[] (ReadPrec [(Int, WrappedAny)]) where
    emit (EmitReadMany _) = do
        lift $ L.expect (Ident "nul")
        pure []

instance Read x => Emit EmitReadMany (x ': xs) (ReadPrec [(Int, WrappedAny)]) where
    emit (EmitReadMany i) = do
        a <- readPrec @x
        lift $ L.expect (Symbol "./")
        pure [(i, WrappedAny (unsafeCoerce a))]

readMany
    :: forall xs.
       AFoldable (Collector0 EmitReadMany xs) (ReadPrec [(Int, WrappedAny)])
    => Proxy (xs :: [Type]) -> ReadPrec [(Int, WrappedAny)]
readMany _ = afoldr (liftA2 (++)) (pure []) (Collector0 (EmitReadMany @xs 0))

-- | @read "5 ./ False ./ 'X' ./ Just 'O' ./ nul" == (5 :: Int) './' False './' \'X' './' Just \'O' './' 'nul'@
instance (AFoldable (Collector0 EmitReadMany xs) (ReadPrec [(Int, WrappedAny)])) =>
         Read (Many xs) where
    readPrec =
        parens $
        prec 10 $ do
            xs <- readMany @xs Proxy
            pure (Many 0 (fromList' xs))

-- | 'WrappedAny' avoids the following:
-- Illegal type synonym family application in instance: Any
newtype WrappedAny = WrappedAny Any
