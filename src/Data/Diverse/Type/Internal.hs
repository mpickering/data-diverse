{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Diverse.Type.Internal where

import Data.Kind
import GHC.TypeLits

-- | Get the first position of a type (indexed by 1)
-- Will return 0 if @x@ doesn't exists in @xs@.
type family PositionOfImpl (i :: Nat) (x :: k) (xs :: [k]) :: Nat where
   PositionOfImpl i x (x ': xs) = 1 + i
   PositionOfImpl i y (x ': xs) = PositionOfImpl (i + 1) y xs
   PositionOfImpl i x '[] = 0

-- | Get the first index of a type from a list
type family IndexOfImpl (ctx :: [k]) (accum :: Nat) (x :: k) (xs :: [k]) :: Nat where
   IndexOfImpl ctx accum x (x ': xs) = accum
   IndexOfImpl ctx accum y (x ': xs) = IndexOfImpl ctx (accum + 1) y xs
   IndexOfImpl ctx accum y '[] = TypeError ('Text "IndexOf error: ‘"
                                      ':<>: 'ShowType y
                                      ':<>: 'Text "’"
                                      ':<>: 'Text " is not a member of "
                                      ':<>: 'Text "‘"
                                      ':<>: 'ShowType ctx
                                      ':<>: 'Text "’")

-- | Searches for y in ys
-- if not found, than use y, and repeat search with next (y ': ys) in ctx
-- else if found, then don't use y, then repeat search with next (y ': ys) in ctx
type family NubImpl (ctx :: [k]) (y :: k) (ys :: [k]) :: [k] where
    NubImpl '[] y '[] = y ': '[]
    NubImpl '[] y (y ': xs) = '[]
    NubImpl (x ': xs) y '[] = y ': NubImpl xs x xs
    NubImpl (x ': xs) y (y ': ys) = NubImpl xs x xs
    NubImpl ctx y (x ': xs) = NubImpl ctx y xs

-- | Errors if a type exists in a typelist
type family MissingImpl (ctx :: [k]) (y :: k) (xs :: [k]) :: Constraint where
    MissingImpl ctx y '[] = ()
    MissingImpl ctx x (x ': xs) = TypeError ('Text "Unique error: ‘"
                                             ':<>: 'ShowType x
                                             ':<>: 'Text "’"
                                             ':<>: 'Text " is a duplicate in "
                                             ':<>: 'Text "‘"
                                             ':<>: 'ShowType ctx
                                             ':<>: 'Text "’")
    MissingImpl ctx y (x ': xs) = (MissingImpl ctx y xs)

-- | Ensures that the type list contain unique types
type family IsDistinctImpl (dummy :: Constraint) (ctx :: [k]) (xs :: [k]) :: Constraint where
    IsDistinctImpl dummy ctx '[] = ()
    IsDistinctImpl dummy ctx (x ': xs) = IsDistinctImpl (MissingImpl ctx x xs) ctx xs

-- | Ensures that @x@ only ever appears once in @xs@
type family UniqueImpl (ctx :: [k]) (x :: k) (xs :: [k]) :: Constraint where
    UniqueImpl ctx x '[] = ()
    UniqueImpl ctx x (x ': xs) = MissingImpl ctx x xs
    UniqueImpl ctx x (y ': xs) = UniqueImpl ctx x xs

-- | Indexed access into the list
type family KindAtIndexImpl (orig :: Nat) (ctx :: [k]) (n :: Nat) (xs :: [k]) :: k where
    KindAtIndexImpl i ctx 0 '[] = TypeError ('Text "KindAtIndex error: Index ‘"
                                       ':<>: 'ShowType i
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " is out of bounds of "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ctx
                                       ':<>: 'Text "’")
    KindAtIndexImpl i ctx 0 (x ': xs) = x
    KindAtIndexImpl i ctx n (x ': xs) = KindAtIndexImpl i ctx (n - 1) xs

-- | Labelled access into the list
type family KindAtLabelImpl (l :: k1) (ctx :: [k2]) (xs :: [k2]) :: k2 where
    KindAtLabelImpl l ctx '[] = TypeError ('Text "KindAtLabel error: Label ‘"
                                       ':<>: 'ShowType l
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " is not found in "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ctx
                                       ':<>: 'Text "’")
    KindAtLabelImpl l ctx (tagged l x ': xs) = tagged l x
    KindAtLabelImpl l ctx (x ': xs) = KindAtLabelImpl l ctx xs

-- | Ensures two typelists are the same length
type family SameLengthImpl (ctx :: [k1]) (cty :: [k2]) (xs :: [k1]) (yx :: [k2]) :: Constraint where
    SameLengthImpl as bs '[] '[] = ()
    SameLengthImpl as bs (x ': xs) (y ': ys) = SameLengthImpl as bs xs ys
    SameLengthImpl as bs xs ys = TypeError ('Text "SameLength error: ‘"
                                            ':<>: 'ShowType as
                                            ':<>: 'Text "’"
                                            ':<>: 'Text " is not the same length as "
                                            ':<>: 'Text "‘"
                                            ':<>: 'ShowType bs
                                            ':<>: 'Text "’")

-- | Reverse list
type family ReverseImpl (accum :: [k]) (leftover :: [k]) (xs :: [k]) :: [k] where
    ReverseImpl accum '[] '[] = accum
    ReverseImpl accum (y ': ys) xs = ReverseImpl accum ys (y ': xs)
    ReverseImpl accum '[] (x ': xs) = ReverseImpl (x ': accum) '[] xs

-- | The typelist @xs@ without the type at Nat @n@. @n@ must be within bounds of @xs@
type family WithoutIndexImpl (accum :: [k]) (i :: Nat) (ctx :: [k]) (n :: Nat) (xs :: [k]) :: [k] where
    WithoutIndexImpl accum i ctx 0 '[] = ReverseImpl '[] '[] accum
    WithoutIndexImpl accum i ctx n '[] = TypeError ('Text "WithoutIndex error: Index ‘"
                                       ':<>: 'ShowType i
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " is out of bounds of "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ctx
                                       ':<>: 'Text "’")
    WithoutIndexImpl accum i ctx 0 (x ': xs) = ReverseImpl '[] xs accum -- no @x@
    WithoutIndexImpl accum i ctx n (x ': xs) = WithoutIndexImpl (x ': accum) i ctx (n - 1) xs

-- | The typelist @xs@ without the type at Nat @n@ replaced by @y@. @n@ must be within bounds of @xs@
type family ReplaceIndexImpl (accum :: [k]) (i :: Nat) (ctx :: [k]) (n :: Nat) (y :: k) (xs :: [k]) :: [k] where
    ReplaceIndexImpl accum i ctx n y '[] = TypeError ('Text "ReplaceIndex error: Index ‘"
                                       ':<>: 'ShowType i
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " is out of bounds of "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ctx
                                       ':<>: 'Text "’")
    ReplaceIndexImpl accum i ctx 0 y (x ': xs) = ReverseImpl '[] (y ': xs) accum
    ReplaceIndexImpl accum i ctx n y (x ': xs) = ReplaceIndexImpl (x ': accum) i ctx (n - 1) y xs

-- | The typelist @xs@ with the first @x@ replaced by @y@. It is okay for @x@ not to exist in @xs@
type family ReplaceImpl (accum :: [k]) (x :: k) (y :: k) (xs :: [k]) :: [k] where
    ReplaceImpl accum x y '[] = ReverseImpl '[] '[] accum
    ReplaceImpl accum x y (x ': xs) = ReverseImpl '[] (y ': xs) accum
    ReplaceImpl accum x y (z ': xs) = ReplaceImpl (z ': accum) x y xs

-- | The typelist @zs@ with the first @xs@ replaced by @ys@.
-- @xs@ must be the same size as @ys@
type family ReplacesImpl (accum :: [k]) (xs' :: [k]) (ys' :: [k]) (xs :: [k]) (ys :: [k]) (zs :: [k]) :: [k] where
    ReplacesImpl accum xs' ys' xs ys '[] = ReverseImpl '[] '[] accum
    ReplacesImpl accum xs' ys' '[] '[] (z ': zs) = ReplacesImpl (z ': accum) xs' ys' xs' ys' zs
    ReplacesImpl accum xs' ys' (x ': xs) (y ': ys) (x ': zs) = ReplacesImpl (y ': accum) xs' ys' xs' ys' zs
    ReplacesImpl accum xs' ys' (x ': xs) (y ': ys) (z ': zs) = ReplacesImpl accum xs' ys' xs ys (z ': zs)
    ReplacesImpl accum xs' ys' xs ys zs = TypeError ('Text "Replaces error: ‘"
                                       ':<>: 'ShowType xs'
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " must be the same size as "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ys'
                                       ':<>: 'Text "’")

-- | The type @x@ replaced by an @y@ if an @n@ matches @i@.
type family ReplaceIfIndex (ns :: [Nat]) (ys :: [k]) (i :: Nat) (x :: k) :: k where
    ReplaceIfIndex '[] ys i x = x
    ReplaceIfIndex ns '[] i x = x
    ReplaceIfIndex (n ': ns) (y ': ys) n x = y
    ReplaceIfIndex (n ': ns) (y ': ys) i x = ReplaceIfIndex ns ys i x

-- | The typelist @xs@ replaced by @ys@ at the indices @ns@. @ns@ and @ys@ must be the same length. @ns@ must be within bounds of @xs@
type family ReplacesIndexImpl (accum :: [k]) (i :: Nat) (ns :: [Nat]) (ys :: [k]) (xs :: [k]) :: [k] where
    ReplacesIndexImpl accum i ns ys '[] = ReverseImpl '[] '[] accum
    ReplacesIndexImpl accum i '[] '[] xs = ReverseImpl '[] xs accum
    ReplacesIndexImpl accum i ns ys (x ': xs) = ReplacesIndexImpl (ReplaceIfIndex ns ys i x ': accum) (i + 1) ns ys xs
    ReplacesIndexImpl accum i ns ys xs = TypeError ('Text "ReplacesIndex error: ‘"
                                       ':<>: 'ShowType ns
                                       ':<>: 'Text "’"
                                       ':<>: 'Text " must be the same size as "
                                       ':<>: 'Text "‘"
                                       ':<>: 'ShowType ys
                                       ':<>: 'Text "’")

-- | Zips up @xs@ and @ys@, which must be the same length
type family ZipImpl (accum :: [k]) (xs' :: [k]) (ys' :: [k]) (xs :: [k]) (ys :: [k]) :: [k] where
    ZipImpl accum xs' ys' '[] '[] = ReverseImpl '[] '[] accum
    ZipImpl accum xs' ys' (x ': xs) (y ': ys) = ZipImpl ((x, y) ': accum) xs' ys' xs ys
    ZipImpl accum xs' ys' xs ys = TypeError ('Text "Zip error: ‘"
                              ':<>: 'ShowType xs'
                              ':<>: 'Text "’"
                              ':<>: 'Text " must be the same size as "
                              ':<>: 'Text "‘"
                              ':<>: 'ShowType ys'
                              ':<>: 'Text "’")

type family InitImpl (accum :: [k]) (xs :: [k]) :: [k] where
    InitImpl accum '[]  = TypeError ('Text "Init error: empty type list")
    InitImpl accum '[x] = ReverseImpl '[] '[] accum
    InitImpl accum (x ': xs) = InitImpl (x ': accum) xs


type family AppendImpl (accum :: [k]) (xs :: [k]) (ys :: [k]) :: [k] where
    AppendImpl accum '[] ys = ReverseImpl '[] ys accum
    AppendImpl accum (x ': xs) ys = AppendImpl (x ': accum) xs ys

type family KindsAtIndicesImpl (accum :: [k]) (ns :: [Nat]) (xs :: [k]) :: [k] where
    KindsAtIndicesImpl accum '[] xs = ReverseImpl '[] '[] accum
    KindsAtIndicesImpl accum (n ': ns) xs = KindsAtIndicesImpl (KindAtIndexImpl n xs n xs ': accum) ns xs

type family WithoutImpl (accum ::[k]) (x :: k) (xs :: [k]) :: [k] where
    WithoutImpl accum x '[] = ReverseImpl '[] '[] accum
    WithoutImpl accum x (x ': xs) = ReverseImpl '[] xs accum
    WithoutImpl accum x (y ': xs) = WithoutImpl (y ': accum) x xs
