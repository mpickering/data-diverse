[![Hackage](https://img.shields.io/hackage/v/data-diverse.svg)](https://hackage.haskell.org/package/data-diverse)
[![Build Status](https://secure.travis-ci.org/louispan/data-diverse.png?branch=master)](http://travis-ci.org/louispan/data-diverse)

"Data.Diverse.Many" is an extensible record for any size encoded efficiently as (Seq Any).

"Data.Diverse.Which" polymorphic variant of possibilities encoded as (Int, Any).

Provides getters, setters, projection, injection, folds, and catamorphisms;
accessed by type or index or label.

Refer to [ManySpec.hs](https://github.com/louispan/data-diverse/blob/master/test/Data/Diverse/ManySpec.hs) and [WhichSpec.hs](https://github.com/louispan/data-diverse/blob/master/test/Data/Diverse/WhichSpec.hs) for example usages.

Iso, Lens and Prisms are provided in [data-diverse-lens](http://hackage.haskell.org/package/data-diverse-lens)


# Changelog

* 0.1.0.0
    Initial version represented as (Int, Data.Map Int Any)

* 0.4.0.0
    Removed Emit typeclass, breaking renames. Added label accessors.

* 0.5.0.0
    Renamed type level functions module from Type to TypeLevel

* 0.6.0.0
    Moved lens to data-diverse-lens

* 0.7.0.0
    Removed NOINLINE pragmas.
    Changed internal representation to (Int, Data.IntMap Any) for a 2.5x append speedup.

* 0.8.0.0
    Changed internal representation to (Data.Seq Any) for a further 2x append speedup.
    Added NFData instance for Many

* 0.8.1.0
    Added NFData instance for Which
    Forgot to expose Many.sliceL and Many.sliceR
