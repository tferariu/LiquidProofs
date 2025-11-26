{-# OPTIONS --no-eta-equality #-}

open import Haskell.Prelude

module MWE2 (Foo : Set) where

record FooBar : Set where
    field
        bar1 : Foo
        bar2 : Nat
open FooBar public

--{-# COMPILE AGDA2HS FooBar existing-class #-}
--{-# COMPILE AGDA2HS bar1  #-}
--{-# COMPILE AGDA2HS bar2 #-}

getFoo : FooBar -> Foo
getFoo x = FooBar.bar1 x


--{-# COMPILE AGDA2HS getFoo #-}
