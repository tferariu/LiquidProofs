open import Haskell.Prelude
--open import Data.Map

module MWE3 where

open import MWE2 Nat

--postulate
--  bar : Set
--  getFoo : bar -> Nat


--{-# COMPILE AGDA2HS bar to Bar #-}
--{-# COMPILE AGDA2HS getFoo #-}

foobar : FooBar -> Nat
foobar x = getFoo x

{-# COMPILE AGDA2HS foobar #-}
