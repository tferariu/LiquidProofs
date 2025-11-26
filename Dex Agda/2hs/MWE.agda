open import Haskell.Prelude
open import Haskell.Test Integer

module MWE where

--Foo = Nat
--Bar = Int

--{-# COMPILE AGDA2HS Foo #-}
--{-# COMPILE AGDA2HS Bar #-}

--FooBar = Foo × Bar

getFoo : Foo -> Bar -> FooBar
getFoo a b = a + b 

foo : Nat -> ScriptContext -> Bool
foo n ctx = newValue ctx == n

validator : Foo -> Integer -> ScriptContext -> Bool
validator f b ctx = newValue ctx == oldValue ctx && newDatum ctx == b


{-# COMPILE AGDA2HS foo #-}
{-# COMPILE AGDA2HS getFoo #-}
{-# COMPILE AGDA2HS validator #-}
