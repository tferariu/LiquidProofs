open import Haskell.Prelude
--open import Haskell.Test Integer

module MWE' where

--Foo = Nat
--Bar = Int

--{-# COMPILE AGDA2HS Foo #-}
--{-# COMPILE AGDA2HS Bar #-}

--FooBar = Foo × Bar

data Datum : Set where
  Holding : Datum
  Collecting : Nat -> Integer -> Datum


{-# COMPILE AGDA2HS Datum #-}

record ScriptContext : Set where
    field
        outputDatum : Datum
        other : Nat
        stuff : Nat


getOther : ScriptContext -> Nat
getOther ctx = ScriptContext.other ctx

validator : Datum -> Nat -> ScriptContext -> Bool
validator dat b ctx = getOther ctx == b


{-# COMPILE AGDA2HS validator #-}

--{-# COMPILE AGDA2HS foo #-}


--{-# COMPILE AGDA2HS getFoo #-}
--{-# COMPILE AGDA2HS validator #-}
