open import Agda.Builtin.Nat
open import Data.List

module test where

record Thing : Set where
    field
        list    : List Nat
        item    : Nat


processThing : Thing -> List Nat
processThing record { list = [] ; item = item } = []
processThing record { list = (x ∷ list) ; item = item } = {!if x == item then x else processThing!}

