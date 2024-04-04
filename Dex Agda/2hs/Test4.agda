
module Test4 where

open import Data.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.List
open import Data.List.Properties
--open import Relation.Nullary

axiom1 : ∀ (n m : ℕ) -> (n ≡ᵇ m) ≡ true -> n ≡ m
axiom1 zero zero pf = refl
axiom1 (suc n) (suc m) pf = cong suc (axiom1 n m pf)

n≡ᵇn : ∀ (n : ℕ) -> (n ≡ᵇ n) ≡ false -> ⊥
n≡ᵇn (suc n) pf = n≡ᵇn n pf

axiom2 : ∀ (n m : ℕ) -> (n ≡ᵇ m) ≡ false -> n ≢ m
axiom2 zero zero () x
axiom2 zero (suc m) pf ()
axiom2 (suc n) (suc .n) pf refl = n≡ᵇn n pf

open import ListInsertLib ℕ _≡ᵇ_ axiom1 axiom2

test1 : insertList (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ [])
        ≡ 4 ∷ 5 ∷ 6 ∷ 1 ∷ 2 ∷ 3 ∷ []
test1 = refl

test2 : insertList' (1 ∷ 2 ∷ 3 ∷ []) (4 ∷ 5 ∷ 6 ∷ [])
        ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
test2 = refl

test3 : insertList (1 ∷ 6 ∷ 2 ∷ 3 ∷ 4 ∷ []) (4 ∷ 5 ∷ 6 ∷ [])
        ≡ 4 ∷ 5 ∷ 6 ∷ 1 ∷ 2 ∷ 3 ∷ []
test3 = refl


