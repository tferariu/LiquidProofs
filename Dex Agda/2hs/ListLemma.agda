module ListLemma where

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Agda.Builtin.Equality
open import Relation.Nullary
--open import Data.List.Relation.Unary.Unique.Setoid --??

variable
  a b c d : Set

record Eq (a : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : a → a → Bool

  _/=_ : a → a → Bool
  x /= y = not (x == y)

open Eq ⦃...⦄ public

postulate
  axiom : {{eqA : Eq a}} -> ∀ (x y : a) -> (x == y) ≡ true -> x ≡ y
  axiom2 : {{eqA : Eq a}} -> ∀ (x y : a) -> (x == y) ≡ false -> ¬ x ≡ y


_∈_ : ∀ (x : a) (xs : List a) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ (x : a) (xs : List a) → Set
x ∉ xs = ¬ (x ∈ xs)

data Unique {b : Set} : List b → Set where
  root : Unique []
  _::_ : {x : b} {l : List b} → x ∉ l → Unique l → Unique (x ∷ l)

insert : {{eqA : Eq a}} -> a -> List a -> List a
insert a [] = a ∷ []
insert a (x ∷ l) =
  if a == x then a ∷ l
            else x ∷ (insert a l)



insertList : {{eqA : Eq a}} -> List a -> List a -> List a
insertList l1 [] = l1
insertList l1 (x ∷ l2) = insert x (insertList l1 l2)


insertList' : {{eqA : Eq a}} -> List a -> List a -> List a
insertList' l1 [] = l1
insertList' l1 (x ∷ l2) = insertList' (insert x l1) l2

--uniqueInsertL : {{eqA : Eq a}} -> ∀ (l : List a) (n : ℕ) ... length (insert x l) __ length l

uniqueInsert : {{eqA : Eq a}} -> ∀ (l1 l2 : List a) (n : ℕ) (pf1 : Unique l2) (pf2 : (length l2 ≥ n)) -> (length (insertList l1 l2) ≥ n)
uniqueInsert l1 [] .zero pf1 z≤n = z≤n
uniqueInsert l1 (x ∷ l2) n (x₁ :: pf1) pf2 = {!!}

lemma1 : {{eqA : Eq a}} -> ∀ (x : a) (l : List a) -> x ∉ l -> length (insert x l) ≡ suc (length l)
lemma1 = {!!}

--lemma2 : -> 

uil :  {{eqA : Eq a}} -> ∀ (l1 l2 : List a) (pf : Unique l2) -> (length (insertList l1 l2) ≥ length l2)
uil l1 [] pf = z≤n
uil l1 (x ∷ l2) pf = {!!}



lemmaR : {{eqA : Eq a}} -> ∀ (l : List a) -> insertList [] l ≡ reverse l
lemmaR [] = refl
lemmaR (x ∷ l) rewrite lemmaR l = {!!}

uil' :  {{eqA : Eq a}} -> ∀ (l : List a) (pf : Unique l) -> (length (insertList [] l) ≥ length l)
uil' [] pf = z≤n
uil' (x ∷ l) pf = {!!}





{-
uniqueInsert' : {{eqA : Eq a}} -> ∀ (l1 l2 : List a) (n : ℕ) (pf1 : Unique l2) (pf2 : (length l2 ≥ n)) -> (length (insertList' l1 l2) ≥ n)
uniqueInsert' l1 [] .zero pf1 z≤n = z≤n
uniqueInsert' l1 (x ∷ l2) n pf1 pf2 = {!!}





insertSomething : {{eqA : Eq a}} -> ∀ (x : a) (l : List a) -> length (insert x l) ≥ 0
insertSomething x [] = z≤n
insertSomething x (y ∷ l) with x == y
... | false = z≤n 
... | true = z≤n

lemma1 : {{eqA : Eq a}} -> ∀ (x : a) (l : List a) (n : ℕ) (pf1 : length l ≥ n) (pf2 : x ∉ l) -> suc n ≤ length (insert x l)
lemma1 x [] n pf1 pf2 = s≤s pf1
lemma1 x (y ∷ l) n pf1 pf2 with x == y
lemma1 x (y ∷ l) zero pf1 pf2 | false = s≤s (insertSomething x l)
lemma1 x (y ∷ l) (suc n) (s≤s pf1) pf2 | false = s≤s (lemma1 x l n pf1 (λ z → pf2 (there z)))
... | true = {!!}

_≡?_ : {{eqA : Eq a}} -> ∀ (x y : a) -> Dec (x ≡ y)
_≡?_ x y = {!!}

uniqueInsertEmpty : {{eqA : Eq a}} -> ∀ (l : List a) (n : ℕ) (pf1 : Unique l) (pf2 : (length l ≥ n)) -> (length (insertList [] l) ≥ n)
uniqueInsertEmpty [] .zero pf1 z≤n = z≤n
uniqueInsertEmpty (x ∷ l) zero (p :: pf1) pf2 = {!!}
uniqueInsertEmpty (x ∷ l) (suc n) (p :: pf1) pf2 = lemma1 {!!} {!!} {!!} {!!} {!!}
-}
