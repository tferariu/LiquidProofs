module ListLemmaLib where

open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans )
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Data.Empty
open import Data.List.Relation.Unary.All as All

import Agda.Builtin.Nat as NAT

--add, get known to community, get regognized

variable
  a b c d : Set

record Eq (a : Set) : Set where
  infix 4 _==_ _/=_
  field
    _==_ : a → a → Bool

  _/=_ : a → a → Bool
  x /= y = not (x == y)

open Eq {{...}} public


--ask agda2hs what to do for decision procedures
--convert from == to =? and back, see which is easier (probably =? to ==)


instance
  iEqN : Eq ℕ
  iEqN ._==_ = NAT._==_ 
{--}

--have it as as module parameter
--fill in later as parameter
postulate
  axiom : {{eqA : Eq a}} -> ∀ (x y : a) -> (x == y) ≡ true -> x ≡ y
  axiom2 : {{eqA : Eq a}} -> ∀ (x y : a) -> (x == y) ≡ false -> ¬ x ≡ y

--get from library
_∈_ : ∀ (x : a) (xs : List a) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ (x : a) (xs : List a) → Set
x ∉ xs = ¬ (x ∈ xs)

--build on library, check 100% if it is in the standard library
data Unique {b : Set} : List b → Set where
  root : Unique []
  _::_ : {x : b} {l : List b} → x ∉ l → Unique l → Unique (x ∷ l)

--where is this in the library, if at all
_⊆_ : List  a → List a → Set
l₁ ⊆ l₂ = All (_∈ l₂) l₁

--also check in library (particularly fresh Lists)
insert : {{eqA : Eq a}} -> a -> List a -> List a
insert a [] = a ∷ []
insert a (x ∷ l) =
  if a == x then a ∷ l
            else x ∷ (insert a l)

⊆-cons : (x : a){l₁ l₂ : List a} → l₁ ⊆  l₂ → l₁ ⊆ (x ∷ l₂)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : (l : List a) → l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷  ⊆-cons x (⊆-refl l)

⊆-trans : {l₁ l₂ l₃ : List a} → l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃
⊆-trans [] p₂ = []
⊆-trans (px ∷ p₁) p₂ = All.lookup p₂ px ∷  ⊆-trans  p₁ p₂

--be 100% these are not in fresh lists,currently 96%
insert-lem₁ : {{eqA : Eq a}} → (x : a)(l : List a) → l ⊆ insert x l
insert-lem₁ x [] = []
insert-lem₁ x (y ∷ l) with x == y in eq
... | false = here refl ∷ ⊆-cons y (insert-lem₁ x l)
... | true rewrite axiom x y eq = (here refl) ∷ ⊆-cons y (⊆-refl l)

insert-lem₂ : {{eqA : Eq a}} → (x : a)(l : List a) → x ∈ insert x l
insert-lem₂ x [] = here refl
insert-lem₂ x (x₁ ∷ l) with x == x₁ in eq
... | false = there (insert-lem₂ x l) 
... | true = here refl

insert-lem₃ : {{eqA : Eq a}} → (x y : a)(l : List a) → x ∈ l → x ∈ insert y l
insert-lem₃ {{ eqA = eqA }} x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite axiom y z eq | px = here refl
insert-lem₃ {{ eqA = eqA }} x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem₃ x y l pf)
...| true = there pf

insertList : {{eqA : Eq a}} -> List a -> List a -> List a
insertList [] l = l
insertList (x ∷ l1) l2 = insertList l1 (insert x l2)

del : ∀{x} (l : List a) → x ∈ l → List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) → suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong suc (length-del p) 

∈-del : ∀{x y}{l₂ : List a} (p : x ∈ l₂) → x ≢ y →  y ∈ l₂ → y ∈ del l₂ p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l₁ l₂ : List a} (p : x ∈ l₂) → (x ∉ l₁) → l₁ ⊆ l₂ → l₁ ⊆ del l₂ p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e → n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {{eqA : Eq a}}{l₁ l₂ : List a} → l₁ ⊆ l₂ → Unique l₁ → length l₁ ≤ length l₂
unique-lem [] root = z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = s≤s (unique-lem (subset-del px x sub) un)


insertList-sublem : {{eqA : Eq a}}(l₁ l₂ : List a) (x : a) -> x ∈ l₂ -> x ∈ insertList l₁ l₂
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l₁) l₂ x pf = insertList-sublem l₁ (insert y l₂) x (insert-lem₃ x y l₂ pf)

insertList-lem₁ : {{eqA : Eq a}} → (l₁ l₂ : List a) → l₁ ⊆ insertList l₁ l₂
insertList-lem₁ {{ eqA = eqA }} [] l₂ = []
insertList-lem₁ {{ eqA = eqA }} (x ∷ l₁) l₂ 
  = insertList-sublem l₁ (insert x l₂) x (insert-lem₂ x l₂) ∷ insertList-lem₁ l₁ (insert x l₂)

insertList-lem₂ : {{eqA : Eq a}} → (l₁ l₂ : List a) → l₂ ⊆ insertList l₁ l₂
insertList-lem₂ {{ eqA = eqA }} [] l₂ = ⊆-refl l₂
insertList-lem₂ {{ eqA = eqA }} (x ∷ l₁) l₂
  = ⊆-trans (insert-lem₁ x l₂) (insertList-lem₂ l₁ (insert x l₂))


uniqueInsertLemma : {{eqA : Eq a}} → ∀ (l₁ l₂ : List a) (pf : Unique l₁)
                    → (length (insertList l₁ l₂) ≥ length l₁)
uniqueInsertLemma l₁ l₂ pf = unique-lem (insertList-lem₁ l₁ l₂) pf

test : insertList (4 ∷ 5 ∷ 6 ∷ []) (1 ∷ 2 ∷ 3 ∷ []) ≡ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []
test = {!!}

{-
--rebuild l1 into l2 not l2 into l1
insertList : {{eqA : Eq a}} -> List a -> List a -> List a
insertList l1 [] = l1
insertList l1 (x ∷ l2) = insert x (insertList l1 l2)




insertList-lem₂ : {{eqA : Eq a}} → (l₁ l₂ : List a) → l₂ ⊆ insertList l₁ l₂
insertList-lem₂ {{ eqA = eqA }} l₁ [] = []
insertList-lem₂ {{ eqA = eqA }} l₁ (x₁ ∷ l₂) 
  = insert-lem₂ x₁ (insertList l₁ l₂) ∷ ⊆-trans (insertList-lem₂ l₁ l₂) (insert-lem₁  x₁ (insertList l₁ l₂))



uil :  {{eqA : Eq a}} -> ∀ (l1 l2 : List a) (pf : Unique l2) -> (length l2 ≤ length (insertList l1 l2))
uil l1 l2 pf = unique-lem (insertList-lem₂ l1 l2) pf


----------------------------------------------------------------------------

--claim: insertList [1 2 3] [4 5 6] ≡ [456123], but want [123456]

--relate insertList to _++_ and nub

insertList' : {{eqA : Eq a}} -> List a -> List a -> List a
insertList' l1 [] = l1
insertList' l1 (x ∷ l2) = insertList' (insert x l1) l2





-}
