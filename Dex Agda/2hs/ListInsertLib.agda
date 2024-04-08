open import Relation.Binary.Bundles
open import Data.Bool hiding (_≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])

module ListInsertLib (A : Set) (_==_ : A → A → Bool)
       (axiom1 : ∀ (x y : A) → (x == y) ≡ true → x ≡ y)
       (axiom2 : ∀ (x y : A) → (x == y) ≡ false → x ≢ y ) where

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans )
open import Relation.Nullary using (¬_)

open import Data.Empty
open import Data.List.Relation.Unary.All as All
open import Agda.Primitive


open import Data.List.Base
open import Function.Base

open import Relation.Binary

S : Setoid lzero lzero
S = record { Carrier = A ; _≈_ = _≡_ ;
             isEquivalence = record { refl = refl ;
                                      sym = sym ;
                                      trans = trans } }

open import Data.List.Membership.Setoid S

{-
_∈_ : ∀ (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)
-}

insert : A → List A → List A
insert a [] = a ∷ []
insert a (x ∷ l) =
  if a == x then a ∷ l
            else x ∷ (insert a l)

insertList : List A → List A → List A
insertList [] l = l
insertList (x ∷ l₁) l₂ = insertList l₁ (insert x l₂)

data Unique : List A → Set where
  root : Unique []
  _::_ : {x : A} {l : List A} → x ∉ l → Unique l → Unique (x ∷ l)

_⊆_ : List A → List A → Set
l₁ ⊆ l₂ = All (_∈ l₂) l₁

⊆-cons : ∀ {l₁ l₂ : List A} (x : A) → l₁ ⊆  l₂ → l₁ ⊆ (x ∷ l₂)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : ∀ (l : List A) → l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷  ⊆-cons x (⊆-refl l)

⊆-trans : ∀ {l₁ l₂ l₃ : List A} → l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃
⊆-trans [] p₂ = []
⊆-trans (px ∷ p₁) p₂ = All.lookup p₂ px ∷ ⊆-trans  p₁ p₂


insert-lem₁ : ∀ (x : A) (l : List A) → l ⊆ insert x l
insert-lem₁ x [] = []
insert-lem₁ x (y ∷ l) with x == y in eq
... | false = here refl ∷ ⊆-cons y (insert-lem₁ x l)
... | true rewrite axiom1 x y eq = (here refl) ∷ ⊆-cons y (⊆-refl l)

insert-lem₂ : ∀ (x : A) (l : List A) → x ∈ insert x l
insert-lem₂ x [] = here refl
insert-lem₂ x (x₁ ∷ l) with x == x₁ in eq
... | false = there (insert-lem₂ x l) 
... | true = here refl

insert-lem₃ : ∀ (x y : A) (l : List A) → x ∈ l → x ∈ insert y l
insert-lem₃ x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite axiom1 y z eq | px = here refl
insert-lem₃ x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem₃ x y l pf)
...| true = there pf

insert-lem₄ : ∀ (x : A) (l : List A) -> x ∉ l → insert x l ≡ l ++ [ x ]
insert-lem₄ x [] pf = refl
insert-lem₄ x (y ∷ l) pf with x == y in eq
...| false = cong (y ∷_) (insert-lem₄ x l (λ z → pf (there z)))
...| true rewrite axiom1 x y eq = ⊥-elim (pf (here refl)) 


del : ∀ {x} (l : List A) → x ∈ l → List A
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀ {x} {l : List A} (p : x ∈ l) → suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong suc (length-del p) 

∈-del : ∀ {x y} {l : List A} (p : x ∈ l) → x ≢ y →  y ∈ l → y ∈ del l p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀ {x} {l₁ l₂ : List A} (p : x ∈ l₂) → (x ∉ l₁) → l₁ ⊆ l₂ → l₁ ⊆ del l₂ p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e → n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : ∀ {l₁ l₂ : List A} → l₁ ⊆ l₂ → Unique l₁ → length l₁ ≤ length l₂
unique-lem [] root = z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = s≤s (unique-lem (subset-del px x sub) un)


insertList-sublem : ∀ (l₁ l₂ : List A) (x : A) → x ∈ l₂ → x ∈ insertList l₁ l₂
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l₁) l₂ x pf = insertList-sublem l₁ (insert y l₂) x (insert-lem₃ x y l₂ pf)

insertList-lem₁ : ∀ (l₁ l₂ : List A) → l₁ ⊆ insertList l₁ l₂
insertList-lem₁ [] l₂ = []
insertList-lem₁ (x ∷ l₁) l₂ 
  = insertList-sublem l₁ (insert x l₂) x (insert-lem₂ x l₂) ∷ insertList-lem₁ l₁ (insert x l₂)

insertList-lem₂ : ∀ (l₁ l₂ : List A) → l₂ ⊆ insertList l₁ l₂
insertList-lem₂ [] l₂ = ⊆-refl l₂
insertList-lem₂ (x ∷ l₁) l₂
  = ⊆-trans (insert-lem₁ x l₂) (insertList-lem₂ l₁ (insert x l₂))


uniqueInsertLemma : ∀ (l₁ l₂ : List A) (pf : Unique l₁)
                    → (length (insertList l₁ l₂) ≥ length l₁)
uniqueInsertLemma l₁ l₂ pf = unique-lem (insertList-lem₁ l₁ l₂) pf



--relate insertList to _++_ and nub

_∅_ : List A → List A → Set
l₁ ∅ l₂ = All (_∉ l₂) l₁

∉-reduce : ∀ (x y : A) (l : List A) → x ∉ (y ∷ l) → x ∉ l
∉-reduce x y [] pf = λ ()
∉-reduce x y (z ∷ l) pf = λ t → pf (there t)

∉-lemma : ∀ (x y : A) (l : List A) → y ≢ x → x ∉ l → x ∉ (l ++ y ∷ [])
∉-lemma x y [] pf₁ pf₂ = λ { (here px) → pf₁ (sym px)}
∉-lemma x y (z ∷ l) pf₁ pf₂ = λ { (here px) → pf₂ (here px)
                                ; (there py) → ∉-lemma x y l pf₁ (∉-reduce x z l pf₂) py} 

∅-lemma : ∀ (x : A) (l₁ l₂ : List A) → l₁ ∅ l₂ → x ∉ l₁ → l₁ ∅ (l₂ ++ x ∷ [])
∅-lemma x [] l₂ pf₁ pf₂ = []
∅-lemma x (y ∷ l₁) l₂ (p₁ ∷ pf₁) pf₂ with x == y in eq
...| true rewrite axiom1 x y eq = ⊥-elim (pf₂ (here refl)) 
...| false = (λ z → ∉-lemma y x l₂ ((axiom2 x y eq)) p₁ z) ∷ ∅-lemma x l₁ l₂ pf₁ (λ z → pf₂ (there z))

++lemma : ∀ (x : A) (l₁ l₂ : List A) -> (l₁ ++ x ∷ []) ++ l₂ ≡ l₁ ++ x ∷ l₂
++lemma x [] l₂ = refl
++lemma x (y ∷ l₁) l₂ = cong (y ∷_) (++lemma x l₁ l₂)

++insertLemma : ∀ (l₁ l₂ : List A) → l₁ ∅ l₂ → Unique l₁ → insertList l₁ l₂ ≡ l₂ ++ l₁
++insertLemma [] l₂ pf₁ pf₂ = sym (++-identityʳ l₂)
++insertLemma (x ∷ l₁) l₂ (p₁ ∷ pf₁) (p₂ :: pf₂) rewrite insert-lem₄ x l₂ p₁
              | ++insertLemma l₁ (l₂ ++ x ∷ []) (∅-lemma x l₁ l₂ pf₁ p₂) pf₂ = ++lemma x l₂ l₁


insertList' : List A -> List A -> List A
insertList' l₁ [] = l₁
insertList' l₁ (x ∷ l₂) = insertList' (insert x l₁) l₂


filterᵇ : (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

deduplicateᵇ : (A → A → Bool) → List A → List A
deduplicateᵇ r [] = []
deduplicateᵇ r (x ∷ xs) = x ∷ filterᵇ (not ∘ r x) (deduplicateᵇ r xs)

{-
asdf : ∀ (xs ys : List A) -> insertList' xs ys ≡ xs ++ (deduplicateᵇ _==_ ys)
asdf xs [] = sym (++-identityʳ xs)
asdf xs (y ∷ ys) = {!!}
-}

