open import Relation.Binary.Bundles
open import Data.Bool hiding (_≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])

module ListInsertLib (A : Set) (_==_ : A → A → Bool)
       (axiom1 : ∀ (x y : A) → (x == y) ≡ true → x ≡ y)
       (axiom2 : ∀ (x y : A) → (x == y) ≡ false → x ≢ y ) where

open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Base
open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans ; n≤1+n )
open import Relation.Nullary using (¬_)

open import Data.Empty
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties
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
open import Data.List.Relation.Unary.Unique.Setoid S
open import Data.List.Relation.Binary.Subset.Setoid S
open import Data.List.Relation.Binary.Subset.Setoid.Properties


insert : A → List A → List A
insert a [] = a ∷ []
insert a (x ∷ l) =
  if a == x then (x ∷ l)
            else x ∷ (insert a l)

--xs@(x ∷ l)
--a ∷ l replaced by xs

--what if x ∷ l instead?

--needs separation?

insertList : List A → List A → List A
insertList [] l = l
insertList (x ∷ l₁) l₂ = insertList l₁ (insert x l₂)

⊆-cons : ∀ {l₁ l₂ : List A} (x : A) → l₁ ⊆  l₂ → l₁ ⊆ (x ∷ l₂)
⊆-cons x p1 p2 = there (p1 p2)


insert-lem₁ : ∀ (x : A) (l : List A) → l ⊆ insert x l
insert-lem₁ x [] = λ ()
insert-lem₁ x (y ∷ l) with x == y in eq
... | false = λ { (here px) → here px ; (there p) → there (insert-lem₁ x l p)}
... | true rewrite axiom1 x y eq = λ z → z

insert-lem₂ : ∀ (x : A) (l : List A) → x ∈ insert x l
insert-lem₂ x [] = here refl
insert-lem₂ x (y ∷ l) with x == y in eq
... | false = there (insert-lem₂ x l) 
... | true = here (axiom1 x y eq)

insert-lem₃ : ∀ {x y : A} (l : List A) → x ∈ l → x ∈ insert y l
insert-lem₃ {x} {y} (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite axiom1 y z eq | px = here refl
insert-lem₃ {x} {y} (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem₃ l pf)
...| true = there pf

insert-lem₄ : ∀ {x : A} (l : List A) -> x ∉ l → insert x l ≡ l ++ [ x ]
insert-lem₄ {x} [] pf = refl
insert-lem₄ {x} (y ∷ l) pf with x == y in eq
...| false = cong (y ∷_) (insert-lem₄ l (λ z → pf (there z)))
...| true rewrite axiom1 x y eq = ⊥-elim (pf (here refl)) 


insertList-sublem : ∀ (l₁ l₂ : List A) (x : A) → x ∈ l₂ → x ∈ insertList l₁ l₂
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l₁) l₂ x pf = insertList-sublem l₁ (insert y l₂) x (insert-lem₃ l₂ pf)

insertList-lem₁ : ∀ (l₁ l₂ : List A) → l₁ ⊆ insertList l₁ l₂
insertList-lem₁ [] l₂ = λ ()
insertList-lem₁ (x ∷ l₁) l₂ 
  = λ { (here refl) → insertList-sublem l₁ (insert x l₂) x (insert-lem₂ x l₂) ;
        (there y) → insertList-lem₁ l₁ (insert x l₂) y}


insertList-lem₂ : ∀ (l₁ l₂ : List A) → l₂ ⊆ insertList l₁ l₂
insertList-lem₂ [] l₂ = λ z → z
insertList-lem₂ (x ∷ l₁) l₂ = ⊆-trans S (insert-lem₁ x l₂) (insertList-lem₂ l₁ (insert x l₂))

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
subset-del p nin sub y = ∈-del p (λ {refl → nin y}) (sub y)


∈[] : ∀ {x} → x ∈ [] → ⊥
∈[] ()


{-
test-lem : ∀ {l1 l2 : List A} -> l1 ⊆ l2 -> length l1 ≤ length l2
test-lem = {!!}

--incorrect because  (1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ⊆ (1 ∷ 2 ∷ 3 ∷ [])

-}

unique-lem : ∀ {l₁ l₂ : List A} → l₁ ⊆ l₂ → Unique l₁ → length l₁ ≤ length l₂
unique-lem p [] = z≤n
unique-lem {x ∷ xs} {[]} p (u ∷ us) = ⊥-elim (∈[] (p (here refl)))
unique-lem {x ∷ xs} {y ∷ ys} p (u ∷ us) rewrite sym (length-del (p (here refl)))
  = s≤s (unique-lem (subset-del (p (here refl)) (All¬⇒¬Any u) (λ z → p (there z))) us)


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

-- Unique ys -> insertList xs ys ≡ nub (ys ++ xs)

-- Unique ys ? -> length (nub (ys ++ xs)) ≥ length (nub xs)

-- Unique xs -> length (nub (ys ++ xs)) ≥ length xs !!

-- Unique ys -> insert x ys ≡ nub (ys ++ [ x ]) --start here -> write spec with nub (dedidable deduplicate) ++ length


-- make your own good nub?

++insertLemma : ∀ (l₁ l₂ : List A) → l₁ ∅ l₂ → Unique l₁ → insertList l₁ l₂ ≡ l₂ ++ l₁
++insertLemma [] l₂ pf₁ pf₂ = sym (++-identityʳ l₂)
++insertLemma (x ∷ l₁) l₂ (p₁ ∷ pf₁) (p₂ ∷ pf₂) rewrite insert-lem₄ l₂ p₁
              | ++insertLemma l₁ (l₂ ++ x ∷ []) (∅-lemma x l₁ l₂ pf₁ (All¬⇒¬Any p₂)) pf₂
              = ++lemma x l₂ l₁


insertList' : List A -> List A -> List A
insertList' l₁ [] = l₁
insertList' l₁ (x ∷ l₂) = insertList' (insert x l₁) l₂


filterᵇ : (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

deduplicateᵇ : (A → A → Bool) → List A → List A
deduplicateᵇ r [] = []
deduplicateᵇ r (x ∷ xs) = x ∷ filterᵇ (not ∘ r x) (deduplicateᵇ r xs)

nub : List A → List A
nub = deduplicateᵇ _==_



==refl : ∀ (x : A) → x == x ≡ true
==refl x with x == x in eq
...| true = refl
...| false = ⊥-elim (axiom2 x x eq refl)

∉-lem : ∀ {y x : A} {zs : List A} → y ∉ (x ∷ zs) → y ∉ zs
∉-lem p = λ t → p (there t)

{-
∉-lem' : ∀ {y x z : A} {ts : List A} → y ∉ (x ∷ z ∷ ts) → y ∉ (x ∷ ts)
∉-lem' p = λ { (here px) → p (here px)
             ; (there f) → p (there (there f))}
-}

filter-lem' : ∀ {y : A} {xs : List A} → y ∉ xs → filterᵇ (λ z → not (y == z)) xs ≡ xs
filter-lem' {y} {[]} p = refl
filter-lem' {y} {x ∷ xs} p with y == x in eq
...| true = ⊥-elim (p (here (axiom1 y x eq)))
...| false = cong (x ∷_) (filter-lem' (∉-lem p))

{-
∉-lem2 : ∀ {y x : A} {zs : List A} → y ∉ x ∷ zs → x ∉ zs → x ∉ zs ++ y ∷ []
∉-lem2 {y} {x} {[]} p1 p2 = λ { (here px) → p1 (here (sym px))}
∉-lem2 {y} {x} {x₁ ∷ zs} p1 p2 = λ { (here px) → p2 (here px)
                                   ; (there t) → ∉-lem2 (∉-lem' p1) (∉-lem p2) t}
-}
∉-lem2 : ∀ {y x : A} {zs : List A} → y ≢ x → x ∉ zs → x ∉ zs ++ y ∷ []
∉-lem2 {y} {x} {[]} p1 p2 = λ { (here px) → p1 (sym px)}
∉-lem2 {y} {x} {x₁ ∷ zs} p1 p2 = λ { (here px) → p2 (here px)
                                   ; (there t) → ∉-lem2 p1 (∉-lem p2) t}

nub-lem : ∀ {y : A} {xs : List A} → Unique xs → y ∉ xs → nub (xs ++ y ∷ []) ≡ xs ++ y ∷ []
nub-lem {y} {[]} [] p2 = refl
nub-lem {y} {x ∷ xs} (p ∷ p1) p2 rewrite nub-lem p1 (∉-lem p2) | filter-lem' (∉-lem2 (λ z → p2 (here z)) (All¬⇒¬Any p)) = refl

filter-lem : ∀ {y : A} {xs : List A} → y ∉ xs → filterᵇ (λ z → not (y == z)) (xs ++ y ∷ []) ≡ xs
filter-lem {y} {[]} pf rewrite ==refl y = refl
filter-lem {y} {x ∷ xs} pf with y == x in eq
...| true = ⊥-elim (pf (here (axiom1 y x eq)))
...| false = cong (x ∷_) (filter-lem (∉-lem pf))


filterNub-lem : ∀ {y : A} {xs : List A} → Unique xs → y ∉ xs → xs ≡ filterᵇ (λ z → not (y == z)) (nub (xs ++ y ∷ []))
filterNub-lem p1 p2 rewrite nub-lem p1 p2 | filter-lem p2 = refl

{-
filterNub-lem' : ∀ {y : A} {xs : List A} → Unique xs → y ∉ xs → xs ≡ filterᵇ (λ z → not (y == z)) (nub xs)
filterNub-lem' p1 p2 = {!!}
-}
--rewrite nub-lem p1 p2 | filter-lem p2 = refl


filter∈-lem : ∀ {y x : A} {zs : List A} → y ∈ filterᵇ (λ t → not (x == t)) zs → y ∈ zs
filter∈-lem {y} {x} {z ∷ zs} p with x == z in eq
...| true = there (filter∈-lem p)
filter∈-lem {y} {x} {z ∷ zs} (here px) | false = here px
filter∈-lem {y} {x} {z ∷ zs} (there p) | false = there (filter∈-lem p)

∉nub-lem : ∀ {y : A} {xs : List A} → y ∉ xs → y ∉ nub xs
∉nub-lem {y} {[]} p = p
∉nub-lem {y} {x ∷ xs} p  
         = λ { (here px) → ⊥-elim (p (here px))
             ; (there z) → ∉nub-lem (∉-lem p) (filter∈-lem z) }

∉filter-lem : ∀ {y x : A} {zs : List A} → y ∉ zs → y ∉ ((filterᵇ (λ t → not (x == t))) zs)
∉filter-lem {y} {x} {[]} p = p
∉filter-lem {y} {x} {z ∷ zs} p with x == z in eq
...| true = λ t → p (there (filter∈-lem t))
...| false = λ { (here px) → p (here px)
               ; (there t) → p (there (filter∈-lem t))}


insertU-lem : ∀ {y : A} {xs : List A} → Unique xs → insert y xs ≡ nub (xs ++ [ y ])
insertU-lem {xs = []} p = refl
insertU-lem {y} {x ∷ xs} (p ∷ ps) with y == x in eq
...| true rewrite axiom1 y x eq | sym (filterNub-lem ps (All¬⇒¬Any p))= refl
...| false rewrite insertU-lem {y} {xs} ps = cong (x ∷_) (sym (filter-lem' (∉nub-lem (∉-lem2 (axiom2 y x eq) (All¬⇒¬Any p))))) 




nubLength-sublem : ∀ (xs ys : List A) -> length (nub (ys ++ xs)) ≡ length (nub (xs ++ ys))
nubLength-sublem [] [] = refl
nubLength-sublem [] (x ∷ ys) rewrite ++-identityʳ ys = refl
nubLength-sublem (x ∷ xs) [] rewrite ++-identityʳ xs = refl 
nubLength-sublem (x ∷ xs) (y ∷ ys) = {!!}
{--}
--rewrite nubLength-sublem (x ∷ xs) ys = {!!} --cong suc {!!} --refl

nubUnique-lem : ∀ {xs} → Unique xs → nub xs ≡ xs
nubUnique-lem [] = refl
nubUnique-lem {x ∷ xs} (p ∷ ps) rewrite nubUnique-lem ps = cong (x ∷_) (filter-lem' (λ y → All¬⇒¬Any p y))


length-filterᵇ : ∀ (xs : List A) (f : A → Bool)  → length (filterᵇ f xs) ≤ length xs
length-filterᵇ [] f = z≤n
length-filterᵇ (x ∷ xs) f with f x
...| true = s≤s (length-filterᵇ xs f)
...| false = ≤-trans (length-filterᵇ xs f) (n≤1+n (length xs))

jij : ∀ {x y : A} {zs : List A} → All (¬_ ∘ _≡_ x) (y ∷ zs) → All (¬_ ∘ _≡_ x) zs
jij {zs = zs} (px ∷ p) = p


asdd : ∀ {x y : A} {xs : List A} -> Unique (x ∷ xs)
  → length xs ≤ length (filterᵇ (λ z → not (y == z)) (nub (x ∷ xs)))
asdd {x} {y} {xs} (p ∷ ps) with y == x in eq
...| true rewrite axiom1 y x eq | filter-lem' {x} {nub xs} (∉nub-lem (All¬⇒¬Any p)) |
                   filter-lem' {x} {nub xs} (∉nub-lem (All¬⇒¬Any p)) | nubUnique-lem ps = ≤-refl
asdd {x} {y} {[]} (p ∷ ps) | false = z≤n
asdd {x} {y} {x' ∷ xs} ((px ∷ p) ∷ ps) | false with x == x' in eq2
...| true rewrite axiom1 x x' eq2 = ⊥-elim (All¬⇒¬Any (px ∷ p) (here refl))
{-rewrite axiom1 x x' eq2 | filter-lem' {x'} {nub xs} (∉nub-lem (All¬⇒¬Any p')) |
                   filter-lem' {x'} {nub xs} (∉nub-lem (All¬⇒¬Any p')) = s≤s {!asdd!}-}
...| false rewrite filter-lem' {x} {(filterᵇ (λ x₁ → not (x' == x₁)) (deduplicateᵇ _==_ xs))}
                   (∉filter-lem (∉nub-lem (All¬⇒¬Any p))) = s≤s (asdd ps)


double-filter : ∀ (x : A) (zs : List A) ->
       (filterᵇ (λ y → not (x == y)) (filterᵇ (λ z → not (x == z)) zs)) ≡
       (filterᵇ (λ y → not (x == y)) zs)
double-filter x [] = refl
double-filter x (z ∷ zs) with x == z in eq
...| true = double-filter x zs
...| false rewrite eq = cong (z ∷_ ) (double-filter x zs)

--defilter : ∀ {x : A} (zs ts : List A) ->  (filterᵇ (λ y → not (x == y)) zs

asff : ∀ {x : A} (xs ys : List A) -> Unique xs
  → length (filterᵇ (λ z → not (x == z)) (nub (xs))) ≤ length (filterᵇ (λ z → not (x == z)) (nub (ys ++ xs)))
asff {x} xs [] p = ≤-refl
asff {x} xs (y ∷ ys) p with x == y in eq
...| true rewrite axiom1 x y eq | double-filter y (deduplicateᵇ _==_ (ys ++ xs)) = asff xs ys p
...| false = {!!}

nubLength-lem : ∀ {xs ys} → Unique xs -> length (nub (ys ++ xs)) ≥ length xs
nubLength-lem {[]} {ys} p = z≤n
nubLength-lem {x ∷ xs} {[]} (p ∷ ps) rewrite nubUnique-lem ps | filter-lem' λ y → All¬⇒¬Any p y = s≤s ≤-refl
--rewrite nubUnique-lem p = {!!}
nubLength-lem {x ∷ xs} {y ∷ ys} (p ∷ ps) = s≤s {!!} --(≤-trans {!!} {!!} ) --(nubLength-lem {ys = ys} ps) )

--other way around???

{-
sublem1 : ∀ {z} (xs ys : List A) → length (nub xs) ≤ length (nub (xs ++ ys))
          → length (filterᵇ (not ∘ _==_ z) (nub xs)) ≤ length (filterᵇ (not ∘ _==_ z) (nub (xs ++ ys)))
sublem1 [] ys p = z≤n
sublem1 {z} (x ∷ xs) ys (s≤s p) with z == x in eq
...| true = {!!} --sublem1 xs ys p
...| false = s≤s {!!} --(sublem1 xs ys p)

-- insert x ys -> x ∈ ys

--

--  length (xs ++ ys) ≥ length xs

lem1 : ∀ (xs ys : List A) → length (nub (xs ++ ys)) ≥ length (nub xs)
lem1 [] ys = z≤n
lem1 (x ∷ xs) ys = s≤s {!!}
-}
--(sublem1 {!xs!} {!!} {!!}) --s≤s {!!} --(lem1 {!!} ys)


{-
∈-++⁺ˡ : ∀ {v xs ys} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ = Any.++⁺ˡ

  ∈-++⁺ʳ : ∀ {v} xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = Any.++⁺ʳ

  ∈-++⁻ : ∀ {v} xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
  ∈-++⁻ = Any.++⁻
-}

--length-++ : ∀ (xs : List A) {ys} → length (xs ++ ys) ≡ length xs + length ys
--m≤m+n : ∀ m n → m ≤ m + n

--length (nub (nub xs ++ nub ys)) <= length (nub xs) + length (nub ys)
--distinct us && distinct vs -> length (nub (us ++ vs)) <= length us + length vs

-- insertList xs ys = nub (ys ++ xs)
--  ∀ (l₁ l₂ : List A) (pf : Unique l₁) → (length (insertList l₁ l₂) ≥ length l₁)

--prop : ∀ (xs ys : List A) → length (insertList' xs ys) ≡ length 



{-[] [] = z≤n
unique-lem (px ∷ sub) (x ∷ un) rewrite sym (length-del px) = s≤s {!!}-}
--rewrite sym (length-del px) = s≤s (unique-lem (subset-del px {!!} sub) un)


{-
insertList-lem₂ (x ∷ l₁) [] = λ ()
insertList-lem₂ (x ∷ l₁) (y ∷ l₂) with x == y in eq
...| false = λ { (here refl) → insertList-sublem l₁ (y ∷ insert x l₂) y (here refl) ;
                 (there z) → insertList-lem₂ l₁ (y ∷ insert x l₂) (there (insert-lem₃ l₂ z)) }
...| true = λ { (here refl) → insertList-sublem l₁ (x ∷ l₂) y (here (sym (axiom1 x y eq))) ;
                (there z) → insertList-lem₂ l₁ (x ∷ l₂) (there z)}
  -}

--⊆-trans (insert-lem₁ x l₂) (insertList-lem₂ l₁ (insert x l₂))
  

{-



{-
asdf : ∀ (xs ys : List A) -> insertList' xs ys ≡ xs ++ (deduplicateᵇ _==_ ys)
asdf xs [] = sym (++-identityʳ xs)
asdf xs (y ∷ ys) = {!!}

nub∷-lem : ∀ (y : A) (xs : List A) → length (nub (y ∷ xs)) ≡ suc (length ((filterᵇ (λ z → not (y == z))) (nub xs)))
nub∷-lem y [] = refl
nub∷-lem y (x ∷ xs) = refl
-}
-}
