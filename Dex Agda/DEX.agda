{-# OPTIONS --rewriting #-}

module DEX where

{-
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)

open import Data.List
open import Data.String
open import Data.Rational
open import Data.Maybe
open import Data.Integer

-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (dec-yes)
open import Data.Integer hiding (_⊔_) -- hiding (_≤_;)
open import Data.Rational  hiding (_⊔_) -- hiding (_≤_;)
open import Data.String
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core
open import Agda.Builtin.Equality --.Rewrite
-- open import Agda.Builtin.Sigma
-- open import Agda.Primitive

{-
data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A
-}


private variable A B C : Set

-- ** simple way
-- f : A → B → A × B
-- f a b = ⟨ a , b ⟩

-- g : A → B → B × A
-- g a b = ⟨ b , a ⟩

-- ** module way
-- module _ (a : A) (b : B) where
--  f : A × B
--  f = ⟨ a , b ⟩
--
--  g : B × A
--  g = ⟨ b , a ⟩

{-
infix 2 Σ-syntax

private variable a b : Level

Σ-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

infix 2 ∃-syntax

∃-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B
-}


data Currency : Set where
  C1    : Currency
  C2    : Currency
  Other : Currency

postulate
  -- Map ℕ ℤ
  Map : (A : Set) → (B : Set) → Set
  -- insertions
  insert : A -> B → Map A B → Map A B
  singleton : A -> B -> Map A B
  -- queries
  _∈_ : A → Map A B → Set
  _∈?_ : A → Map A B → Set
  query : ∀ (k : A) (m : Map A B) → B
  -- query : (k : A) (m : Map A B) {_ : k ∈ m} → B
  -- deletion
  _-ᵐ_ : Map A B → Map A B → Map A B
  _≤ᵐ_ : Map A B → Map A B → Set
  _≤?ᵐ_ : ∀ (m m′ : Map A B) → Dec (m ≤ᵐ m′)
  _~_ : (m : Map A B) (m′ : Map A B) {_ : m ≤ᵐ m′} → Map A B
  compute : Map A (Map B C) -> Currency -> Currency -> Map B (Map Currency C)
  sum : Map A B -> B
  -- key equality



  
record State : Set where
  field
    curr1 : Currency
    curr2 : Currency
    omap1 : Map ℚ ( Map String ℤ )
    omap2 : Map ℚ ( Map String ℤ )
    v1    : ℤ
    v2    : ℤ
    out   : Map String (Map Currency ℤ)
    pf    : curr1 ≢ curr2

open State

{-
data _cof_ : Currency -> State -> Set where

  first : ∀ {cur s}
    -> cur ≡ (curr1 s)
    --------------------
    -> cur cof s

  second : ∀ {cur s}
    -> cur ≡ (curr2 s)
    -------------------
    -> cur cof s


  neither : ∀ {cur s}
    ->
    ->
    ------------------
    -> 
-}


_c=?_ : ∀ (x y : Currency) -> Dec (x ≡ y)
C1 c=? C1 = yes refl
C1 c=? C2 = no (λ ())
C1 c=? Other = no (λ ())
C2 c=? C1 = no (λ ())
C2 c=? C2 = yes refl
C2 c=? Other = no (λ ())
Other c=? C1 = no (λ ())
Other c=? C2 = no (λ ())
Other c=? Other = yes refl

offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer st pkh v cur r =
  if (Dec.does (0ℤ Data.Integer.<? v))
    then if (Dec.does (0ℚ Data.Rational.<? r))
      then if (Dec.does (cur c=? (curr1 st)))
        then just (record st { omap1 = (insert r (singleton pkh v) (omap1 st)); v1 = (v1 st) Data.Integer.+ v } )
        else if (Dec.does (cur c=? (curr2 st)))
          then just (record st { omap2 = (insert r (singleton pkh v) (omap2 st)) ; v2 = (v2 st) Data.Integer.+ v } )
          else nothing
      else nothing
    else nothing

{-if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap1 = (insert r (singleton pkh v) (omap1 st)) } )
    else nothing
  else nothing
... | C2 = if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap2 = (insert r (singleton pkh v) (omap2 st)) } )
    else nothing
  else nothing
... | Other = nothing -}

{-
offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer st pkh v cur r with cur
... | C1 = if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap1 = (insert r (singleton pkh v) (omap1 st)) } )
    else nothing
  else nothing
... | C2 = if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap2 = (insert r (singleton pkh v) (omap2 st)) } )
    else nothing
  else nothing
... | Other = nothing



request : State -> Currency -> Map ℚ (Map String ℤ) -> Maybe State
request st cur smap with cur
... | C1 = if (Dec.does (smap ≤?ᵐ (omap1 st)))
  then just (record st { omap1 = (omap1 st) -ᵐ smap })
  else nothing
... | C2 = if (Dec.does (smap ≤?ᵐ (omap2 st)))
  then just (record st { omap2 = (omap2 st) -ᵐ smap })
  else nothing
... | Other = nothing
-}



request : State -> Currency -> Map ℚ (Map String ℤ) -> Maybe State
request st cur smap =
  if (Dec.does (cur c=? (curr1 st)))
    then if (Dec.does (smap ≤?ᵐ (omap1 st)))
      then just (record st { omap1 = (omap1 st) -ᵐ smap ; out = compute smap cur (curr2 st)
        ; v1 = (v1 st) Data.Integer.- sum(sum smap)}) -- VALUE
      else nothing
    else if (Dec.does (cur c=? (curr2 st)))
      then if (Dec.does (smap ≤?ᵐ (omap2 st)))
        then just (record st { omap2 = (omap2 st) -ᵐ smap ; out = compute smap cur (curr1 st)
          ; v2 = (v2 st) Data.Integer.- sum(sum smap)})
        else nothing
      else nothing



cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel st pkh v cur r =
  if (Dec.does (cur c=? (curr1 st)))
    then if ( Dec.does ( 0ℤ Data.Integer.<? v ) ∧ Dec.does ( v Data.Integer.≤? (query pkh (query r (omap1 st))) ) )
      then just (record st { omap1 = insert r (singleton pkh ( Data.Integer.- v )) (omap1 st)
        ; v1 = (v1 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
      else nothing
    else if (Dec.does (cur c=? (curr2 st)))
      then if ( Dec.does ( 0ℤ Data.Integer.<? v ) ∧ Dec.does ( v Data.Integer.≤? (query pkh (query r (omap2 st))) ) )
        then just (record st { omap2 = insert r (singleton pkh ( Data.Integer.- v )) (omap2 st)
          ; v2 = (v2 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
        else nothing
      else nothing





{-
cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel st pkh v cur r with cur
... | C1 = if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap1 st))) ))
  then just (record st { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 st))) Data.Integer.- v )) (omap1 st)} )
  else nothing
... | C2 = if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap2 st))) ))
  then just (record st { omap2 = insert r (singleton pkh ( (query pkh (query r (omap2 st))) Data.Integer.- v )) (omap2 st)} )
  else nothing
... | Other = nothing

-}



{-
(Dec.does ( v Data.Integer.≤? (((omap2 st) r) pkh) ))
  then just (record st { omap2 = (insertm r ( λ x -> if x == pkh then ( (((omap2 st) r) pkh) Data.Integer.- v) else 0ℤ) (omap2 st)) } )
 
-}


{-offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer st pkh v cur r =
  if (Dec.does (0ℤ Data.Integer.<? v))
    then if (Dec.does (0ℚ Data.Rational.<? r))
      then if (Dec.does (cur c=? (curr1 st)))
        then just (record st { omap1 = (insert r (singleton pkh v) (omap1 st)); v1 = (v1 st) Data.Integer.+ v } )
        else if (Dec.does (cur c=? (curr2 st)))
          then just (record st { omap2 = (insert r (singleton pkh v) (omap2 st)) ; v2 = (v2 st) Data.Integer.+ v } )
          else nothing
      else nothing
    else nothing-}



prop1 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} {cur : Currency}
      -> (cur ≢ (curr1 st) )
      -> (cur ≢ (curr2 st) )
      --------------------------
      -> (offer st pkh v cur r) ≡ nothing
prop1 {v = +_ zero} nc1 nc2 = refl
prop1 {v = -[1+_] n} nc1 nc2 = refl
prop1 {v = +[1+ n ]} {mkℚ (-[1+_] n₁) denominator-1 isCoprime} nc1 nc2 = refl
prop1 {v = +[1+ n ]} {mkℚ (+_ zero) denominator-1 isCoprime} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = curr2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 = ⊥-elim (nc1 refl)
prop1 {record { curr1 = C2 ; curr2 = C1  }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = C2 ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 = refl
prop1 {record { curr1 = C2 ; curr2 = Other }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 = refl
prop1 {record { curr1 = Other ; curr2 = C1  }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = Other ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 = refl
prop1 {record { curr1 = Other ; curr2 = Other }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C1} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = C1 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = C1 ; curr2 = Other  }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 = refl
prop1 {record { curr1 = C2 ; curr2 = curr2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 =  ⊥-elim (nc1 refl)
prop1 {record { curr1 = Other ; curr2 = C1 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 = refl
prop1 {record { curr1 = Other ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = Other ; curr2 = Other }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {C2} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = C1 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 = refl
prop1 {record { curr1 = C1 ; curr2 = Other }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = C2 ; curr2 = C1 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 = refl
prop1 {record { curr1 = C2 ; curr2 = C2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 = refl
prop1 {record { curr1 = C2 ; curr2 = Other }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 =  ⊥-elim (nc2 refl)
prop1 {record { curr1 = Other ; curr2 = curr2 }} {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {Other} nc1 nc2 =  ⊥-elim (nc1 refl)


prop2 : ∀ {st : State} {pkh : String} {curr : Currency} {r : ℚ} -> (offer st pkh -1ℤ curr r) ≡ nothing
prop2 = refl

prop3 : ∀ {st : State} {pkh : String} {v : ℤ} {curr : Currency} -> (offer st pkh v curr -½ ) ≡ nothing
prop3 {v = +_ zero}  = refl
prop3 {v = +[1+ n ]} = refl
prop3 {v = -[1+_] n} = refl


prop4 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} {cur : Currency}
      -> (cur ≢ (curr1 st) )
      -> (cur ≢ (curr2 st) )
      --------------------------
      -> (cancel st pkh v cur r) ≡ nothing
prop4 {record { curr1 = C1 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 =  ⊥-elim (nc1 refl)
prop4 {record { curr1 = C2 ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = C2 ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 = refl
prop4 {record { curr1 = C2 ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 = refl
prop4 {record { curr1 = Other ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = Other ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 = refl
prop4 {record { curr1 = Other ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C1} nc1 nc2 = refl
prop4 {record { curr1 = C1 ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 = refl
prop4 {record { curr1 = C1 ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = C1 ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 = refl
prop4 {record { curr1 = C2 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 =  ⊥-elim (nc1 refl)
prop4 {record { curr1 = Other ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 = refl
prop4 {record { curr1 = Other ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = Other ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = C2} nc1 nc2 = refl
prop4 {record { curr1 = C1 ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 = refl
prop4 {record { curr1 = C1 ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 = refl
prop4 {record { curr1 = C1 ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = C2 ; curr2 = C1 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 = refl
prop4 {record { curr1 = C2 ; curr2 = C2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 = refl
prop4 {record { curr1 = C2 ; curr2 = Other ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 =  ⊥-elim (nc2 refl)
prop4 {record { curr1 = Other ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }} {cur = Other} nc1 nc2 =  ⊥-elim (nc1 refl)



lemma1 : ∀ (n : ℕ) -> ( (n Data.Nat.<ᵇ ℕ.suc n) ≡ true )
lemma1 zero = refl
lemma1 (ℕ.suc n) = lemma1 n

lemma2 : ∀ (n : ℕ) -> ( (n Data.Nat.≤ᵇ n) ≡ true )
lemma2 zero = refl
lemma2 (ℕ.suc n) = lemma1 n

lemma3 : ∀ (z : ℤ) -> ( (Dec.does ( z Data.Integer.≤? z )) ≡ true )
lemma3 (+_ n) = lemma2 n
lemma3 (-[1+_] n) = lemma2 n

lemma' : ∀ (n : ℕ) (pkh : String) (r : ℚ) (s : State)
  -> query pkh (query r (omap1 s)) ≡ +[1+ n ]
  -> (Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap1 s))) ≡ true )
lemma' n pkh r s q rewrite q = lemma2 (ℕ.suc n)

lemmaC1 : ∀ (i j : Maybe State) -> (n : ℕ) (pkh : String) (r : ℚ) (s : State)
  -> (Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap1 s))) ≡ true )
  -> ( (if Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap1 s))) then i else j) ≡ i)
lemmaC1 i j n pkh r s d rewrite d = refl

lemma'' : ∀ (n : ℕ) (pkh : String) (r : ℚ) (s : State)
  -> query pkh (query r (omap2 s)) ≡ +[1+ n ]
  -> (Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap2 s))) ≡ true )
lemma'' n pkh r s q rewrite q = lemma2 (ℕ.suc n)

lemmaC2 : ∀ (i j : Maybe State) -> (n : ℕ) (pkh : String) (r : ℚ) (s : State)
  -> (Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap2 s))) ≡ true )
  -> ( (if Dec.does (+[1+ n ] Data.Integer.≤? query pkh (query r (omap2 s))) then i else j) ≡ i)
lemmaC2 i j n pkh r s d rewrite d = refl


dingus : ∀ (s : State) ->  (Dec.does (curr1 s c=? curr1 s)) ≡ true
dingus record { curr1 = C1 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out } = refl
dingus record { curr1 = C2 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out } = refl
dingus record { curr1 = Other ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out } = refl


lemmaCUR1 : ∀ (s : State) (n : ℕ) (pkh : String) (r : ℚ) {mst : Maybe State}
  -> (query pkh (query r (omap1 s)) ≡ (+ n))
  -> 0 Data.Nat.< n
  -> (if Dec.does (curr1 s c=? curr1 s) then
       if Dec.does (0ℤ Data.Integer.<? + n) ∧ Dec.does ( + n Data.Integer.≤? (query pkh (query r (omap1 s))) ) 
       then
       just
       (record
        { curr1 = curr1 s
        ; curr2 = curr2 s
        ; omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s)
        ; omap2 = omap2 s
        ; v1 = v1 s Data.Integer.+ Data.Integer.- (+ n)
        ; v2 = v2 s
        ; out = singleton pkh (singleton (curr1 s) (+ n))
        ; pf = pf s
        })
       else nothing
       else mst )
      ≡
      just
      (record
       { curr1 = curr1 s
       ; curr2 = curr2 s
       ; omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s)
       ; omap2 = omap2 s
       ; v1 = v1 s Data.Integer.- + n
       ; v2 = v2 s
       ; out = singleton pkh (singleton (curr1 s) (+ n))
       ; pf = pf s
       })
lemmaCUR1 record { curr1 = C1 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out } (ℕ.suc n) pkh r pf (Data.Nat.s≤s pn) rewrite pf | lemma1 n = refl
lemmaCUR1 record { curr1 = C2 ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out } (ℕ.suc n) pkh r pf (Data.Nat.s≤s pn) rewrite pf | lemma1 n = refl
lemmaCUR1 record { curr1 = Other ; curr2 = curr2 ; omap1 = omap1 ; omap2 = omap2 ; v1 = v1 ; v2 = v2 ; out = out }  (ℕ.suc n) pkh r pf (Data.Nat.s≤s pn) rewrite pf | lemma1 n = refl




lemmaCUR2 : ∀ (s : State) (n : ℕ) (pkh : String) (r : ℚ) {mst : Maybe State}
  -> (query pkh (query r (omap2 s)) ≡ (+ n))
  -> 0 Data.Nat.< n
  -> ( if Dec.does (curr2 s c=? curr1 s)
       then mst
       else if Dec.does (curr2 s c=? curr2 s)
         then if Dec.does (0ℤ Data.Integer.<? + n) ∧ Dec.does (+ n Data.Integer.≤? query pkh (query r (omap2 s)))
           then just (record
                     { curr1 = curr1 s
                     ; curr2 = curr2 s
                     ; omap1 = omap1 s
                     ; omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s)
                     ; v1 = v1 s
                     ; v2 = v2 s Data.Integer.- + n
                     ; out = singleton pkh (singleton (curr2 s) (+ n))
                     ; pf = pf s
                     })
           else nothing
         else nothing )
     ≡ just (record
            { curr1 = curr1 s
            ; curr2 = curr2 s
            ; omap1 = omap1 s
            ; omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s)
            ; v1 = v1 s
            ; v2 = v2 s Data.Integer.- + n
            ; out = singleton pkh (singleton (curr2 s) (+ n))
            ; pf = pf s
            })
lemmaCUR2 record { curr1 = C1 ; curr2 = C1 ; pf = pf } n pkh r prf pn = ⊥-elim (pf refl)
lemmaCUR2 record { curr1 = C1 ; curr2 = C2 ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = C1 ; curr2 = Other ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = C2 ; curr2 = C1 ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = C2 ; curr2 = C2 ; pf = pf } n pkh r prf pn = ⊥-elim (pf refl)
lemmaCUR2 record { curr1 = C2 ; curr2 = Other ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = Other ; curr2 = C1 ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = Other ; curr2 = C2 ; pf = pf } (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) rewrite prf | lemma2 (ℕ.suc n) = refl
lemmaCUR2 record { curr1 = Other ; curr2 = Other ; pf = pf } n pkh r prf pn = ⊥-elim (pf refl)

lemneg : ∀ (m n : ℕ) -> Data.Integer.- (+ m) Data.Integer.< +[1+ n ]
lemneg zero n = +<+ (Data.Nat.s≤s Data.Nat.z≤n)
lemneg (ℕ.suc m) n = -<+

obviously : ∀ (m n : ℕ) -> m Data.Nat.≤ n -> m Data.Nat.≤ ℕ.suc n
obviously zero n Data.Nat.z≤n = Data.Nat.z≤n
obviously (ℕ.suc n) (ℕ.suc m) (Data.Nat.s≤s p) = Data.Nat.s≤s (obviously n m p)

lemmonus : ∀ (m n : ℕ) -> m ∸ n Data.Nat.≤ m
lemmonus zero zero = Data.Nat.z≤n
lemmonus zero (ℕ.suc n) = Data.Nat.z≤n
lemmonus (ℕ.suc m) zero = Data.Nat.s≤s (lemmonus m zero)
lemmonus (ℕ.suc m) (ℕ.suc n) = obviously (m ∸ n) m (lemmonus m n)

lemplus : ∀ (m n : ℕ) -> m Data.Nat.≤ m Data.Nat.+ n
lemplus zero zero = Data.Nat.z≤n
lemplus (ℕ.suc m) zero = Data.Nat.s≤s (lemplus m zero)
lemplus zero (ℕ.suc n) = Data.Nat.z≤n
lemplus (ℕ.suc m) (ℕ.suc n) = Data.Nat.s≤s (lemplus m (ℕ.suc n))

lemminus : ∀ (z : ℤ) (n : ℕ)
  -> 0ℤ Data.Integer.< + n
  -> z Data.Integer.- + n  Data.Integer.< z
lemminus (+_ m) zero (+<+ ())
lemminus (+_ zero) (ℕ.suc n) p = -<+
lemminus +[1+ m ] (ℕ.suc n) p with m Data.Nat.<ᵇ n
... | true = lemneg (n ∸ m) m
... | false = +<+ (Data.Nat.s≤s (lemmonus m n))
lemminus (-[1+_] n) zero (+<+ ())
lemminus (-[1+_] zero) (ℕ.suc n) p = -<- (Data.Nat.s≤s Data.Nat.z≤n)
lemminus (-[1+_] (ℕ.suc m)) (ℕ.suc n) p = -<- (Data.Nat.s≤s (Data.Nat.s≤s (lemplus m n)))


-- Liquidity
prop5 : ∀ (s : State)
  -> ∃[ pkh ] ∃[ r ] ∃[ v ] (((query pkh (query r (omap1 s)) ≡ v) ⊎ (query pkh (query r (omap2 s)) ≡ v)) × (0ℤ Data.Integer.< v ) )
  -> ∃[ pkh ] ∃[ v ] ∃[ c ] ∃[ r ] ∃[ s' ] ( cancel s pkh v c r ≡ ( just s' ) × (v1 s' Data.Integer.< v1 s ⊎ v2 s' Data.Integer.< v2 s ) )
-----------------------------------------
--  -> cancel s pkh c r ≡ just s' 
-- ∨ (∃ c map s' -> reqest s c map = just s')
prop5 s ⟨ pkh , ⟨ r , ⟨ +_ n , ⟨ inj₁ x , +<+ m<n ⟩ ⟩ ⟩ ⟩ = ⟨ pkh , ⟨ (+_ n) , ⟨ (curr1 s) , ⟨ r , ⟨ ((record s { omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s) ; v1 = (v1 s) Data.Integer.- (+_ n) ; out = singleton pkh (singleton (curr1 s) (+_ n)) })) , ⟨ lemmaCUR1 s n pkh r x m<n , inj₁ (lemminus (v1 s) n (+<+ m<n)) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
prop5 s ⟨ pkh , ⟨ r , ⟨ +_ n , ⟨ inj₂ y , +<+ m<n ⟩ ⟩ ⟩ ⟩ = ⟨ pkh , ⟨ (+_ n) , ⟨ (curr2 s) , ⟨ r , ⟨ ((record s { omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s) ; v2 = (v2 s) Data.Integer.- (+_ n) ; out = singleton pkh (singleton (curr2 s) (+_ n)) })) , ⟨ lemmaCUR2 s n pkh r y m<n , inj₂ (lemminus (v2 s) n (+<+ m<n)) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


eqLemma : ∀ {a b c : Currency} -> a ≡ b -> a ≡ c -> b ≡ c
eqLemma ab ac rewrite ac = sym ab

postulate
  mapLemma : ∀ {map : Map ℚ (Map String ℤ)} {r : ℚ} {pkh : String} {v : ℤ} -> sum (sum (insert r (singleton pkh v) map)) ≡ sum (sum map) Data.Integer.+ v 


sumLemma : ∀ {map : Map ℚ (Map String ℤ)} {r : ℚ} {pkh : String} {x v : ℤ} -> sum (sum map) ≡ x -> x Data.Integer.+ v ≡ sum (sum (insert r (singleton pkh v) map))
sumLemma refl = sym mapLemma


--DaoProof
prop6 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((offer s pkh v cur r ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ ( offer s pkh v cur r ≡ nothing )
prop6 s pkh (+_ zero) cur r p1 p2 = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ (+_ zero) denominator-1 isCoprime) p1 p2 = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ +[1+ n₁ ] denominator-1 isCoprime) p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes x | yes z = ⊥-elim (pf s (eqLemma x z))
... | yes x | no t  = inj₁ ⟨ (record s { omap1 = (insert (mkℚ +[1+ n₁ ] denominator-1 isCoprime) (singleton pkh +[1+ n ]) (omap1 s)); v1 = (v1 s) Data.Integer.+ +[1+ n ] } ) , ⟨ refl , ⟨ sumLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | no y  | yes z = inj₁ ⟨ (record s { omap2 = (insert (mkℚ +[1+ n₁ ] denominator-1 isCoprime) (singleton pkh +[1+ n ]) (omap2 s)); v2 = (v2 s) Data.Integer.+ +[1+ n ] } ) , ⟨ refl , ⟨ p1 , (sumLemma (sym p2)) ⟩ ⟩ ⟩
... | no y  | no  t = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ (-[1+_] n₁) denominator-1 isCoprime) p1 p2 = inj₂ refl
prop6 s pkh (-[1+_] n) cur r p1 p2 = inj₂ refl



postulate
  mapMinusLemma : ∀ {map1 map2 : Map ℚ (Map String ℤ)} -> sum (sum (map1 -ᵐ map2)) ≡ sum (sum map1) Data.Integer.- sum (sum map2) 


minusMLemma : ∀ {map1 map2 : Map ℚ (Map String ℤ)} {x : ℤ} -> sum (sum map1) ≡ x -> x Data.Integer.- sum (sum map2) ≡ sum (sum (map1 -ᵐ map2))
minusMLemma refl = sym mapMinusLemma

prop7 : ∀ (s : State) (cur : Currency) (map : Map ℚ (Map String ℤ))
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((request s cur map ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ ( request s cur map ≡ nothing )
prop7 s cur map p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | map ≤?ᵐ (omap1 s) | map ≤?ᵐ (omap2 s)
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y))
... | yes _ | no _  | yes _ | _ = inj₁ ⟨ (record s { omap1 = (omap1 s) -ᵐ map ; out = compute map cur (curr2 s) ; v1 = (v1 s) Data.Integer.- sum(sum map)}) , ⟨ refl , ⟨ minusMLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | yes _ | no _  | no _  | _ = inj₂ refl
... | no _  | yes _ | _ | yes _ = inj₁ ⟨ (record s { omap2 = (omap2 s) -ᵐ map ; out = compute map cur (curr1 s) ; v2 = (v2 s) Data.Integer.- sum(sum map)}) , ⟨ refl , ⟨ p1 , minusMLemma (sym p2) ⟩ ⟩ ⟩
... | no _  | yes _ | _ | no _  = inj₂ refl
... | no _  | no  _ | _ | _ = inj₂ refl


prop8 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((cancel s pkh v cur r ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ (cancel s pkh v cur r ≡ nothing)
prop8 s pkh (+_ zero) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = inj₂ refl
... | no  _ | yes _ = inj₂ refl
... | no  _ | no  _ = inj₂ refl
prop8 s pkh (-[1+_] n) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = inj₂ refl
... | no  _ | yes _ = inj₂ refl
... | no  _ | no  _ = inj₂ refl
prop8 s pkh +[1+ n ] cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap1 s))) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap2 s)))
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y)) 
... | yes _ | no  _ | yes _ | _ = inj₁ ⟨ (record s { omap1 = insert r (singleton pkh ( Data.Integer.- +[1+ n ] )) (omap1 s) ; v1 = (v1 s) Data.Integer.- +[1+ n ] ; out = singleton pkh (singleton cur +[1+ n ]) }) , ⟨ refl , ⟨ sumLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | yes _ | no  _ | no _ | _  = inj₂ refl
... | no  _ | yes _ | _ | yes _ = inj₁ ⟨  (record s { omap2 = insert r (singleton pkh ( Data.Integer.- +[1+ n ] )) (omap2 s) ; v2 = (v2 s) Data.Integer.- +[1+ n ] ; out = singleton pkh (singleton cur +[1+ n ]) }) , ⟨ refl , ⟨ p1 , sumLemma (sym p2) ⟩ ⟩ ⟩
... | no  _ | yes _ | _ | no _  = inj₂ refl
... | no  _ | no  _ | _ | _ = inj₂ refl


{-

cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel st pkh v cur r =
  if (Dec.does (cur c=? (curr1 st)))
    then if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap1 st))) ))
      then just (record st { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 st))) Data.Integer.- v )) (omap1 st)
        ; v1 = (v1 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
      else nothing
    else if (Dec.does (cur c=? (curr2 st)))
      then if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap2 st))) ))
        then just (record st { omap2 = insert r (singleton pkh ( (query pkh (query r (omap2 st))) Data.Integer.- v )) (omap2 st)
          ; v2 = (v2 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
        else nothing
      else nothing
-}

nonsenseLemma : ∀ {a : ℤ} {n : ℕ} -> +[1+ n ] Data.Integer.≤ a -> a ≡ +0 -> ⊥
nonsenseLemma (+≤+ ()) refl

-- Authorized Access
prop9 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (query pkh (query r (omap1 s))) ≡ 0ℤ
  -> (query pkh (query r (omap2 s))) ≡ 0ℤ
  -> (cancel s pkh v cur r ≡ nothing)
prop9 s pkh (+_ zero) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = refl
... | no  _ | yes _ = refl
... | no  _ | no  _ = refl
prop9 s pkh (-[1+_] n) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = refl 
... | no  _ | yes _ = refl 
... | no  _ | no  _ = refl 
prop9 s pkh +[1+ n ] cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap1 s))) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap2 s)))
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y)) 
... | yes x | no  y | yes z | _ = ⊥-elim (nonsenseLemma z p1)
... | yes _ | no  _ | no _ | _  = refl
... | no  x | yes y | _ | yes z = ⊥-elim (nonsenseLemma z p2)
... | no  _ | yes _ | _ | no _  = refl
... | no  _ | no  _ | _ | _ = refl




{-
s ⟨ pkh , ⟨ r , ⟨ +[1+ n ] , ⟨ inj₁ x , +<+ m<n ⟩ ⟩ ⟩ ⟩ with (lemmaC1 (just (record s { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 s))) Data.Integer.-  +[1+ n ] )) (omap1 s)} )) nothing n pkh r s (lemma' n pkh r s x))
...| y = ⟨ pkh , ⟨  +[1+ n ] , ⟨ C1 , ⟨ r , ⟨ ( (record s { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 s))) Data.Integer.-  +[1+ n ] )) (omap1 s)} )) , {!!} ⟩ ⟩ ⟩ ⟩ ⟩

prop5 s ⟨ pkh , ⟨ r , ⟨ +[1+ n ] , ⟨ inj₂ y , +<+ m<n ⟩ ⟩ ⟩ ⟩ with (lemmaC2 (just (record s { omap2 = insert r (singleton pkh ( (query pkh (query r (omap2 s))) Data.Integer.-  +[1+ n ] )) (omap2 s)} )) nothing n pkh r s (lemma'' n pkh r s y))
...| x = ⟨ pkh , ⟨ +[1+ n ] , ⟨ C2 , ⟨ r , ⟨  record s { omap2 = insert r (singleton pkh ( (query pkh (query r (omap2 s))) Data.Integer.-  +[1+ n ] )) (omap2 s)} , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
-}
{-

-}

--with (x)
--... | z =  ⟨ pkh , ⟨  +[1+ n ] , ⟨ C1 , ⟨ r , ⟨ ( (record s { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 s))) Data.Integer.-  +[1+ n ] )) (omap1 s)} )) , {!!} ⟩ ⟩ ⟩ ⟩ ⟩

--subst? variables unify, terms don't variables at the bottom of inference rules

-- with ( lemma' n pkh r s x) in H
-- ...| y = ⟨ pkh , ⟨  +[1+ n ] , ⟨ C1 , ⟨ r , ⟨ ( (record s { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 s))) Data.Integer.-  +[1+ n ] )) (omap1 s)} )) , {!!} ⟩ ⟩ ⟩ ⟩ ⟩

-- with (lemma3  +[1+ n ] ) in H ... | y


-- ... | false = {!!}

ghjk : ∀ {n} -> n Data.Nat.≤ n
ghjk {zero} = Data.Nat.z≤n
ghjk {ℕ.suc n} = Data.Nat.s≤s ghjk

asdf : ∀ {n} -> +[1+ n ] Data.Integer.≤ +[1+ n ]
asdf = +≤+ (Data.Nat.s≤s ghjk)

-- test : ∀ (n : ℕ) -> (+[1+ n ] Data.Integer.≤? +[1+ n ]) ≡ yes (asdf)
-- test zero = {!!}
-- test (ℕ.suc n) = {!!}



{-
prop5 s = λ
      { ⟨ pkh , ⟨ r , ⟨ +[1+ n ] , ⟨ inj₁ x , +<+ m<n ⟩ ⟩ ⟩ ⟩
        → ⟨ pkh , ⟨  +[1+ n ] , ⟨ C1 , ⟨ r ,
        ⟨ ( (record s { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 s))) Data.Integer.-  +[1+ n ] )) (omap1 s)} )) , {!!} ⟩ ⟩ ⟩ ⟩ ⟩
      ;  ⟨ pkh , ⟨ r , ⟨ +[1+ n ] , ⟨ inj₂ y , +<+ m<n ⟩ ⟩ ⟩ ⟩ → {!!}}

-}


--  ⟨ pkh , ⟨ v , ⟨ C1 , ⟨ r , ⟨ {!!} , {! !} ⟩ ⟩ ⟩ ⟩ ⟩

{-
   prop3 {v = +_ zero} {curr = C1} = refl
   prop3 {v = +[1+ n ]} {curr = C1} = refl
   prop3 {v = -[1+_] n} {curr = C1} = refl
   prop3 {v = +_ zero} {curr = C2} = refl
   prop3 {v = +[1+ n ]} {curr = C2} = refl
   prop3 {v = -[1+_] n} {curr = C2} = refl
   prop3 {curr = Other} = {!!} -}



-- prop4 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (cancel st pkh v Other r) ≡ nothing
-- prop4 = refl

-- Map ℕ ℕ

-- m : k₁ ↦ v₁  ≤ m′ : k₁ ↦ v₁
--     k₂ ↦ v₂         k₂ ↦ v₂
--        ⋮               ⋮
--     k∞ ↦ v∞         k∞ ↦ v∞

-- m : Map Currency (Map ℚ ℕ)
-- c : Currency

-- ∀ c → c ≢ C₁ → c ∉ m


-- private variable X Y : Set


-- data Currency : Set where
--   C1    : Currency
--   C2    : Currency
--   Other : Currency


-- record Eqq (A : Set) : Set where
--   field
--     _===_ : A -> A -> Bool

-- open Eqq {{...}}

-- record Addable (A : Set) : Set where
--   field
--     _+++_ : A -> A -> A

-- open Addable {{...}}

-- record Ord (A : Set) : Set where
--   field
--     _<<_ : A → A → Bool
--     {{eqA}} : Eqq A

-- open Ord {{...}} hiding (eqA)

-- Map : Set -> Set -> Set
-- Map A B = A -> B

-- m : Map ℕ ℕ
-- m = λ x -> x


-- _<ᵐ_ : ∀ {A B : Set} {x : A} {{OrdB : Ord B}} -> Map A B -> Map A B -> Bool
-- _<ᵐ_ {x = x} m1 m2 = (m1 x) << (m2 x)

-- _==ᵐ_ : ∀ {A B : Set} {x : A} {{EqB : Eqq B}} -> Map A B -> Map A B -> Bool
-- _==ᵐ_ {x = x} m1 m2 = (m1 x) === (m2 x)

-- {-
-- _=?_ : {A : Set} -> (x : A) -> (b : A) -> Bool
-- x =? x = Bool.true
-- x =? y = Bool.false
-- -}



-- lookupm : {A B : Set} -> A -> Map A B -> B
-- lookupm a map = map a

-- insertm : {A B : Set} {{ EqA : Eqq A }} -> A -> B -> Map A B -> Map A B
-- insertm a b map = λ x -> if x === a then b else (map x)

-- _+ᵐ_ : {A B : Set} {{ AddB : Addable B }} -> Map A B -> Map A B -> Map A B
-- _+ᵐ_ m1 m2 = λ x -> (m1 x) +++ (m2 x)

-- {-
-- data _≤ᵐ_ : {A B : Set} -> Map A B -> Map A B -> Set₂ where
--   m≤m : ∀ {A B} {{ OrdB : Ord B }} (a : A) (m1 m2 : Map A B) -> (m1 a) << (m2 a) -> m1 ≤ᵐ m2


-- data _≤ᵐ_ : {A B : Set} {{ OrdB : Ord B }} -> Map A B -> Map A B -> Set where

--   m≤m : ∀ ( m1 m2 : (Map A B) )
--   -> m1 ≤ᵐ m2

-- -- Value : Map Currency ℕ
--  -- {a : A}
--   -- -> (m1 a) << (m2 a) -}

-- _==ℕ_ : ℕ → ℕ → Bool
-- zero  ==ℕ zero  = true
-- suc n ==ℕ suc m = n ==ℕ m
-- _     ==ℕ _     = false


-- _==ℤ_ : ℤ -> ℤ -> Bool
-- -[1+ m ] ==ℤ -[1+ n ] = n ==ℕ m
-- (+ m)    ==ℤ -[1+ n ] = Bool.false
-- -[1+ m ] ==ℤ (+ n)    = Bool.false
-- (+ m)    ==ℤ (+ n)    = m ==ℕ n



-- instance
--   Addℕ : Addable ℕ
--   _+++_ {{Addℕ}} = ( Data.Nat._+_ )

--   Addℤ : Addable ℤ
--   _+++_ {{Addℤ}} = ( Data.Integer._-_ )

--   AddMap : Addable (Map X ℤ)
--   _+++_ {{AddMap}} = ( _+ᵐ_ )

--   AddMap' : Addable (Map Y (Map X ℤ))
--   _+++_ {{AddMap'}} = ( _+ᵐ_ )

--   Eqℤ : Eqq ℤ
--   _===_ {{Eqℤ}} = ( _==ℤ_ )

--   Ordℤ : Ord ℤ
--   _<<_ {{Ordℤ}} = ( Data.Integer._≤ᵇ_ )

--   EqMap : Eqq (Map String ℤ)
--   _===_ {{EqMap}} = ( _==ᵐ_ )

--   OrdMap : Ord (Map String ℤ)
--   _<<_ {{OrdMap}} = ( _<ᵐ_ )


-- aux : ℚ -> ℚ -> Bool
-- aux a b =  Dec.does ( Data.Rational._≟_ a b )

-- instance
--   Eqℚ : Eqq ℚ
--   _===_ {{Eqℚ}} = aux





-- record Pair (A B : Set) : Set where
--   constructor _,_
--   field
--     fst : A
--     snd : B

-- open Pair
-- data Currency : Set where
--   C1    : Currency
--   C2    : Currency
--   Other : Currency
-- record State : Set where
--  -- constructor state{_,_,_,_,_}
--   field
--     curr1 : Currency
--     curr2 : Currency
--     omap1 : Map ℚ ( Map String ℤ ) - m′
--     omap2 : Map ℚ ( Map String ℤ )

-- open State

-- {-
-- test : ℚ -> ℚ -> Bool
-- test a b = Dec.does (a ≤? b)
-- -}

-- ALTERNATIVE: transition relation instead of (computable) functions
{-
data _↝_ : State → → State → Set where
  offer-C₁ : ∀ {v r pkh}
    → 0ℤ Data.Integer.<  v
    → 0ℚ Data.Rational.< r
      ----------------------------------------------------------------------------------
      s ↝⟨ "offer" ⟩ record s { omap1 = insertm r (λ x -> if x == pkh then v else 0ℤ) (s .omap1) }

  offer-C₂ :

    -------------
    s ↝⟨ "offer" ⟩ s′

offer s ... = s′
----------------
keys s ≤ keys s′

s ↝⟨ "offer" ⟩ s′
----------------
keys s ≤ keys s′

s ↝⟨ "request" ⟩ s′
----------------
⋯
-}

-- module _ (_<?_ : Dec _<_) (_≤?_ : Dec _≤_) where

--   offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
--   offer {_<?_} = ....

--   offer′ : {_<?_ : Dec _<_}
--   offer′ = ?

-- offer st pkh v cur r with cur
-- ... | C1 = if (Dec.does (0ℤ Data.Integer.<? v))
--   then if (Dec.does (0ℚ Data.Rational.<? r))
--     then just (record st { omap1 = (insertm r ( λ x -> if x == pkh then v else 0ℤ) (omap1 st)) } )
--     else nothing
--   else nothing
-- ... | C2 = if (Dec.does (0ℤ Data.Integer.<? v))
--   then if (Dec.does (0ℚ Data.Rational.<? r))
--     then just (record st { omap2 = (insertm r ( λ x -> if x == pkh then v else 0ℤ) (omap2 st)) } )
--     else nothing
--   else nothing
-- ... | Other = nothing

-- request : State -> Currency -> Map ℚ (Map String ℤ) -> Maybe State
-- request st cur smap with cur
-- ... | C1 = if smap <ᵐ (omap1 st)
--   then just (record st { omap1 = (omap1 st) +++ smap })
--   else nothing
-- ... | C2 = if smap <ᵐ (omap2 st)
--   then just (record st { omap2 = (omap2 st) +++ smap })
--   else nothing
-- ... | other = nothing


-- cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
-- cancel st pkh v cur r with cur
-- ... | C1 = if (Dec.does ( v Data.Integer.≤? (((omap1 st) r) pkh) ))
--   then just (record st { omap1 = (insertm r ( λ x -> if x == pkh then ( (((omap1 st) r) pkh) Data.Integer.- v) else 0ℤ) (omap1 st)) } )
--   else nothing
-- ... | C2 = if (Dec.does ( v Data.Integer.≤? (((omap2 st) r) pkh) ))
--   then just (record st { omap2 = (insertm r ( λ x -> if x == pkh then ( (((omap2 st) r) pkh) Data.Integer.- v) else 0ℤ) (omap2 st)) } )
--   else nothing
-- ... | Other = nothing



-- prop1 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (offer st pkh v Other r) ≡ nothing
-- prop1 = refl

-- prop2 : ∀ {st : State} {pkh : String} {curr : Currency} {r : ℚ} -> (offer st pkh -1ℤ curr r) ≡ nothing
-- prop2 {curr = C1} = refl
-- prop2 {curr = C2} = refl
-- prop2 {curr = Other} = refl


-- prop3 : ∀ {st : State} {pkh : String} {v : ℤ} {curr : Currency} -> (offer st pkh v curr -½ ) ≡ nothing
-- prop3 {v = +_ zero} {curr = C1} = refl
-- prop3 {v = +[1+ n ]} {curr = C1} = refl
-- prop3 {v = -[1+_] n} {curr = C1} = refl
-- prop3 {v = +_ zero} {curr = C2} = refl
-- prop3 {v = +[1+ n ]} {curr = C2} = refl
-- prop3 {v = -[1+_] n} {curr = C2} = refl
-- prop3 {curr = Other} = refl



-- prop4 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (cancel st pkh v Other r) ≡ nothing
-- prop4 = refl


-- {-
-- insert : (Pair ℚ String) -> ℤ -> List (Pair (Pair ℚ String) ℤ) -> List (Pair (Pair ℚ String) ℤ)
-- insert a b [] = (a , b) ∷ []
-- insert a b ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.<? (fst x) ))
--   then (a , b) ∷ ((x , y) ∷ xs)
--   else if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
--     then  if (Dec.does ( (snd a) Data.String.<? (snd x) ))
--       then (a , b) ∷ ((x , y) ∷ xs)
--       else if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
--         then (a , (b Data.Integer.+ y)) ∷ xs
--         else (x , y) ∷ (insert a b xs)
--     else (x , y) ∷ (insert a b xs)


-- reduce : (Pair ℚ String) -> ℤ -> List (Pair (Pair ℚ String) ℤ) -> List (Pair (Pair ℚ String) ℤ)
-- reduce a b [] = (a , b) ∷ []
-- reduce a b ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
--   then if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
--     then if (Dec.does ( b Data.Integer.≟ y ))
--       then xs
--       else (x , (y Data.Integer.- b)) ∷ xs
--     else (x , y) ∷ (reduce a b xs)
--   else (x , y) ∷ (reduce a b xs)


-- lookup' : (Pair ℚ String) -> List (Pair (Pair ℚ String) ℤ) -> ℤ
-- lookup' a [] = 0ℤ
-- lookup' a ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
--   then if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
--     then y
--     else lookup' a xs
--   else lookup' a xs

-- {-
-- (a , b) ∷ ((x , y) ∷ xs)
--   else if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
--     then  if (Dec.does ( (snd a) Data.String.<? (snd x) ))
--       then (a , b) ∷ ((x , y) ∷ xs)
--       else if
--         then (a , (b Data.Integer.+ y)) ∷ xs
--         else (x , y) ∷ (insert a b xs)
--     else (x , y) ∷ (insert a b xs)
-- -}


-- offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
-- offer st pkh v cur r with cur
-- ... | C1 = if (Dec.does (0ℤ Data.Integer.<? v))
--   then if (Dec.does (0ℚ Data.Rational.<? r))
--     then just (record st { omap1 = (insert (r , pkh) v (omap1 st)); tot1 = ((tot1 st) Data.Integer.+ v) } )
--     else nothing
--   else nothing
-- ... | C2 = if (Dec.does (0ℤ Data.Integer.<? v))
--   then if (Dec.does (0ℚ Data.Rational.<? r))
--     then just (record st { omap2 = (insert (r , pkh) v (omap2 st)); tot1 = ((tot1 st) Data.Integer.+ v) } )
--     else nothing
--   else nothing
-- ... | Other = nothing









-- {-
-- prop2 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (0ℚ Data.Rational.< r) ->  (0ℤ Data.Integer.< v) -> (is-just (offer st pkh v C1 r)) ≡ true --(insert (r , pkh) v (omap1 st))
-- prop2 (*<* x) (+<+ m<n) = {!!} -}





-- cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
-- cancel st pkh v cur r with cur
-- ... | C1 = if (Dec.does ( v Data.Integer.≤? (lookup' (r , pkh) (omap1 st)) ))
--   then just (record st { omap1 = (reduce (r , pkh) v (omap1 st)); tot1 = ((tot1 st) Data.Integer.- v) } )
--   else nothing
-- ... | C2 = if (Dec.does ( v Data.Integer.≤? (lookup' (r , pkh) (omap2 st)) ))
--   then just (record st { omap2 = (reduce (r , pkh) v (omap2 st)); tot2 = ((tot2 st) Data.Integer.- v) } )
--   else nothing
-- ... | Other = nothing

-- -}
