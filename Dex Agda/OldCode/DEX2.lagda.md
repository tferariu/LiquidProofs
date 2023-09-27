

```agda
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
```



```agda

private variable X Y : Set


data Currency : Set where
  C1    : Currency
  C2    : Currency
  Other : Currency


record Eqq (A : Set) : Set where
  field
    _===_ : A -> A -> Bool

open Eqq {{...}}

record Addable (A : Set) : Set where
  field
    _+++_ : A -> A -> A

open Addable {{...}}

record Ord (A : Set) : Set where
  field
    _<<_ : A → A → Bool
    {{eqA}} : Eqq A

open Ord {{...}} hiding (eqA)

Map : Set -> Set -> Set
Map A B = A -> B

m : Map ℕ ℕ
m = λ x -> x

{-
_=?_ : {A : Set} -> (x : A) -> (b : A) -> Bool
x =? x = Bool.true
x =? y = Bool.false
-}



lookupm : {A B : Set} -> A -> Map A B -> B
lookupm a map = map a

insertm : {A B : Set} {{ EqA : Eqq A }} -> A -> B -> Map A B -> Map A B
insertm a b map = λ x -> if x === a then b else (map x)

_+ᵐ_ : {A B : Set} {{ AddB : Addable B }} -> Map A B -> Map A B -> Map A B
_+ᵐ_ m1 m2 = λ x -> (m1 x) +++ (m2 x)

data _≤ᵐ_ : {A B : Set} {{ OrdB : Ord B }} -> Map A B -> Map A B -> Set where
  jij : ∀ {a b ord} (m1 m2 : Map a b) -> m1 ≤ᵐ m2

{-
data _≤ᵐ_ : {A B : Set} {{ OrdB : Ord B }} -> Map A B -> Map A B -> Set where

  m≤m : ∀ ( m1 m2 : (Map A B) )  
  -> m1 ≤ᵐ m2

-- Value : Map Currency ℕ
 -- {a : A}
  -- -> (m1 a) << (m2 a) -}


instance
  Addℕ : Addable ℕ
  _+++_ {{Addℕ}} = ( Data.Nat._+_ )

  AddMap : Addable (Map X ℕ)
  _+++_ {{AddMap}} = ( _+ᵐ_ )

  AddMap' : Addable (Map Y (Map X ℕ))
  _+++_ {{AddMap'}} = ( _+ᵐ_ )
 
{-
instance
  Eqℚ : Eqq ℚ
  _===_ {{Eqℚ}} = ( Data.Rational._≟_ )

-}



record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

record State : Set where
 -- constructor state{_,_,_,_,_}
  field
    curr1 : Currency
    curr2 : Currency
    omap1 : List (Pair (Pair ℚ String) ℤ)
    omap2 : List (Pair (Pair ℚ String) ℤ)
    tot1  : ℤ
    tot2  : ℤ

open State

{-
test : ℚ -> ℚ -> Bool
test a b = Dec.does (a ≤? b)
-}
  



insert : (Pair ℚ String) -> ℤ -> List (Pair (Pair ℚ String) ℤ) -> List (Pair (Pair ℚ String) ℤ)
insert a b [] = (a , b) ∷ []
insert a b ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.<? (fst x) ))
  then (a , b) ∷ ((x , y) ∷ xs)
  else if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
    then  if (Dec.does ( (snd a) Data.String.<? (snd x) ))
      then (a , b) ∷ ((x , y) ∷ xs)
      else if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
        then (a , (b Data.Integer.+ y)) ∷ xs 
        else (x , y) ∷ (insert a b xs)
    else (x , y) ∷ (insert a b xs)


reduce : (Pair ℚ String) -> ℤ -> List (Pair (Pair ℚ String) ℤ) -> List (Pair (Pair ℚ String) ℤ)
reduce a b [] = (a , b) ∷ []
reduce a b ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
  then if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
    then if (Dec.does ( b Data.Integer.≟ y ))
      then xs
      else (x , (y Data.Integer.- b)) ∷ xs
    else (x , y) ∷ (reduce a b xs)
  else (x , y) ∷ (reduce a b xs)


lookup' : (Pair ℚ String) -> List (Pair (Pair ℚ String) ℤ) -> ℤ
lookup' a [] = 0ℤ
lookup' a ((x , y) ∷ xs) = if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
  then if (Dec.does ( (snd a) Data.String.≟ (snd x) ))
    then y
    else lookup' a xs
  else lookup' a xs

{-
(a , b) ∷ ((x , y) ∷ xs)
  else if (Dec.does ( (fst a) Data.Rational.≟ (fst x) ))
    then  if (Dec.does ( (snd a) Data.String.<? (snd x) ))
      then (a , b) ∷ ((x , y) ∷ xs)
      else if 
        then (a , (b Data.Integer.+ y)) ∷ xs 
        else (x , y) ∷ (insert a b xs)
    else (x , y) ∷ (insert a b xs)
-}


offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer st pkh v cur r with cur
... | C1 = if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap1 = (insert (r , pkh) v (omap1 st)); tot1 = ((tot1 st) Data.Integer.+ v) } )
    else nothing
  else nothing
... | C2 = if (Dec.does (0ℤ Data.Integer.<? v))
  then if (Dec.does (0ℚ Data.Rational.<? r))
    then just (record st { omap2 = (insert (r , pkh) v (omap2 st)); tot1 = ((tot1 st) Data.Integer.+ v) } )
    else nothing
  else nothing
... | Other = nothing




prop1 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (offer st pkh v Other r) ≡ nothing
prop1 = refl

prop2 : ∀ {st : State} {pkh : String} {curr : Currency} {r : ℚ} -> (offer st pkh -1ℤ curr r) ≡ nothing
prop2 {curr = C1} = refl
prop2 {curr = C2} = refl
prop2 {curr = Other} = refl


prop3 : ∀ {st : State} {pkh : String} {v : ℤ} {curr : Currency} -> (offer st pkh v curr -½ ) ≡ nothing
prop3 {v = +_ zero} {curr = C1} = refl
prop3 {v = +[1+ n ]} {curr = C1} = refl
prop3 {v = -[1+_] n} {curr = C1} = refl
prop3 {v = +_ zero} {curr = C2} = refl
prop3 {v = +[1+ n ]} {curr = C2} = refl
prop3 {v = -[1+_] n} {curr = C2} = refl
prop3 {curr = Other} = refl

{-
prop2 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (0ℚ Data.Rational.< r) ->  (0ℤ Data.Integer.< v) -> (is-just (offer st pkh v C1 r)) ≡ true --(insert (r , pkh) v (omap1 st))
prop2 (*<* x) (+<+ m<n) = {!!} -}





cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel st pkh v cur r with cur
... | C1 = if (Dec.does ( v Data.Integer.≤? (lookup' (r , pkh) (omap1 st)) ))
  then just (record st { omap1 = (reduce (r , pkh) v (omap1 st)); tot1 = ((tot1 st) Data.Integer.- v) } )
  else nothing
... | C2 = if (Dec.does ( v Data.Integer.≤? (lookup' (r , pkh) (omap2 st)) ))
  then just (record st { omap2 = (reduce (r , pkh) v (omap2 st)); tot2 = ((tot2 st) Data.Integer.- v) } )
  else nothing
... | Other = nothing








```
