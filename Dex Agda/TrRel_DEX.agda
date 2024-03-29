module TrRel_DEX where

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
open import Data.Integer -- hiding (_≤_;)
open import Data.Rational -- hiding (_≤_;)
open import Data.String
open import Data.Maybe
open import Data.Sum.Base
open import Data.Product
open import Function.Base

{-
data Dec (A : Set) : Set where
  yes : A   → Dec A
  no  : ¬ A → Dec A
-}


private variable A B : Set

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

postulate
  -- Map ℕ ℤ
  Map : (A : Set) → (B : Set) → Set
  -- insertions
  insert : A -> B → Map A B → Map A B
  singleton : A -> B -> Map A B
  -- queries
  _∈_ : A → Map A B → Set
  _∈?_ : A → Map A B → Set
  query : (k : A) (m : Map A B) → B
  -- query : (k : A) (m : Map A B) {_ : k ∈ m} → B
  -- deletion
  _-ᵐ_ : Map A B → Map A B → Map A B
  _≤ᵐ_ : Map A B → Map A B → Set
  _≤?ᵐ_ : ∀ (m m′ : Map A B) → Dec (m ≤ᵐ m′)
  _~_ : (m : Map A B) (m′ : Map A B) {_ : m ≤ᵐ m′} → Map A B
  _only_ : Map A B -> A -> Set
  
  -- key equality


data Currency : Set where
  C1    : Currency
  C2    : Currency
  Other : Currency
-- variable c : Currency
  
record State : Set where
  field
    curr1 : Currency
    curr2 : Currency
    omap  : Map Currency ( Map String (Map ℚ ℤ) )
  --  omap2 : Map ℚ ( Map String ℤ )

open State

-- ∀ s -> ∃ s' -> s ↝ s' ∧ s' lessValue s

-- ∀ s -> s ↝ s' 
{-
data C1⊎C2 : Currency → Set where
  C1 : C1⊎C2 C1
  C2 : C1⊎C2 C2
-- variable cur : C1⊎C2 c

ofr : State -> String -> ℤ -> ℚ -> (c : Currency) ->  (C1⊎C2 c) -> State
ofr s pkh v r c' x = case x of λ where
        C1 -> record s { omap1 = (insert r (singleton pkh v) (omap1 s)) }
        C2 -> record s { omap2 = (insert r (singleton pkh v) (omap2 s)) }


can : State -> String -> ℤ -> ℚ 
-}

data _↝_ : State → State → Set where

  offer : ∀ {v r pkh s cur }
    → 0ℤ Data.Integer.<  v
    → 0ℚ Data.Rational.< r
    → ( cur ≡ C1 ⊎ cur ≡ C2 )
      ---------------------------------------------------------------------------
    → s ↝ record s { omap = (insert cur (singleton pkh (singleton r v)) (omap s)) }

-- s ↝ ofr s pkh v r c cur

-- record s { omap = (insert r (singleton pkh (singleton cur v)) (omap s)) }

  cancel : ∀ {s pkh v r cur}
    → v Data.Integer.≤ ( query r (query pkh (query cur (omap s))))
    ----------------------------------------------------------------
    → s ↝ record s { omap = insert cur (singleton pkh (singleton r ( (query r (query pkh (query cur (omap s)))) Data.Integer.- v ))) (omap s) }
       

  request : ∀ {s map cur }
    → map ≤ᵐ (omap s)
    → map only cur
    → ( cur ≡ C1 ⊎ cur ≡ C2 )
    -------------------------------------------
    → s ↝ record s { omap = (omap s) -ᵐ map }




-- record s { omap1 = (insert r (singleton pkh v) (omap1 s)) }

--  offer-C₂ : ∀ {v r pkh s}
--    → 0ℤ Data.Integer.<  v
--    → 0ℚ Data.Rational.< r
      ----------------------------------------------------------------------------------
--    → s ↝ record s { omap2 = (insert r (singleton pkh v) (omap2 s)) }


  
{-
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










{-
offer' : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer' st pkh v cur r with cur
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

request' : State -> Currency -> Map ℚ (Map String ℤ) -> Maybe State
request' st cur smap with cur
... | C1 = if (Dec.does (smap ≤?ᵐ (omap1 st)))
  then just (record st { omap1 = (omap1 st) -ᵐ smap })
  else nothing
... | C2 = if (Dec.does (smap ≤?ᵐ (omap2 st)))
  then just (record st { omap2 = (omap2 st) -ᵐ smap })
  else nothing
... | Other = nothing

-- ∀ s -> (∃ pkh z c r s' -> cancel s pkh c r = just s' ) ∨ (∃ c map s' -> reqest s c map = just s')

cancel' : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel' st pkh v cur r with cur
... | C1 = if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap1 st))) ))
  then just (record st { omap1 = insert r (singleton pkh ( (query pkh (query r (omap1 st))) Data.Integer.- v )) (omap1 st)} )
  else nothing
... | C2 = if (Dec.does ( v Data.Integer.≤? (query pkh (query r (omap2 st))) ))
  then just (record st { omap2 = insert r (singleton pkh ( (query pkh (query r (omap1 st))) Data.Integer.- v )) (omap2 st)} )
  else nothing
... | Other = nothing

{-
(Dec.does ( v Data.Integer.≤? (((omap2 st) r) pkh) ))
  then just (record st { omap2 = (insertm r ( λ x -> if x == pkh then ( (((omap2 st) r) pkh) Data.Integer.- v) else 0ℤ) (omap2 st)) } )
 
-}


prop1 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (offer' st pkh v Other r) ≡ nothing
prop1 = refl

prop2 : ∀ {st : State} {pkh : String} {curr : Currency} {r : ℚ} -> (offer' st pkh -1ℤ curr r) ≡ nothing
prop2 {curr = C1} = refl
prop2 {curr = C2} = refl
prop2 {curr = Other} = refl


prop3 : ∀ {st : State} {pkh : String} {v : ℤ} {curr : Currency} -> (offer' st pkh v curr -½ ) ≡ nothing
prop3 {v = +_ zero} {curr = C1} = refl
prop3 {v = +[1+ n ]} {curr = C1} = refl
prop3 {v = -[1+_] n} {curr = C1} = refl
prop3 {v = +_ zero} {curr = C2} = refl
prop3 {v = +[1+ n ]} {curr = C2} = refl
prop3 {v = -[1+_] n} {curr = C2} = refl
prop3 {v = +_ zero} {curr = Other} = refl
prop3 {v = +[1+ n ]} {curr = Other} = refl
prop3 {v = -[1+_] n} {curr = Other} = refl

prop4 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} -> (cancel' st pkh v Other r) ≡ nothing
prop4 = refl

-}

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
