open import Validators.MultiSig renaming (now to now')
open import Lib
open import Value


open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
import Data.Nat.Properties as N
--open import Data.Integer 
--open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

open import Haskell.Prim hiding (⊥ ; Any ; All) 
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup)


open import ProofLib

module Proofs.MultiSigProofs where


record State : Set where
  field
    datum      : Label
    value      : Value  
    outVal     : Value
    now        : Nat
    tsig       : PubKeyHash
    continues  : Bool
    spends     : TxOutRef
    hasToken   : Bool
    mint       : Integer
    token      : AssetClass
open State


_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)


--Transition Rules

record MParams : Set where
    field
        address   : Address
        outputRef : TxOutRef
        tokName   : TokenName
        authSigs  : List PubKeyHash
        nr        : Nat
        maxWait   : Nat
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s tok}
    -> datum s ≡ ( tok , Holding )
    -> (lovelaces 2xMinValue < lovelaces (value s)) ≡ true
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> token s ≡ tok
    -> token s .snd ≡ tokName par
    -> hasToken s ≡ true
    -------------------
    -> par ⊢ s


data _⊢_~[_]~>_ : MParams -> State -> Input -> State -> Set where
 
  TPropose : ∀ {v tok pkh d s s' par} 
    -> geq (value s) v ≡ true
    -> (lovelaces v >= lovelaces minValue) ≡ true
    -> datum s ≡ (tok , Holding)
    -> datum s' ≡ (tok , Collecting v pkh d [])
    -> value s ≡ value s'
    -> d N.≤ (now s') N.+ (maxWait par) 
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'

  TAdd : ∀ {sig par s s' v tok pkh d sigs} 
    -> sig ∈ (authSigs par)
    -> tsig s' ≡ sig
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Collecting v pkh d (insert sig sigs))
    -> value s ≡ value s'
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'

  TPay : ∀ {v pkh tok d sigs s s' par} 
    -> value s ≡ addValue (value s') v
    -> length sigs N.≥ nr par
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Holding)
    -> outVal s' ≡ v
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par v pkh d sigs tok} 
    -> now s' N.> d
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Holding)
    -> value s ≡ value s' 
    -> continues s ≡ true
    -> continues s' ≡ true 
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'


data _⊢_~[_]~|_ : MParams -> State -> Input -> State -> Set where

  TClose : ∀ {par s s' tok}
    -> datum s ≡ ( tok , Holding )
    -> (lovelaces 2xMinValue > lovelaces (value s)) ≡ true
    -> continues s ≡ true
    -> continues s' ≡ false
    -> hasToken s ≡ true
    -> hasToken s' ≡ false
    -> mint s' ≡ -1
    -------------------
    -> par ⊢ s ~[ Close ]~| s'

data Unique {a : Set} : List a → Set where
  root : Unique []
  _::_ : {x : a} {l : List a} -> x ∉ l -> Unique l -> Unique (x ∷ l)


--Valid State
data ValidS : State -> Set where

  Hol : ∀ {s tok}
    -> datum s ≡ (tok , Holding) 
    -> continues s ≡ true
    -> hasToken s ≡ true
    ----------------
    -> ValidS s

  Col : ∀ {s v pkh d sigs tok}
    -> datum s ≡ ( tok , Collecting v pkh d sigs )
    -> geq (value s) v ≡ true
    -> (lovelaces v >= lovelaces minValue) ≡ true
    -> Unique sigs   
    -> continues s ≡ true
    -> hasToken s ≡ true
    --------------------------------
    -> ValidS s

--Multi-Step Transition
data _⊢_~[_]~*_ : MParams -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''

  fin : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~| s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


--State Validity sub-lemmas
diffLabels : ∀ {v pkh d sigs tok1 tok2} (dat : Label) -> dat ≡ (tok1 , Holding)
           -> dat ≡ (tok2 , Collecting v pkh d sigs) -> ⊥ 
diffLabels (tok , Holding) p1 ()
diffLabels (tok , (Collecting v pkh d sigs)) () p2

sameValue : ∀ {v v' pkh pkh' d d' sigs sigs' } {tok tok' : AssetClass}
  -> (tok , Collecting v pkh d sigs) ≡ (tok' , Collecting v' pkh' d' sigs') -> v ≡ v'
sameValue refl = refl

sameSigs : ∀ {v v' pkh pkh' d d' sigs sigs'} {tok tok' : AssetClass}
  -> (tok , Collecting v pkh d sigs) ≡ (tok' , Collecting v' pkh' d' sigs')  -> sigs ≡ sigs'
sameSigs refl = refl


reduce∈ : ∀ {A : Set} {x y : A} {xs} -> y ∈ (x ∷ xs) -> y ≢ x -> y ∈ xs
reduce∈ (here px) p2 = ⊥-elim (p2 px)
reduce∈ (there p1) p2 = p1 


insertPreserves∈ : ∀ {x y zs}
  -> x ∈ insert y zs -> (y == x) ≡ false -> x ∈ zs
insertPreserves∈ {x} {y} {zs = []} (here px) p2 rewrite px = ⊥-elim (n≠n y p2)
insertPreserves∈ {x} {y} {z ∷ zs} p1 p2 with y == x in eq1
...| true =  ⊥-elim (get⊥ p2)
...| false with y == z in eq2
...| true = p1 
...| false with x == z in eq3
...| true rewrite ==to≡ x z eq3 = here refl 
...| false = there (insertPreserves∈ (reduce∈ p1 (λ {refl → n≠n z eq3})) eq1)


insertPreservesUniqueness : ∀ {sig sigs}
  -> Unique sigs -> Unique (insert sig sigs)
insertPreservesUniqueness root = (λ ()) :: root
insertPreservesUniqueness {sig} {(x ∷ xs)} (p :: ps) with sig == x in eq
...| false = (λ z → p (insertPreserves∈ z eq)) :: (insertPreservesUniqueness ps)
...| true = p :: ps


--State Validity Invariant
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> ValidS s
validStateInitial (TStart p1 p' p2 p3 p4 p5 p6 p7) = Hol p1 p3 p7

validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition iv (TPropose p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 = Col p4 p1 p2 root p8 p10
validStateTransition {s} (Hol pf pf' pf'') (TAdd p1 p2 p3 p4 p5 p6 p7 p8 p9) = ⊥-elim (diffLabels (datum s) pf p3)
validStateTransition (Col pf1 pf2 pf3 pf4 pf5 pf6) (TAdd p1 p2 p3 p4 p5 p6 p7 p8 p9) 
                     rewrite pf1 | sameValue p3 | p5 | sameSigs p3
                     = Col p4 pf2 pf3 (insertPreservesUniqueness pf4) p7 p9
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6 p7 p8 p9 ) = Hol p4 p7 p9 
validStateTransition iv (TCancel p1 p2 p3 p4 p5 p6 p7 p8) = Hol p3 p6 p8

{-deprecated
validStateFinal : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~| s'
  -> ValidS s'
validStateFinal iv (TClose p1 p2 p3 p4 p5 p6 p7) = Stp p4 p6

validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x
validStateMulti iv (fin pf x) = validStateMulti (validStateFinal iv pf) x
-}


--Prop1 sub-lemmas and helper functions
makeIs : List PubKeyHash -> List Input
makeIs [] = []
makeIs (x ∷ pkhs) = Add x ∷ makeIs pkhs

insertList : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
insertList [] sigs = sigs
insertList (x ∷ asigs) sigs = insertList asigs (insert x sigs)

appendLemma : ∀ (x : PubKeyHash) (a b : List PubKeyHash) -> a ++ x ∷ b ≡ (a ++ x ∷ []) ++ b
appendLemma x [] b = refl
appendLemma x (a ∷ as) b = cong (λ y → a ∷ y) (appendLemma x as b) 

∈lemma : ∀ (xs ys : List PubKeyHash) (z : PubKeyHash) -> z ∈ (xs ++ z ∷ ys)
∈lemma [] ys z = here refl
∈lemma (x ∷ xs) ys z = there (∈lemma xs ys z)

finalSig : ∀ (s : State) -> (ls : List Input) -> PubKeyHash
finalSig s [] = tsig s
finalSig s (Propose x x₁ x₂ ∷ [])  = tsig s
finalSig s (Add sig ∷ []) = sig
finalSig s (Pay ∷ []) = tsig s
finalSig s (Cancel ∷ []) = tsig s
finalSig s (i ∷ ls) = finalSig s ls

finalSigLemma : ∀ (s s' : State) (x : PubKeyHash) (xs : List PubKeyHash)
  -> tsig s' ≡ x -> finalSig s (makeIs (x ∷ xs)) ≡ finalSig s' (makeIs xs)
finalSigLemma s1 s2 x [] pf = sym pf
finalSigLemma s1 s2 x (y ∷ []) pf = refl
finalSigLemma s1 s2 x (y ∷ z ∷ xs) pf = finalSigLemma s1 s2 x (z ∷ xs) pf

--Generalized Prop1 (Can add signatures 1 by 1)
prop : ∀ {v pkh d sigs tok} (s s' : State) (par : MParams) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par)
         -> asigs ≡ (asigs' ++ asigs'')
         -> datum s ≡ (tok , Collecting v pkh d sigs)
         -> datum s' ≡ (tok , Collecting v pkh d (insertList asigs'' sigs))
         -> outVal s ≡ outVal s' {- not quite right -}
         -> now s ≡ now s'
         -> value s ≡ value s'
         -> spends s ≡ spends s'
         -> mint s ≡ mint s'
         -> token s ≡ token s'
         -> tsig s' ≡ finalSig s (makeIs asigs'')
         -> continues s ≡ true
         -> continues s' ≡ true
         -> hasToken s ≡ true
         -> hasToken s' ≡ true
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop {v} {pkh} {d} {sigs} {tok} record { datum = .(tok , Collecting v pkh d sigs) ; value = value ; outVal = outVal ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token } record { datum = .(_ , Collecting v pkh d (insertList [] sigs)) ; value = .(value) ; outVal = .(outVal) ; now = .(now) ; tsig = .(finalSig (record { datum = tok , Collecting v pkh d sigs ; value = value ; outVal = outVal  ; now = now ; tsig = tsig ; continues = true ; spends = spends ; hasToken = true ; mint = mint ; token = token }) (makeIs [])) ; continues = .true ; spends = .(spends) ; hasToken = .true ; mint = .(mint) ; token = .(token) } record { authSigs = .(asigs1 ++ []) ; nr = nr₁ ; maxWait = maxWait₁ } .(asigs1 ++ []) asigs1 [] refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl = root

prop {v} {pkh} {d} {sigs} {tok}
  s1@record { datum = .(tok , Collecting v pkh d sigs) ; value = value ; outVal = outVal ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token }
  s2@record { datum = .(tok , Collecting v pkh d (insertList (x ∷ asigs2) sigs)) ; value = .(value) ; outVal = .(outVal) ; now = .(now) ; tsig = .(finalSig (record { datum = _ , Collecting v pkh d sigs ; value = value ; outVal = outVal ; now = now ; tsig = tsig ; continues = true ; spends = spends ; hasToken = true ; mint = mint ; token = token }) (makeIs (x ∷ asigs2))) ; continues = .true ; spends = .(spends) ; hasToken = .true ; mint = .(mint) ; token = .(token) }
  par@record { authSigs = .(asigs1 ++ x ∷ asigs2) ; nr = nr₁ ; maxWait = maxWait₁ } .(asigs1 ++ x ∷ asigs2) asigs1 (x ∷ asigs2) refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
  = cons (TAdd (∈lemma asigs1 asigs2 x) refl refl refl refl refl refl refl refl)
    (prop s' s2 par (asigs1 ++ x ∷ asigs2) (asigs1 ++ [ x ]) asigs2 refl (appendLemma x asigs1 asigs2) refl refl refl refl refl refl refl refl  (finalSigLemma s1 s' x asigs2 refl) refl refl refl refl)
    where
      s' = record
            { datum = tok , Collecting v pkh d (insert x sigs)
            ; value = value
            ; outVal = outVal
            ; now = now
            ; tsig = x
            ; continues = true
            ; spends = spends
            ; hasToken = true
            ; mint = mint
            ; token = token
            }



--Actual Prop1 (Can add all signatures 1 by 1)
prop1 : ∀ { v pkh d sigs tok } (s s' : State) (par : MParams)
        -> datum s ≡ (tok , Collecting v pkh d sigs)
        -> datum s' ≡ (tok , Collecting v pkh d (insertList (authSigs par) sigs))
        -> outVal s ≡ outVal s'
        -> now s ≡ now s'
        -> value s ≡ value s'
        -> spends s ≡ spends s'
        -> mint s ≡ mint s'
        -> token s ≡ token s'
        -> tsig s' ≡ finalSig s (makeIs (authSigs par))
        -> continues s ≡ true
        -> continues s' ≡ true
        -> hasToken s ≡ true
        -> hasToken s' ≡ true
        -> par ⊢ s ~[ (makeIs (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13  = prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13  


--UniqueInsertLemma sub-lemmas


_⊆_ : List a -> List a -> Set
l1 ⊆ l2 = All (_∈ l2) l1

⊆-cons : (x : a){l1 l2 : List a} -> l1 ⊆ l2 -> l1 ⊆ (x ∷ l2)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : (l : List a) -> l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷ ⊆-cons x (⊆-refl l)

⊆-trans : {l1 l2 l3 : List a} -> l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3
⊆-trans [] p2 = []
⊆-trans (px ∷ p1) p2 = All.lookup p2 px ∷ ⊆-trans  p1 p2


insert-lem1 : (x : PubKeyHash)(l : List PubKeyHash) -> x ∈ insert x l
insert-lem1 x [] = here refl
insert-lem1 x (y ∷ l) with x == y in eq
... | false = there (insert-lem1 x l) 
... | true rewrite ==to≡ x y eq = here refl

insert-lem2 : (x y : PubKeyHash)(l : List PubKeyHash) -> x ∈ l -> x ∈ insert y l
insert-lem2 x y [] pf = there pf
insert-lem2 x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite px = here refl
insert-lem2 x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem2 x y l pf) 
...| true = there pf

del : ∀{x} (l : List a) -> x ∈ l -> List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) -> N.suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong N.suc (length-del p) 

∈-del : ∀{x y}{l : List a} (p : x ∈ l) -> x ≢ y -> y ∈ l -> y ∈ del l p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l1 l2 : List a} (p : x ∈ l2) -> (x ∉ l1) -> l1 ⊆ l2 -> l1 ⊆ del l2 p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e -> n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {l1 l2 : List a} -> l1 ⊆ l2 -> Unique l1 -> length l2 N.≥ length l1
unique-lem [] root = N.z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = N.s≤s (unique-lem (subset-del px x sub) un)

insertList-sublem : (l1 l2 : List PubKeyHash) (x : PubKeyHash) -> x ∈ l2 -> x ∈ insertList l1 l2
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l1) l2 x pf = insertList-sublem l1 (insert y l2) x (insert-lem2 x y l2 pf)


insertList-lem : (l1 l2 : List PubKeyHash) -> l1 ⊆ insertList l1 l2
insertList-lem [] l = []
insertList-lem (x ∷ l1) l2 = insertList-sublem l1 (insert x l2) x (insert-lem1 x l2) ∷ insertList-lem l1 (insert x l2)

--Unique Insert Lemma
uil : ∀ (l1 l2 : List PubKeyHash) (pf : Unique l1) -> (length (insertList l1 l2) N.≥ length l1)
uil l1 l2 pf = unique-lem (insertList-lem l1 l2) pf

--Valid Parameters
ValidP : MParams -> Set 
ValidP par = Unique (authSigs par) × length (authSigs par) N.≥ nr par
  
--Multi-Step lemma
lemmaMultiStep : ∀ (par : MParams) (s s' s'' : State) (is is' : List Input)
                   -> par ⊢ s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep par s .s s'' [] is' root p2 = p2
lemmaMultiStep par s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)
lemmaMultiStep par s s' s'' (x ∷ is) is' (fin {s' = s'''} p1 p2) p3 = fin p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)

--Prop2 (Can add signatures 1 by 1 and then pay)
prop2 : ∀ { v pkh d sigs tok } (s s' : State) (par : MParams)
          -> ValidS s
          -> datum s ≡ (tok , Collecting v pkh d sigs)
          -> datum s' ≡ (tok , Holding)
          -> outVal s' ≡ v
          -> value s ≡ addValue (value s') v
          -> ValidP par
          -> continues s ≡ true
          -> continues s' ≡ true
          -> hasToken s ≡ true
          -> hasToken s' ≡ true
          -> tsig s' ≡ pkh
          -> par ⊢ s ~[ ((makeIs (authSigs par)) ++ [ Pay ]) ]~* s'


prop2 {d = d} {sigs = sigs} {tok = tok}
  s1@record { datum = .(tok , Collecting outVal sig d sigs) ; value = .(addValue value outVal) ; outVal = oV ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token }
  s2@record { datum = .(tok , Holding) ; value = value ; outVal = outVal ; now = n ; tsig = sig ; continues = .true ; spends = spn ; hasToken = .true ; mint = m ; token = tok' } par (Col p1 p2 p3 p4 p7 p8) refl refl refl refl (p5 , p6) refl refl refl refl refl
  = lemmaMultiStep par s1 s' s2 (makeIs (authSigs par)) [ Pay ]
    (prop1 s1 s' par refl refl refl refl refl refl refl refl refl refl refl refl refl)
    (cons (TPay refl (N.≤-trans p6 (uil (authSigs par) sigs p5)) refl refl refl refl refl refl refl) root)
  where
    s' = record
          { datum = tok , (Collecting outVal sig d (insertList (authSigs par) sigs)) 
          ; value = addValue value outVal
          ; outVal = oV
          ; now = now
          ; tsig = finalSig (record { datum = tok , Collecting outVal sig d sigs
                                    ; value = addValue value outVal
                                    ; outVal = oV
                                    ; now = now
                                    ; tsig = tsig
                                    ; continues = true
                                    ; spends = spends
                                    ; hasToken = true
                                    ; mint = mint
                                    ; token = token })  (makeIs (authSigs par))
          ; continues = true
          ; spends = spends
          ; hasToken = true
          ; mint = mint
          ; token = token
          }
                                                                             


takeLength : ∀ {a : Nat} {l : List PubKeyHash} -> length l N.≥ a -> a N.≤ length (take a l)
takeLength {zero} {[]} p = p
takeLength {zero} {x ∷ l} p = N.z≤n
takeLength {N.suc a} {x ∷ l} (N.s≤s p)= N.s≤s (takeLength p)

∈take : ∀ {y : PubKeyHash} {a : Nat} {l : List PubKeyHash} -> y ∈ take a l -> y ∈ l
∈take {y} {suc a} {x ∷ l} (here px) = here px
∈take {y} {suc a} {x ∷ l} (there p) = there (∈take p)

∉take : ∀ {y : PubKeyHash} {a : Nat} {l : List PubKeyHash} -> y ∉ l -> y ∉ take a l
∉take {y} {zero} {[]} p = p
∉take {y} {zero} {x ∷ l} p = λ ()
∉take {y} {suc a} {[]} p = p
∉take {y} {suc a} {x ∷ l} p = λ { (here px) → p (here px) ; (there z) → p (there (∈take z))}

takeUnique : ∀ {a : Nat} {l : List PubKeyHash} -> Unique l -> Unique (take a l)
takeUnique {zero} {[]} p = p
takeUnique {zero} {x ∷ l} p = root
takeUnique {suc a} {[]} p = p
takeUnique {suc a} {x ∷ l} (p :: ps) = ∉take p :: (takeUnique ps)




--Weak Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
liquidity : ∀ (par : MParams) (s : State) (pkh : PubKeyHash) 
          -> ValidS s -> ValidP par
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ emptyValue) )
          
liquidity par
  s@record { datum = (tok , Holding) ; value = value ; outVal = outVal ; now = now ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } pkh (Hol refl p p') (p2 , p3) with (lovelaces 2xMinValue > lovelaces value) in eq
...| true = ⟨ s' , ⟨ [ Close ] , ((fin (TClose refl eq p refl p' refl refl) root) , refl) ⟩ ⟩  --(ltToGt (value) (2xMinValue) (notGeqToLt (value) (2xMinValue) eq))
     where
       s' : State
       s' = record
             { datum = tok , Holding
             ; value = emptyValue
             ; outVal = value
             ; now = now
             ; tsig = tsig
             ; continues = false
             ; spends = spends
             ; hasToken = false
             ; mint = -1
             ; token = tok } 
...| false  = ⟨ s'' , ⟨ ((Propose value pkh 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ])) ,
             (cons (TPropose (geq-refl value)
             (geqIntegerTrans (lovelaces value) (pos 6) (pos 3) (ltIntFalseToGeq (lovelaces value) (pos 6) eq) refl)
             refl refl refl N.z≤n p refl p' refl) 
             (prop2 s' s'' par (Col refl (geq-refl value)
             (geqIntegerTrans (lovelaces value) (pos 6) (pos 3) (ltIntFalseToGeq (lovelaces value) (pos 6) eq) refl)
             root refl refl) refl refl refl (sym (addValIdL value)) (p2 , p3) refl refl refl refl refl) , refl) ⟩ ⟩ 
     where
       s'' = record
              { datum = tok , Holding
              ; value = emptyValue
              ; outVal = value
              ; now = now
              ; tsig = pkh
              ; continues = true
              ; spends = spends
              ; hasToken = true
              ; mint = mint
              ; token = token
              }
       s' = record
             { datum = tok , (Collecting value pkh 0 [])
             ; value = value
             ; outVal = outVal
             ; now = now
             ; tsig = tsig
             ; continues = true
             ; spends = spends
             ; hasToken = true
             ; mint = mint
             ; token = token
             }
liquidity par s@record { datum = (tok , Collecting v' pkh' d' sigs') ; value = value ; outVal = outVal ; now = now ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } pkh (Col refl p2 p3 p4 p5 p6) (p7 , p8) with (lovelaces value >= lovelaces minValue) in eq
...| false rewrite geqIntegerTrans (lovelaces value) (lovelaces v') (pos 3) (lovelaceLemma value v' p2) p3 = ⊥-elim (get⊥ eq) 
...| true  = ⟨ s''' , ⟨ (Cancel ∷ (Propose value pkh 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ])) ,
             ((cons (TCancel  {s' = s'} (N.s≤s N.≤-refl) refl refl refl p5 refl p6 refl) 
             (cons (TPropose (geq-refl value) eq refl refl refl N.z≤n refl refl refl refl) 
             (prop2 s'' s''' par (Col refl (geq-refl value) eq root refl refl) refl refl refl (sym (addValIdL value)) (p7 , p8) refl refl refl refl refl))) , refl) ⟩ ⟩
     where
       s''' = record
              { datum = tok , Holding
              ; value = emptyValue
              ; outVal = value
              ; now = N.suc (N.suc (N.suc d'))
              ; tsig = pkh
              ; continues = true
              ; spends = spends
              ; hasToken = true
              ; mint = mint
              ; token = token
              }
       s'' = record
             { datum = tok , (Collecting value pkh 0 [])
             ; value = value
             ; outVal = outVal
             ; now = N.suc (N.suc d')
             ; tsig = tsig
             ; continues = true
             ; spends = spends
             ; hasToken = true
             ; mint = mint
             ; token = token
             }
       s' = record
              { datum = tok , Holding
              ; value = value
              ; outVal = outVal
              ; now = N.suc d'
              ; tsig = tsig
              ; continues = true
              ; spends = spends
              ; hasToken = true
              ; mint = mint
              ; token = token
              }






--sub-lemmas and helper functions for validator returning true implies transition


l=l : ∀ (l : List Nat) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite n=n x = l=l l

queryTo∈ : ∀ {sig sigs} -> (query sig sigs) ≡ true -> sig ∈ sigs
queryTo∈ {sig} {x ∷ sigs} pf with orToSum (x == sig) (query sig sigs) pf
... | inj₁ a = here (sym (==to≡ x sig a))
... | inj₂ b = there (queryTo∈ b)


lengthNatToLength : ∀ (n : Nat) (l : List PubKeyHash) -> (n N.<ᵇ lengthNat l || lengthNat l N.≡ᵇ n) ≡ true -> n N.≤ length l
lengthNatToLength zero [] pf = N.z≤n
lengthNatToLength zero (x ∷ l) pf = N.z≤n
lengthNatToLength (suc n) (x ∷ l) pf = N.s≤s (lengthNatToLength n l pf)



getS : Label -> ScriptContext -> State
getS (tok , lab) ctx = record
              { datum = (tok , lab)
              ; value = oldValue ctx
              ; outVal = 0
              ; now = 0
              ; tsig = 0
              ; continues = true
              ; spends = 0
              ; hasToken = checkTokenIn tok ctx
              ; mint = 0
              ; token = (0 , 0)
              }


getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
                { datum = newDatum ctx
                ; value = newValue ctx
                ; outVal = 0
                ; now = now' ctx
                ; tsig = sig ctx
                ; continues = continuing ctx
                ; spends = iRef ctx
                ; hasToken = checkTokenOut (ownAssetClass tn ctx) ctx
                ; mint = getMintedAmount ctx
                ; token = ownAssetClass tn ctx
                }



getS' : Label -> ScriptContext -> State
getS' (tok , Holding) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = 0
             ; now = now' ctx
             ; tsig = sig ctx
             ; continues = continuing ctx
             ; spends = iRef ctx
             ; hasToken = checkTokenOut tok ctx
             ; mint = getMintedAmount ctx
             ; token = (0 , 0)
             }
getS' (tok , Collecting v pkh d sigs) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = getPayment pkh ctx
             ; now = now' ctx
             ; tsig = sig ctx
             ; continues = continuing ctx
             ; spends = iRef ctx
             ; hasToken = checkTokenOut tok ctx
             ; mint = getMintedAmount ctx
             ; token = (0 , 0)
             }


getPar : Params -> Address -> TxOutRef -> TokenName -> MParams
getPar p adr oref tn = record
                     { address = adr
                     ; outputRef = oref
                     ; tokName = tn
                     ; authSigs = authSigs p
                     ; nr = nr p
                     ; maxWait = maxWait p
                     }


--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {adr oref tn} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Close
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> getPar par adr oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx

validatorImpliesTransition par (tok , Holding) Close ctx nc pf = ⊥-elim (nc refl)
--validatorImpliesTransition par (tok , Collecting v pkh d sigs) Close ctx nc pf = ⊥-elim (nc refl)
validatorImpliesTransition par (tok , Holding) (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint } nc pf
  = ⊥-elim (&&5false (eqValue outputVal inputVal) (geq inputVal v) (lovelaces v >= lovelaces minValue) (ltNat d (addNat time (maxWait par)) || eqNat (addNat time (maxWait par)) d) continues  pf)
validatorImpliesTransition par (tok , Holding) (Propose v pkh d) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint } nc pf
  rewrite sym (==vto≡ v v' (get (go continues (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))))))) | --(ltInteger v inputVal || eqInteger inputVal v)
  sym (==to≡ pkh pkh' (get (go (eqValue v v') (go continues (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf)))))))) |
  sym (==to≡ d d' (get (go (pkh == pkh') (go (eqValue v v') (go continues (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))))))))) |
  (==lto≡ sigs' [] (get (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go continues (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf)))))))))) |
  (==tto≡ tok tok' (go (sigs' == []) (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go continues (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))))))))))
  = TPropose (get (go (eqValue outputVal inputVal) pf))
     (get (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))) refl 
     refl (sym (==vto≡ outputVal inputVal (get pf))) 
     (≤ᵇNto≤N' (get (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))))) refl 
     (get (go (notTooLate par d ctx) (go (lovelaces v >= lovelaces minValue) (go (geq inputVal v) (go (eqValue outputVal inputVal) pf))))) refl refl 
validatorImpliesTransition par (tok , Holding) (Add x) record { tokenIn = tokenIn ; tokenOut = false } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Holding) (Add x) record { tokenIn = tokenIn ; tokenOut = true  } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) (Add x) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint  } nc pf
  = ⊥-elim (&&4false (eqValue outputVal inputVal) (eqNat x signature) (query x (authSigs par)) continues pf)
validatorImpliesTransition par (tok , Holding) Pay record { tokenIn = tokenIn ; tokenOut = false } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Holding) Pay record { tokenIn = tokenIn ; tokenOut = true  } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Pay ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint  } nc pf
  rewrite 
  ==tto≡ tok tok' (go (inputVal == (addValue outputVal v)) (go (checkPayment pkh v ctx) (go continues (go ((lengthNat sigs) >= (nr par)) pf))))
  = TPay (==vto≡ inputVal (addValue outputVal v) (get (go (checkPayment pkh v ctx) (go continues (go ((lengthNat sigs) >= (nr par)) pf)))))
  (lengthNatToLength (nr par) sigs (get pf)) refl refl
  (==vto≡ (getPayment pkh ctx) v (get (go continues (go ((lengthNat sigs) >= (nr par)) pf)))) refl
  (get (go ((lengthNat sigs) >= (nr par)) pf)) refl refl 
validatorImpliesTransition par (tok , Holding) Cancel record { tokenIn = tokenIn ; tokenOut = false } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Holding) Cancel record { tokenIn = tokenIn ; tokenOut = true  } nc pf = ⊥-elim (&&false tokenIn pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint  } nc pf
  rewrite ==tto≡ tok tok' (go (ltNat d time) (go continues (go (outputVal == inputVal) pf)))
  = TCancel ((<ᵇNto<N (get ((go continues (go (outputVal == inputVal) pf)))))) refl refl 
  (sym (==vto≡ outputVal inputVal (get pf))) refl (get (go (outputVal == inputVal) pf)) refl refl
validatorImpliesTransition par (tok , Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint } nc pf
  rewrite sym (==vto≡ v v' (get (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) pf)))))) |
  sym (==to≡ pkh pkh' (get (go (eqValue v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) pf))))))) |
  sym (==to≡ d d' (get (go (pkh == pkh') (go (eqValue v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) pf)))))))) |
  (==lto≡ sigs' (insert sig sigs) (get (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) pf))))))))) |
  (==tto≡ tok tok' (go (sigs' == (insert sig sigs)) (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) pf)))))))))
  = TAdd (queryTo∈ (get (go (sig == signature) (go (outputVal == inputVal) pf))))
  (sym (==to≡ sig signature (get (go (outputVal == inputVal) pf)))) refl refl --refl
  (sym (==vto≡ outputVal inputVal (get pf))) refl
  (get (go (query sig (authSigs par)) (go (sig == signature) (go (outputVal == inputVal) pf)))) refl refl
  
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Pay record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint } nc pf
  = ⊥-elim (&&2false (ltNat (nr par) (lengthNat sigs) || eqNat (lengthNat sigs) (nr par)) continues pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = true ; tokenOut = true ; mint = mint } nc pf = ⊥-elim (&&2false (eqValue outputVal inputVal) continues pf)





mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≡ 1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> getPar par adr oref tn ⊢ getMintS tn ctx
mintingImpliesStart adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Holding) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = .1 ; tokCurrSymbol = cs } refl pf
  = TStart refl (get (go ((cs , tn) == tok) (go (oref == inputRef) (go continues pf))))
  refl (get pf) (==to≡ oref inputRef (get (go continues pf)))
  (==tto≡ (cs , tn) tok (get (go (oref == inputRef) (go continues pf)))) refl
  (go (lovelaces 2xMinValue < lovelaces outputVal) (go ((cs , tn) == tok) (go (oref == inputRef) (go continues pf))))
mintingImpliesStart adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Collecting x x₁ x₂ x₃) ; time = time ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = .1  } refl pf = ⊥-elim (&&2false continues (eqNat oref inputRef) pf)


bothImplyClose : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
               -> getMintedAmount ctx ≡ -1
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref tn top ctx) ≡ true
               -> getPar par adr oref tn ⊢ getS d ctx ~[ Close ]~| getS' d ctx
bothImplyClose par d@(tok , Holding) adr oref tn top ctx@record { tokenOut = false ; mint = .-1 } refl p = TClose refl (get (go (checkTokenIn tok ctx) (get p))) refl (unNot (go (agdaValidator par d Close ctx) p)) (get (get p)) refl refl
bothImplyClose par (tok , Holding) adr oref tn top ctx@record { tokenOut = true ; mint = .-1 } refl p = ⊥-elim (&&false (checkTokenIn tok ctx) (get p))
bothImplyClose par (tok , Collecting x x₁ x₂ x₃) adr oref tn top ctx@record { tokenOut = false ; mint = .-1 } refl p = ⊥-elim (&&false (checkTokenIn tok ctx) (get p))
bothImplyClose par (tok , Collecting x x₁ x₂ x₃) adr oref tn top ctx@record { tokenOut = true ; mint = .-1 } refl p = ⊥-elim (&&false (checkTokenIn tok ctx) (get p))


--sub-lemmas for transition implies validation returns true


∈toQuery : ∀ {sig sigs} -> sig ∈ sigs -> (query sig sigs) ≡ true
∈toQuery {sig} (here refl) rewrite n=n sig = refl
∈toQuery (there pf) rewrite ∈toQuery pf = ||true

lengthToLengthNat : ∀ (n : Nat) (l : List PubKeyHash) -> n N.≤ length l -> (n N.<ᵇ lengthNat l || lengthNat l N.≡ᵇ n) ≡ true
lengthToLengthNat zero [] N.z≤n = refl
lengthToLengthNat zero (x ∷ l) N.z≤n = refl
lengthToLengthNat (N.suc n) [] ()
lengthToLengthNat (N.suc n) (x ∷ l) (N.s≤s p) = lengthToLengthNat n l p


transitionImpliesValidator : ∀ {adr oref tn} (par : Params) (dat : Label) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref tn ⊢ getS dat ctx ~[ i ]~> getS' dat ctx
                           -> agdaValidator par dat i ctx ≡ true
transitionImpliesValidator par (tok , .Holding) (Propose v pkh d) record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Collecting v pkh d []) ; continues = .true ; inputRef = inputRef ; tokenIn = .true ; tokenOut = .true } (TPropose p1 p2 refl refl refl p6 p7 refl refl refl)
  rewrite v=v inputVal | v=v v | n=n pkh | n=n d | t=t tok | p1 | p2 | ≤Nto≤ᵇN p6 = refl 
transitionImpliesValidator par (tok , Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Collecting v pkh d (insert sig sigs)) ; signature = .sig ; continues = .true ; tokenIn = .true ; tokenOut = .true } (TAdd p1 refl refl refl refl p6 refl refl refl)
  rewrite v=v inputVal | v=v v | n=n pkh | n=n d | t=t tok | l=l (insert sig sigs) | n=n sig | ∈toQuery p1 = refl
transitionImpliesValidator par (tok , Collecting v pkh d sigs) Pay record { inputVal = .(addValue outputVal v) ; outputVal = outputVal ; outputDatum = .(tok , Holding) ;  continues = cont ; tokenIn = .true ; tokenOut = .true } (TPay refl p2 refl refl refl refl p7 refl refl)
  rewrite v=v v | v=v (addValue outputVal v) | t=t tok | lengthToLengthNat (nr par) sigs p2 | p7 = refl
transitionImpliesValidator par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Holding) ; continues = .true ; inputRef = inputRef ; tokenIn = .true ; tokenOut = .true } (TCancel p1 refl refl refl p5 refl refl refl)
  rewrite v=v inputVal | t=t tok | <Nto<ᵇN p1 = refl


startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getPar par adr oref tn ⊢ getMintS tn ctx
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting adr oref tn top record { outputDatum = .((cs , tn) , Holding) ; continues = .true ; inputRef = .oref ; tokenOut = .true ; mint = .1 ; tokCurrSymbol = cs } (TStart refl p refl refl refl refl refl refl) rewrite n=n oref | t=t (cs , tn) | p = refl 



closeImpliesBoth : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
               -> (getPar par adr oref tn ⊢ getS d ctx ~[ Close ]~| getS' d ctx)
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref tn top ctx) ≡ true
closeImpliesBoth par (tok , Holding) adr oref tn top record { continues = .false ; tokenIn = .true ; tokenOut = .false ; mint = .-1 } (TClose refl p2 p3 refl refl refl refl) rewrite p2 = refl 


data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase


record Argument : Set where
  field
    par  : Params
    adr  : Address
    oref : TxOutRef
    tn   : TokenName
    dat  : Label
    inp  : Input
    ctx  : ScriptContext 
open Argument

Classifier : Argument -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = pos 0 } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = pos (suc 0) } } = Initial
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = pos (suc (suc n)) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = (negsuc (suc n)) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose x x₁ x₂) ; ctx = record { mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add x) ; ctx = record { mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = record { mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = record { mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = record { mint = (negsuc zero) } } = Terminal



totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial  = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) &&
                 agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)


totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial  = getPar (arg .par) (arg .adr) (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
... | Running  = getPar (arg .par) (arg .adr) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .dat) (arg .ctx) 
... | Terminal =  getPar (arg .par) (arg .adr) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .dat) (arg .ctx)


removeClose : ∀ (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getPar (arg .par) (arg .adr) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .dat) (arg .ctx)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose x x₁ x₂) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Propose x x₁ x₂) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add x) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Add x) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat Pay ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat Cancel ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Holding) ; inp = Close ; ctx = record { inputVal = inputVal ; continues = continues ; tokenIn = hasTokenIn ; tokenOut = false ; mint = mint } } p1 p2 = ⊥-elim (p1 (==ito≡ mint (negsuc 0) (go (not continues) (go (lovelaces 2xMinValue > lovelaces inputVal) (go hasTokenIn p2)))))
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Collecting x x₁ x₂ x₃) ; inp = Close ; ctx = record { tokenIn = hasTokenIn ; tokenOut = false } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Holding) ; inp = Close ; ctx = record { tokenIn = hasTokenIn ; tokenOut = true } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Collecting x x₁ x₂ x₃) ; inp = Close ; ctx = record { tokenIn = hasTokenIn ; tokenOut = true } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)


record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = pos 0 } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = inp ; ctx = ctx@record { mint = pos (suc 0) } }} x → mintingImpliesStart {par} adr oref tn tt ctx refl x ; --mintingImpliesStart adr oref tt ctx refl x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = pos (suc (suc n)) } }} x → removeClose arg (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { mint = (negsuc (suc n)) } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose v pkh d) ; ctx = ctx@record { mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Propose v pkh d) ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add pkh) ; ctx = ctx@record { mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Add pkh) ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx@record { mint = (negsuc zero) } }} x → validatorImpliesTransition par dat Pay ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx@record { mint = (negsuc zero) } }} x → validatorImpliesTransition par dat Cancel ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = Close ; ctx = ctx@record { mint = (negsuc zero) } }} x → bothImplyClose par dat adr oref tn tt ctx refl x } 
                    ; from = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { mint = pos 0 } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = inp ; ctx = ctx@record { mint = pos (suc 0) } }} x → startImpliesMinting {par} adr oref tn tt ctx x ; 
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { mint = pos (suc (suc n)) } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { mint = (negsuc (suc n)) } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose v pkh d) ; ctx = ctx@record { mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Propose v pkh d) ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add pkh) ; ctx = ctx@record { mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Add pkh) ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx@record { mint = (negsuc zero) } }} x → transitionImpliesValidator par dat Pay ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx@record { mint = (negsuc zero) } }} x → transitionImpliesValidator par dat Cancel ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = Close ; ctx = ctx@record { mint = (negsuc zero) } }} x → closeImpliesBoth par dat adr oref tn tt ctx x } }


inputRewrite : ∀ {oV t sig spn m tok} (par : MParams) (s s' : State) (i : Input)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ record
                           { datum = s .datum
                           ; value = s .value
                           ; outVal = oV
                           ; now = t
                           ; tsig = sig
                           ; continues = s .continues
                           ; spends = spn
                           ; hasToken = s .hasToken
                           ; mint = m
                           ; token = tok
                           } ~[ i ]~> s'
inputRewrite par s s' (Propose v pkh d) (TPropose x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = TPropose x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉
inputRewrite par s s' (Add pkh) (TAdd x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = TAdd x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈
inputRewrite par s s' Pay (TPay x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = TPay x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈
inputRewrite par s s' Cancel (TCancel x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = TCancel x x₁ x₂ x₃ x₄ x₅ x₆ x₇


