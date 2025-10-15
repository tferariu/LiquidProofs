
open import MultiSig

open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Int
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base

open import Haskell.Prim hiding (⊥ ; All; Any)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Tuple as Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)


module MultiSigProofs where

--open import ListInsertLib (PubKeyHash) (==ito≡) (=/=ito≢)

record Context : Set where
  field
    value         : Value  
    outVal        : Value
    outAdr        : PubKeyHash
    now           : Deadline
    tsig          : PubKeyHash
open Context



record State : Set where
  field
    datum      : Label
    value      : Value  
    outVal     : Value
    outAdr     : PubKeyHash
    now        : Deadline
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
        authSigs  : List PubKeyHash
        nr        : Nat
        maxWait   : Deadline
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s tok}
    -> datum s ≡ ( tok , Holding )
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> token s ≡ tok
    -> hasToken s ≡ true
    -------------------
    -> par ⊢ s


data _⊢_~[_]~>_ : MParams -> State -> Input -> State -> Set where
 
  TPropose : ∀ {v tok pkh d s s' par} 
    -> value s ≥ v
    -> v ≥ minValue
    -> datum s ≡ (tok , Holding)
    -> datum s' ≡ (tok , Collecting v pkh d [])
    -> value s ≡ value s'
    -> d ≤ (now s') + (maxWait par) 
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
    -> value s ≡ value s' + v
    -> length sigs ≥ nr par
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Holding)
    -> outVal s' ≡ v
    -> outAdr s' ≡ pkh 
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par v pkh d sigs tok} 
    -> now s' > d
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
    -> minValue > value s
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

≡ᵇto≡ : ∀ {a b} -> (a ≡ᵇ b) ≡ true -> a ≡ b
≡ᵇto≡ {zero} {zero} pf = refl
≡ᵇto≡ {suc a} {suc b} pf = cong suc (≡ᵇto≡ pf)


≡ⁱto≡ : ∀ {a b : Int} -> (a == b) ≡ true -> a ≡ b
≡ⁱto≡ {pos n} {pos m} pf = cong pos (≡ᵇto≡ pf)
≡ⁱto≡ {negsuc n} {negsuc m} pf = cong negsuc (≡ᵇto≡ pf)

==nto≡ : ∀ (a b : Nat) -> (a == b) ≡ true -> a ≡ b
==nto≡ zero zero pf = refl
==nto≡ (suc a) (suc b) pf = cong suc (==nto≡ a b pf)

==ito≡ : ∀ (a b : Int) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong pos (≡ᵇto≡ pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (≡ᵇto≡ pf)

--Valid State
data ValidS : State -> Set where

  Hol : ∀ {s tok}
    -> datum s ≡ (tok , Holding)
    -> hasToken s ≡ true
    ----------------
    -> ValidS s

  Stp : ∀ {s}
    -> continues s ≡ false
    -> hasToken s ≡ false
    ----------------
    -> ValidS s

  Col : ∀ {s v pkh d sigs tok}
    -> datum s ≡ ( tok , Collecting v pkh d sigs )
    -> value s ≥ v
    -> v ≥ minValue
    -> Unique sigs
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

get⊥ : true ≡ false -> ⊥
get⊥ ()

v=v : ∀ (v : Value) -> (v ≡ᵇ v) ≡ true
v=v zero = refl
v=v (suc v) = v=v v

=/=ito≢ : ∀ {a b : Int} -> (a == b) ≡ false -> a ≢ b
=/=ito≢ {pos n} {pos .n} pf refl rewrite v=v n = get⊥ pf
=/=ito≢ {negsuc n} {negsuc .n} pf refl rewrite v=v n = get⊥ pf


reduce∈ : ∀ {A : Set} {x y : A} {xs} -> y ∈ (x ∷ xs) -> y ≢ x -> y ∈ xs
reduce∈ (here px) p2 = ⊥-elim (p2 px)
reduce∈ (there p1) p2 = p1 


insertPreserves∈ : ∀ {x y zs}
  -> x ∈ insert y zs -> (y == x) ≡ false -> x ∈ zs
insertPreserves∈ {zs = []} (here px) p2 = ⊥-elim (=/=ito≢ p2 (sym px))
insertPreserves∈ {x} {y} {z ∷ zs} p1 p2 with y == x in eq1
...| true =  ⊥-elim (get⊥ p2)
...| false with y == z in eq2
...| true rewrite ==ito≡ y z eq2 = p1 
...| false with x == z in eq3
...| true rewrite ==ito≡ x z eq3 = here refl 
...| false = there (insertPreserves∈ (reduce∈ p1 (=/=ito≢ eq3)) eq1)


insertPreservesUniqueness : ∀ {sig sigs}
  -> Unique sigs -> Unique (insert sig sigs)
insertPreservesUniqueness root = (λ ()) :: root
insertPreservesUniqueness {sig} {(x ∷ xs)} (p :: ps) with sig == x in eq
...| false = (λ z → p (insertPreserves∈ z eq)) :: (insertPreservesUniqueness ps)
...| true rewrite ==ito≡ sig x eq = p :: ps


--State Validity Invariant
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> ValidS s
validStateInitial (TStart p1 p2 p3 p4 p5 p6) = Hol p1 p6

validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition iv (TPropose p1 (s≤s p2) p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 = Col p4 p1 (s≤s p2) root p10
validStateTransition {s} (Hol pf pf') (TAdd p1 p2 p3 p4 p5 p6 p7 p8 p9) = ⊥-elim (diffLabels (datum s) pf p3)
validStateTransition (Col pf1 pf2 pf3 pf4 pf5) (TAdd p1 p2 p3 p4 p5 p6 p7 p8 p9)
                     rewrite pf1 | sameValue p3 | p5 | sameSigs p3
                     = Col p4 pf2 pf3 (insertPreservesUniqueness pf4) p9
validStateTransition (Stp pf pf') (TAdd p1 p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf = ⊥-elim (get⊥ (sym p6))
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) = Hol p4 p10
validStateTransition iv (TCancel p1 p2 p3 p4 p5 p6 p7 p8) = Hol p3 p8

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
         -> outAdr s ≡ outAdr s'
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

prop {v} {pkh} {d} {sigs} {tok} record { datum = .(tok , Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token } record { datum = .(_ , Collecting v pkh d (insertList [] sigs)) ; value = .(value) ; outVal = .(outVal) ; outAdr = .(outAdr) ; now = .(now) ; tsig = .(finalSig (record { datum = tok , Collecting v pkh d sigs ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = true ; spends = spends ; hasToken = true ; mint = mint ; token = token }) (makeIs [])) ; continues = .true ; spends = .(spends) ; hasToken = .true ; mint = .(mint) ; token = .(token) } record { authSigs = .(asigs1 ++ []) ; nr = nr₁ ; maxWait = maxWait₁ } .(asigs1 ++ []) asigs1 [] refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl = root

prop {v} {pkh} {d} {sigs} {tok}
  s1@record { datum = .(tok , Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token }
  s2@record { datum = .(tok , Collecting v pkh d (insertList (x ∷ asigs2) sigs)) ; value = .(value) ; outVal = .(outVal) ; outAdr = .(outAdr) ; now = .(now) ; tsig = .(finalSig (record { datum = _ , Collecting v pkh d sigs ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = true ; spends = spends ; hasToken = true ; mint = mint ; token = token }) (makeIs (x ∷ asigs2))) ; continues = .true ; spends = .(spends) ; hasToken = .true ; mint = .(mint) ; token = .(token) }
  par@record { authSigs = .(asigs1 ++ x ∷ asigs2) ; nr = nr₁ ; maxWait = maxWait₁ } .(asigs1 ++ x ∷ asigs2) asigs1 (x ∷ asigs2) refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl refl
  = cons (TAdd (∈lemma asigs1 asigs2 x) refl refl refl refl refl refl refl refl)
    (prop s' s2 par (asigs1 ++ x ∷ asigs2) (asigs1 ++ [ x ]) asigs2 refl (appendLemma x asigs1 asigs2) refl refl refl refl refl refl refl refl refl (finalSigLemma s1 s' x asigs2 refl) refl refl refl refl)
    where
      s' = record
            { datum = tok , Collecting v pkh d (insert x sigs)
            ; value = value
            ; outVal = outVal
            ; outAdr = outAdr
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
        -> outAdr s ≡ outAdr s'
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
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 = prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 


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
... | true rewrite ==ito≡ x y eq = here refl

insert-lem2 : (x y : PubKeyHash)(l : List PubKeyHash) -> x ∈ l -> x ∈ insert y l
insert-lem2 x y [] pf = there pf
insert-lem2 x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite ==ito≡ y z eq | px = here refl
insert-lem2 x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem2 x y l pf) 
...| true rewrite ==ito≡ y z eq = there pf

del : ∀{x} (l : List a) -> x ∈ l -> List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) -> suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong suc (length-del p) 

∈-del : ∀{x y}{l : List a} (p : x ∈ l) -> x ≢ y -> y ∈ l -> y ∈ del l p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l1 l2 : List a} (p : x ∈ l2) -> (x ∉ l1) -> l1 ⊆ l2 -> l1 ⊆ del l2 p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e -> n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {l1 l2 : List a} -> l1 ⊆ l2 -> Unique l1 -> length l2 ≥ length l1
unique-lem [] root = z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = s≤s (unique-lem (subset-del px x sub) un)

insertList-sublem : (l1 l2 : List PubKeyHash) (x : PubKeyHash) -> x ∈ l2 -> x ∈ insertList l1 l2
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l1) l2 x pf = insertList-sublem l1 (insert y l2) x (insert-lem2 x y l2 pf)


insertList-lem : (l1 l2 : List PubKeyHash) -> l1 ⊆ insertList l1 l2
insertList-lem [] l = []
insertList-lem (x ∷ l1) l2 = insertList-sublem l1 (insert x l2) x (insert-lem1 x l2) ∷ insertList-lem l1 (insert x l2)

--Unique Insert Lemma
uil : ∀ (l1 l2 : List PubKeyHash) (pf : Unique l1) -> (length (insertList l1 l2) ≥ length l1)
uil l1 l2 pf = unique-lem (insertList-lem l1 l2) pf

--Valid Parameters
data ValidP : MParams -> Set where

  Always : ∀ {par}
    -> Unique (authSigs par)
    -> length (authSigs par) ≥ nr par
    ------------------
    -> ValidP par

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
          -> outAdr s' ≡ pkh
          -> value s ≡ value s' + v
          -> ValidP par
          -> continues s ≡ true
          -> continues s' ≡ true
          -> hasToken s ≡ true
          -> hasToken s' ≡ true
          -> tsig s' ≡ pkh
          -> par ⊢ s ~[ ((makeIs (authSigs par)) ++ [ Pay ]) ]~* s'


prop2 {d = d} {sigs = sigs} {tok = tok}
  s1@record { datum = .(tok , Collecting outVal outAdr d sigs) ; value = .(addNat value outVal) ; outVal = oV ; outAdr = oA ; now = now ; tsig = tsig ; continues = .true ; spends = spends ; hasToken = .true ; mint = mint ; token = token }
  s2@record { datum = .(tok , Holding) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = n ; tsig = outAdr ; continues = .true ; spends = spn ; hasToken = .true ; mint = m ; token = tok' } par (Col p1 p2 p3 p4 p7) refl refl refl refl refl (Always p5 p6) refl refl refl refl refl
  = lemmaMultiStep par s1 s' s2 (makeIs (authSigs par)) [ Pay ]
    (prop1 s1 s' par refl refl refl refl refl refl refl refl refl refl refl refl refl refl)
    (cons (TPay refl (≤-trans p6 (uil (authSigs par) sigs p5)) refl refl refl refl refl refl refl refl) root)
  where
    s' = record
          { datum = tok , (Collecting outVal outAdr d (insertList (authSigs par) sigs)) 
          ; value = addNat value outVal
          ; outVal = oV
          ; outAdr = oA
          ; now = now
          ; tsig = finalSig (record { datum = tok , Collecting outVal outAdr d sigs
                                    ; value = addNat value outVal
                                    ; outVal = oV
                                    ; outAdr = oA
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
                                                                             


takeLength : ∀ {a : Nat} {l : List PubKeyHash} -> length l ≥ a -> a ≤ length (take a l)
takeLength {.zero} {[]} z≤n = z≤n
takeLength {zero} {x ∷ l} p = z≤n
takeLength {suc a} {x ∷ l} (s≤s p) rewrite length-take a (x ∷ l) = s≤s (takeLength p)

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

v≤v : ∀ (v : Value) -> v ≤ v
v≤v zero = z≤n
v≤v (suc v) = s≤s (v≤v v)


≤ᵇto≤ : ∀ {a b} -> (a <ᵇ b || a ≡ᵇ b) ≡ true -> a ≤ b
≤ᵇto≤ {zero} {zero} pf = z≤n
≤ᵇto≤ {zero} {suc b} pf = z≤n
≤ᵇto≤ {suc a} {suc b} pf = s≤s (≤ᵇto≤ pf)

swapEqNat : ∀ (n m : Nat) -> eqNat n m ≡ eqNat m n
swapEqNat zero zero = refl
swapEqNat zero (suc m) = refl
swapEqNat (suc n) zero = refl
swapEqNat (suc n) (suc m) = swapEqNat n m

≤ᵇto≤' : ∀ {a b} -> (a <ᵇ b || b ≡ᵇ a) ≡ true -> a ≤ b
≤ᵇto≤' {a} {b} p rewrite swapEqNat b a = ≤ᵇto≤ p

n≤ᵇto> : ∀ {a b} -> (a <ᵇ b || a ≡ᵇ b) ≡ false -> a > b
n≤ᵇto> {suc a} {zero} pf = s≤s z≤n
n≤ᵇto> {suc a} {suc b} pf = s≤s (n≤ᵇto> pf)

--Weak Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
liquidity : ∀ (par : MParams) (s : State) (pkh : PubKeyHash) 
          -> ValidS s -> ValidP par -> continues s ≡ true
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ 0) )
          
liquidity par s pkh (Stp p1 p4) p2 p3 rewrite p1 = ⊥-elim (get⊥ (sym p3))
liquidity par
  s@record { datum = (tok , Holding) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } pkh (Hol refl p) (Always p2 p3) p4 with minValue <= value in eq
...| false = ⟨ s' , ⟨ [ Close ] , ((fin (TClose refl (n≤ᵇto> eq) p4 refl p refl refl) root) , refl) ⟩ ⟩
     where
       s' : State
       s' = record
             { datum = tok , Holding
             ; value = zero
             ; outVal = value
             ; outAdr = pkh
             ; now = now
             ; tsig = tsig
             ; continues = false
             ; spends = spends
             ; hasToken = false
             ; mint = -1
             ; token = tok } 
...| true  = ⟨ s'' , ⟨ ((Propose value pkh 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ])) ,
             (cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl z≤n p4 refl p refl)
             (prop2 s' s'' par (Col refl (v≤v value) (≤ᵇto≤ eq) root refl) refl refl refl refl refl (Always p2 p3) refl refl refl refl refl) , refl) ⟩ ⟩
     where
       s'' = record
              { datum = tok , Holding
              ; value = zero
              ; outVal = value
              ; outAdr = pkh
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
             ; outAdr = outAdr
             ; now = now
             ; tsig = tsig
             ; continues = true
             ; spends = spends
             ; hasToken = true
             ; mint = mint
             ; token = token
             }
liquidity par s@record { datum = (tok , Collecting v' pkh' d' sigs') ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } pkh (Col refl p2 p3 p4 p5) (Always p6 p7) p8 with minValue <= value in eq
...| false  = ⊥-elim (≤⇒≯ (≤-trans p3 p2) (n≤ᵇto> eq))
...| true  = ⟨ s''' , ⟨ (Cancel ∷ (Propose value pkh 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ])) ,
             ((cons (TCancel  {s' = s'} (s≤s (v≤v d')) refl refl refl p8 refl p5 refl)
             (cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl z≤n refl refl refl refl)
             (prop2 s'' s''' par (Col refl (v≤v value) (≤ᵇto≤ eq) root refl) refl refl refl refl refl (Always p6 p7) refl refl refl refl refl))) , refl) ⟩ ⟩
     where
       s''' = record
              { datum = tok , Holding
              ; value = zero
              ; outVal = value
              ; outAdr = pkh
              ; now = suc (suc (suc d'))
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
             ; outAdr = outAdr
             ; now = suc (suc d')
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
              ; outAdr = outAdr
              ; now = suc d'
              ; tsig = tsig
              ; continues = true
              ; spends = spends
              ; hasToken = true
              ; mint = mint
              ; token = token
              }






--sub-lemmas and helper functions for validator returning true implies transition

<ᵇto< : ∀ {a b} -> (a <ᵇ b) ≡ true -> a < b
<ᵇto< {zero} {suc b} pf = s≤s z≤n
<ᵇto< {suc a} {suc b} pf = s≤s (<ᵇto< pf)

&&false : ∀ (a : Bool) -> (a && false) ≡ true -> ⊥
&&false true ()

2&&false : ∀ (a b : Bool) -> (a && b && false) ≡ true -> ⊥
2&&false true true ()

4&&false : ∀ (a b c d : Bool) -> (a && b && c && d && false) ≡ true -> ⊥
4&&false true true true true ()

5&&false : ∀ (a b c d f : Bool) -> (a && b && c && d && f && false) ≡ true -> ⊥
5&&false true true true true true ()



go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl

≡ˡto≡ : ∀ {a b : List PubKeyHash} -> (a == b) ≡ true -> a ≡ b
≡ˡto≡ {[]} {[]} pf = refl
≡ˡto≡ {(x ∷ a)} {(y ∷ b)} pf rewrite (==ito≡ x y (get pf)) = cong (λ x -> y ∷ x) (≡ˡto≡ (go (x == y) pf))

==lto≡ : ∀ (a b : List PubKeyHash) -> (a == b) ≡ true -> a ≡ b
==lto≡ [] [] pf = refl
==lto≡ (x ∷ a) (y ∷ b) pf rewrite (==ito≡ x y (get pf)) = cong (λ x -> y ∷ x) (==lto≡ a b (go (x == y) pf))



orToSum : ∀ (a b : Bool) -> (a || b) ≡ true -> a ≡ true ⊎ b ≡ true
orToSum false true pf = inj₂ refl
orToSum true b pf = inj₁ refl

queryTo∈ : ∀ {sig sigs} -> (query sig sigs) ≡ true -> sig ∈ sigs
queryTo∈ {sig} {x ∷ sigs} pf with orToSum (x == sig) (query sig sigs) pf
... | inj₁ a = here (sym (==ito≡ x sig a))
... | inj₂ b = there (queryTo∈ b)


lengthNatToLength : ∀ (n : ℕ) (l : List PubKeyHash) -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true -> n ≤ length l
lengthNatToLength zero [] pf = z≤n
lengthNatToLength zero (x ∷ l) pf = z≤n
lengthNatToLength (suc n) (x ∷ l) pf = s≤s (lengthNatToLength n l pf)



getS : Label -> ScriptContext -> State
getS d ctx = record
              { datum = d
              ; value = inputVal ctx
              ; outVal = 0
              ; outAdr = 0
              ; now = 0
              ; tsig = 0
              ; continues = true
              ; spends = 0
              ; hasToken = hasTokenIn ctx
              ; mint = 0
              ; token = 0
              }



getS' : ScriptContext -> State
getS' ctx = record
             { datum = outputDatum ctx
             ; value = outputVal ctx
             ; outVal = payAmt ctx
             ; outAdr = payTo ctx
             ; now = time ctx
             ; tsig = signature ctx
             ; continues = continuing ctx
             ; spends = inputRef ctx
             ; hasToken = hasTokenOut ctx
             ; mint = mint ctx
             ; token = tokAssetClass ctx
             }

getPar : Params -> Address -> TxOutRef -> MParams
getPar p adr oref = record
                     { address = adr
                     ; outputRef = oref
                     ; authSigs = authSigs p
                     ; nr = nr p
                     ; maxWait = maxWait p
                     }



--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {adr oref} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Close
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx

validatorImpliesTransition par (tok , Holding) Close record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = false ; mint = mint ; tokAssetClass = tokAssetClass } nc pf = ⊥-elim (nc refl)
validatorImpliesTransition par (tok , Holding) (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  = ⊥-elim (5&&false (eqNat outputVal inputVal) (ltNat v inputVal || eqNat inputVal v) (ltNat 2 v || eqNat v 2)
    (ltNat d (addNat time (maxWait par)) || eqNat (addNat time (maxWait par)) d) continues  pf)
validatorImpliesTransition par (tok , Holding) Close record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v pkh d sigs) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = false ; mint = mint ; tokAssetClass = tokAssetClass } nc pf = ⊥-elim (nc refl)
validatorImpliesTransition par (tok , Holding) (Propose v pkh d) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  rewrite sym (==nto≡ v v' (get (go continues (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf))))))) |
  sym (==ito≡ pkh pkh' (get (go (eqNat v v') (go continues (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf)))))))) |
  sym (==nto≡ d d' (get (go (pkh == pkh') (go (eqNat v v') (go continues (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf))))))))) |
  (==lto≡ sigs' [] (get (go (d == d') (go (pkh == pkh') (go (eqNat v v') (go continues (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf)))))))))) |
  (==nto≡ tok tok' (go (sigs' == []) (go (d == d') (go (pkh == pkh') (go (eqNat v v') (go continues (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf))))))))))
  = TPropose (≤ᵇto≤' (get (go (eqNat outputVal inputVal) pf )))
     (≤ᵇto≤' (get (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf)))) refl
     refl (sym (≡ᵇto≡ (get pf)))
     (≤ᵇto≤' (get (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf))))) refl
     (get (go (notTooLate par d ctx) (go (v >= 2) (go (ltNat v inputVal || eqNat inputVal v) (go (eqNat outputVal inputVal) pf))))) refl refl
     
validatorImpliesTransition par (tok , Collecting v pkh d sigs) (Add x) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  = ⊥-elim (4&&false (eqNat outputVal inputVal) (eqInteger x signature) (query x (authSigs par)) continues pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Pay ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  rewrite ==ito≡ pkh payTo (get (get (go continues (go ((lengthNat sigs) >= (nr par)) pf)))) |
  sym (==nto≡ v payAmt (go (pkh == payTo) (get (go continues (go ((lengthNat sigs) >= (nr par)) pf))))) |
  ==nto≡ tok tok' (go (inputVal == (addNat outputVal v)) (go (checkPayment pkh v ctx) (go continues (go ((lengthNat sigs) >= (nr par)) pf))))
  = TPay (==nto≡ inputVal (addNat outputVal v) (get (go (checkPayment pkh v ctx) (go continues (go ((lengthNat sigs) >= (nr par)) pf)))))
  (lengthNatToLength (nr par) sigs (get pf)) refl refl refl refl refl
  (get (go ((lengthNat sigs) >= (nr par)) pf)) refl refl
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  rewrite ==nto≡ tok tok' (go (ltNat d time) (go continues (go (outputVal == inputVal) pf)))
  = TCancel (<ᵇto< (get ((go continues (go (outputVal == inputVal) pf))))) refl refl
  (sym (==nto≡ outputVal inputVal (get pf))) refl (get (go (outputVal == inputVal) pf)) refl refl
validatorImpliesTransition par (tok , Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  rewrite sym (==nto≡ v v' (get (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqNat outputVal inputVal) pf)))))) |
  sym (==ito≡ pkh pkh' (get (go (eqNat v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqNat outputVal inputVal) pf))))))) |
  sym (==nto≡ d d' (get (go (pkh == pkh') (go (eqNat v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqNat outputVal inputVal) pf)))))))) |
  (==lto≡ sigs' (insert sig sigs) (get (go (d == d') (go (pkh == pkh') (go (eqNat v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqNat outputVal inputVal) pf))))))))) |
  (==nto≡ tok tok' (go (sigs' == (insert sig sigs)) (go (d == d') (go (pkh == pkh') (go (eqNat v v') (go continues (go (query sig (authSigs par)) (go (sig == signature) (go (eqNat outputVal inputVal) pf)))))))))
  = TAdd (queryTo∈ (get (go (sig == signature) (go (outputVal == inputVal) pf))))
  (sym (==ito≡ sig signature (get (go (outputVal == inputVal) pf)))) refl refl
  (sym (==nto≡ outputVal inputVal (get pf))) refl
  (get (go (query sig (authSigs par)) (go (sig == signature) (go (outputVal == inputVal) pf)))) refl refl
  
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Pay record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf
  = ⊥-elim (2&&false (ltNat (nr par) (lengthNat sigs) || eqNat (lengthNat sigs) (nr par)) continues pf)
validatorImpliesTransition par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } nc pf = ⊥-elim (2&&false (eqNat outputVal inputVal) continues pf)




mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> mint ctx ≡ 1
                           -> (pf : agdaPolicy adr oref top ctx ≡ true)
                           -> getPar par adr oref ⊢ getS' ctx
mintingImpliesStart adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = .1 ; tokAssetClass = tokAssetClass } refl pf
  = TStart refl refl (get pf) (==nto≡ oref inputRef (get (go continues pf)))
  (==nto≡ tokAssetClass tok (get (go (oref == inputRef) (go continues pf))))
  (go (tokAssetClass == tok) (go (oref == inputRef) (go continues pf)))
mintingImpliesStart adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Collecting x x₁ x₂ x₃) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = .1 ; tokAssetClass = tokAssetClass } refl pf = ⊥-elim (2&&false continues (eqNat oref inputRef) pf)


unNot : (b : Bool) -> not b ≡ true -> b ≡ false
unNot false pf = refl

bothImplyClose : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> mint ctx ≡ -1
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref top ctx) ≡ true
               -> getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx
bothImplyClose par d@(tok , Holding) adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = false ; mint = .-1 ; tokAssetClass = tokAssetClass } refl p = TClose refl ((<ᵇto< (get (go hasTokenIn (get p))))) refl (unNot continues (go (agdaValidator par d Close ctx) p)) (get (get p)) refl refl
bothImplyClose par (tok , Holding) adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = true ; mint = .-1 ; tokAssetClass = tokAssetClass } refl p = ⊥-elim (&&false hasTokenIn (get p))
bothImplyClose par (tok , Collecting x x₁ x₂ x₃) adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = false ; mint = .-1 ; tokAssetClass = tokAssetClass } refl p = ⊥-elim (&&false hasTokenIn (get p))
bothImplyClose par (tok , Collecting x x₁ x₂ x₃) adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = true ; mint = .-1 ; tokAssetClass = tokAssetClass } refl p = ⊥-elim (&&false hasTokenIn (get p))


--sub-lemmas for transition implies validation returns true
≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a ≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl

≤to≤ᵇ : ∀ {a b} -> a ≤ b -> (a <ᵇ b || b ≡ᵇ a) ≡ true
≤to≤ᵇ {b = zero} z≤n = refl
≤to≤ᵇ {b = suc b} z≤n = refl
≤to≤ᵇ (s≤s pf) = ≤to≤ᵇ pf

<to<ᵇ : ∀ {a b} -> a < b -> (a <ᵇ b) ≡ true
<to<ᵇ {zero} (s≤s pf) = refl
<to<ᵇ {suc a} (s≤s pf) = <to<ᵇ pf

i=i : ∀ (i : Int) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = i=i (pos n)
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = i=i (pos n)



l=l : ∀ (l : List PubKeyHash) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite i=i x = l=l l

||true : ∀ {b} -> (b || true) ≡ true
||true {false} = refl
||true {true} = refl

∈toQuery : ∀ {sig sigs} -> sig ∈ sigs -> (query sig sigs) ≡ true
∈toQuery {sig} (here refl) rewrite i=i sig = refl
∈toQuery (there pf) rewrite ∈toQuery pf = ||true

lengthToLengthNat : ∀ (n : ℕ) (l : List PubKeyHash) -> n ≤ length l -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true
lengthToLengthNat zero [] z≤n = refl
lengthToLengthNat zero (x ∷ l) z≤n = refl
lengthToLengthNat (suc n) (x ∷ l) (s≤s pf) = lengthToLengthNat n l pf





transitionImpliesValidator : ∀ {adr oref} (par : Params) (dat : Label) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS dat ctx ~[ i ]~> getS' ctx
                           -> agdaValidator par dat i ctx ≡ true
transitionImpliesValidator par (tok , .Holding) (Propose v pkh d) record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Collecting v pkh d []) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = .true ; inputRef = inputRef ; hasTokenIn = .true ; hasTokenOut = .true ; mint = mint ; tokAssetClass = tokAssetClass } (TPropose p1 p2 refl refl refl p6 p7 refl refl refl)
  rewrite v=v inputVal | v=v v | i=i pkh | v=v d | v=v tok | ≤to≤ᵇ p1 | ≤to≤ᵇ p2 | ≤to≤ᵇ p6 = refl
transitionImpliesValidator par (tok , Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Collecting v pkh d (insert sig sigs)) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = .sig ; continues = .true ; inputRef = inputRef ; hasTokenIn = .true ; hasTokenOut = .true ; mint = mint ; tokAssetClass = tokAssetClass } (TAdd p1 refl refl refl refl p6 refl refl refl)
  rewrite v=v inputVal | v=v v | i=i pkh | v=v d | v=v tok | l=l (insert sig sigs) | i=i sig | ∈toQuery p1 = refl
transitionImpliesValidator par (tok , Collecting v pkh d sigs) Pay record { inputVal = .(addNat outputVal v) ; outputVal = outputVal ; outputDatum = .(tok , Holding) ; time = time ; payTo = .pkh ; payAmt = .v ; signature = signature ; continues = .true ; inputRef = inputRef ; hasTokenIn = .true ; hasTokenOut = .true ; mint = mint ; tokAssetClass = tokAssetClass } (TPay refl p2 refl refl refl refl p7 refl refl refl)
  rewrite i=i pkh | v=v v | v=v (addNat outputVal v) | v=v tok | lengthToLengthNat (nr par) sigs p2 = refl
transitionImpliesValidator par (tok , Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = .(inputVal) ; outputDatum = .(tok , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = .true ; inputRef = inputRef ; hasTokenIn = .true ; hasTokenOut = .true ; mint = mint ; tokAssetClass = tokAssetClass } (TCancel p1 refl refl refl p5 refl refl refl)
  rewrite v=v inputVal | v=v tok | <to<ᵇ p1 = refl


startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS' ctx
                           -> agdaPolicy adr oref top ctx ≡ true
startImpliesMinting adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = .(tokAssetClass , Holding) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = .true ; inputRef = .oref ; hasTokenIn = hasTokenIn ; hasTokenOut = .true ; mint = .1 ; tokAssetClass = tokAssetClass } (TStart refl refl refl refl refl refl) rewrite v=v oref | v=v tokAssetClass = refl



closeImpliesBoth : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> (getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx)
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref top ctx) ≡ true
closeImpliesBoth par (tok , Holding) adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = .false ; inputRef = inputRef ; hasTokenIn = .true ; hasTokenOut = .false ; mint = .-1 ; tokAssetClass = tokAssetClass } (TClose refl p2 p3 refl refl refl refl) rewrite <to<ᵇ p2 = refl



data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase


record Argument : Set where
  field
    par  : Params
    adr  : Address
    oref : TxOutRef
    dat  : Label
    inp  : Input
    ctx  : ScriptContext 
open Argument


Classifier : Argument -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (suc zero)) ; tokAssetClass = tokAssetClass } } = Initial
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (2+ n)) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (suc n)) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose x x₁ x₂) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Terminal


totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial  = agdaPolicy (arg .adr) (arg .oref) tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) &&
                 agdaPolicy (arg .adr) (arg .oref) tt (arg .ctx)


totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial  = getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS' (arg .ctx)
... | Running  = getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx) 
... | Terminal =  getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .ctx)


removeClose : ∀ (arg : Argument) -> (mint (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose x x₁ x₂) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Propose x x₁ x₂) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add x) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Add x) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat Pay ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat Cancel ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Holding) ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = false ; mint = mint ; tokAssetClass = tokAssetClass } } p1 p2 = ⊥-elim (p1 (==ito≡ mint (negsuc 0) (go (not continues) (go (gt 2 inputVal) (go hasTokenIn p2)))))
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Collecting x x₁ x₂ x₃) ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = false ; mint = mint ; tokAssetClass = tokAssetClass } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Holding) ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = (fst , Collecting x x₁ x₂ x₃) ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = true ; mint = mint ; tokAssetClass = tokAssetClass } } p1 p2 = ⊥-elim (&&false hasTokenIn p2)


record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos zero) ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (suc zero)) ; tokAssetClass = tokAssetClass } }} x → mintingImpliesStart adr oref tt ctx refl x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (2+ n)) ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (suc n)) ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose v pkh d) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat (Propose v pkh d) ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat (Add pkh) ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat Pay ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat Cancel ctx (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → bothImplyClose par dat adr oref tt ctx refl x } 
                    ; from = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (suc zero)) ; tokAssetClass = tokAssetClass } }} x → startImpliesMinting adr oref tt ctx x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (pos (2+ n)) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (suc n)) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Propose v pkh d) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat (Propose v pkh d) ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Add pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat (Add pkh) ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Pay ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat Pay ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Cancel ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat Cancel ctx x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → closeImpliesBoth par dat adr oref tt ctx x } }


inputRewrite : ∀ {oV oA t sig spn m tok} (par : MParams) (s s' : State) (i : Input)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ record
                           { datum = s .datum
                           ; value = s .value
                           ; outVal = oV
                           ; outAdr = oA
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
inputRewrite par s s' Pay (TPay x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = TPay x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉
inputRewrite par s s' Cancel (TCancel x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = TCancel x x₁ x₂ x₃ x₄ x₅ x₆ x₇



