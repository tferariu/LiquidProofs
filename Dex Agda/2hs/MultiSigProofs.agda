--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import MultiSig

open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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
open import Data.Product

open import Haskell.Prim hiding (⊥ ; All; Any)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
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
    label         : Label
    context       : Context
    stopped       : Bool
open State

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

--Transition Rules
data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TPropose : ∀ {v pkh d s s' par} 
    -> value (context s) ≥ v
    -> v ≥ minValue
    -> label s ≡ Holding
    -> label s' ≡ Collecting v pkh d []
    -> value (context s) ≡ value (context s')
    -> stopped s ≡ False
    -> stopped s' ≡ False
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'

  TAdd : ∀ {sig par s s' v pkh d sigs} 
    -> sig ∈ (authSigs par)
    -> tsig (context s') ≡ sig
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Collecting v pkh d (insert sig sigs)
    -> value (context s) ≡ value (context s')
    -> stopped s ≡ False
    -> stopped s' ≡ False
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'

  TPay : ∀ {v pkh d sigs s s' par} 
    -> tsig (context s') ≡ pkh
    -> value (context s) ≡ value (context s') + v
    -> length sigs ≥ nr par
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding
    -> outVal (context s') ≡ v
    -> outAdr (context s') ≡ pkh 
    -> stopped s ≡ False
    -> stopped s' ≡ False
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par v pkh d sigs} 
    -> now (context s') > d
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding  
    -> value (context s) ≡ value (context s') 
    -> stopped s ≡ False
    -> stopped s' ≡ False 
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'

  TClose : ∀ {par s s'}
    -> label s ≡ Holding
    -> minValue > value (context s)
    -> stopped s ≡ False
    -> stopped s' ≡ True
    -------------------
    -> par ⊢ s ~[ Close ]~> s'

data Unique {a : Set} : List a → Set where
  root : Unique []
  _::_ : {x : a} {l : List a} -> x ∉ l -> Unique l -> Unique (x ∷ l)

≡ᵇto≡ : ∀ {a b} -> (a ≡ᵇ b) ≡ true -> a ≡ b
≡ᵇto≡ {zero} {zero} pf = refl
≡ᵇto≡ {suc a} {suc b} pf = cong suc (≡ᵇto≡ pf)


==ito≡ : ∀ (a b : Int) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong pos (≡ᵇto≡ pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (sym (≡ᵇto≡ pf))

--Valid State
data ValidS : State -> Set where

  Hol : ∀ {s}
    -> label s ≡ Holding
    ----------------
    -> ValidS s

  Stp : ∀ {s}
    -> stopped s ≡ True
    ----------------
    -> ValidS s

  Col : ∀ {s v pkh d sigs}
    -> label s ≡ Collecting v pkh d sigs
    -> value (context s) ≥ v
    -> v ≥ minValue
    -> Unique sigs
    --------------------------------
    -> ValidS s

--Multi-Step Transition
data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


--State Validity sub-lemmas
diffLabels : ∀ {v pkh d sigs} (l : Label) -> l ≡ Holding
           -> l ≡ Collecting v pkh d sigs -> ⊥ 
diffLabels Holding p1 ()
diffLabels (Collecting v pkh d sigs) () p2

sameValue : ∀ {v v' pkh pkh' d d' sigs sigs'}
  -> Collecting v pkh d sigs ≡ Collecting v' pkh' d' sigs' -> v ≡ v'
sameValue refl = refl

sameSigs : ∀ {v v' pkh pkh' d d' sigs sigs'}
  -> Collecting v pkh d sigs ≡ Collecting v' pkh' d' sigs' -> sigs ≡ sigs'
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
validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition iv (TPropose p1 (s≤s p2) p3 p4 p5 p6 p7) rewrite p5 = Col p4 p1 (s≤s p2) root
validStateTransition {s} (Hol pf) (TAdd p1 p2 p3 p4 p5 p6 p7) = ⊥-elim (diffLabels (label s) pf p3)
validStateTransition (Col pf1 pf2 pf3 pf4) (TAdd p1 p2 p3 p4 p5 p6 p7)
                     rewrite pf1 | sameValue p3 | p5 | sameSigs p3
                     = Col p4 pf2 pf3 (insertPreservesUniqueness pf4)
validStateTransition {s} (Stp pf) (TAdd p1 p2 p3 p4 p5 p6 p7) rewrite pf = ⊥-elim (get⊥ p6)
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6 p7 p8 p9) = Hol p5
validStateTransition iv (TCancel p1 p2 p3 p4 p5 p6) = Hol p3
validStateTransition iv (TClose p1 p2 p3 p4) = Stp p4



validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x 



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
finalSig s [] = tsig (context s)
finalSig s (Propose x x₁ x₂ ∷ [])  = tsig (context s)
finalSig s (Add sig ∷ []) = sig
finalSig s (Pay ∷ []) = tsig (context s)
finalSig s (Cancel ∷ []) = tsig (context s)
finalSig s (i ∷ ls) = finalSig s ls

finalSigLemma : ∀ (s s' : State) (x : PubKeyHash) (xs : List PubKeyHash)
  -> tsig (context s') ≡ x -> finalSig s (makeIs (x ∷ xs)) ≡ finalSig s' (makeIs xs)
finalSigLemma s1 s2 x [] pf = sym pf
finalSigLemma s1 s2 x (y ∷ []) pf = refl
finalSigLemma s1 s2 x (y ∷ z ∷ xs) pf = finalSigLemma s1 s2 x (z ∷ xs) pf

--Generalized Prop1 (Can add signatures 1 by 1)
prop : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par)
         -> asigs ≡ (asigs' ++ asigs'')
         -> label s ≡ Collecting v pkh d sigs
         -> label s' ≡ Collecting v pkh d (insertList asigs'' sigs)
         -> outVal (context s) ≡ outVal (context s')
         -> outAdr (context s) ≡ outAdr (context s')
         -> now (context s) ≡ now (context s')
         -> value (context s) ≡ value (context s')
         -> tsig (context s') ≡ finalSig s (makeIs asigs'')
         -> stopped s ≡ False
         -> stopped s' ≡ False
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
           context = record { value = .value₁ ;
                              outVal = .outVal₁ ;
                              outAdr = .outAdr₁ ;
                              now = .now₁ ;
                              tsig = tsig₁ } ;
           stopped = False }
  record { label = .(Collecting v pkh d (insertList [] sigs)) ;
           context = record { value = value₁ ;
                              outVal = outVal₁ ;
                              outAdr = outAdr₁ ;
                              now = now₁ ;
                              tsig = .(finalSig (record { label = Collecting v pkh d sigs ;
                                                          context = record { value = value₁ ;
                                                                             outVal = outVal₁ ;
                                                                             outAdr = outAdr₁ ;
                                                                             now = now₁ ;
                                                                             tsig = tsig₁ } ;
                                                          stopped = False }) (makeIs [])) } ;
           stopped = False }
  record { authSigs = .(sigs2 ++ []) ;
           nr = nr₁ }
  .(sigs2 ++ []) sigs2 [] refl refl refl refl refl refl refl refl refl refl refl = root --root
  
prop {v} {pkh} {d} {sigs}
  s1@(record { label = .(Collecting v pkh d sigs) ;
               context = record { value = .value₁ ;
                                  outVal = .outVal₁ ;
                                  outAdr = .outAdr₁ ;
                                  now = .now₁ ;
                                  tsig = tsig₁ } })
  s2@(record { label = .(Collecting v pkh d (insertList (x ∷ sigs3) sigs)) ;
               context = record { value = value₁ ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = .(finalSig s1 (makeIs (x ∷ sigs3))) } })
  par@(record { authSigs = .(sigs2 ++ x ∷ sigs3) ; nr = nr₁ })
  .(sigs2 ++ x ∷ sigs3) sigs2 (x ∷ sigs3) refl refl refl refl refl refl refl refl refl refl refl
  
  = cons
    (TAdd (∈lemma sigs2 sigs3 x) refl refl refl refl refl refl)
    (prop s' s2 par (sigs2 ++ x ∷ sigs3) (sigs2 ++ [ x ]) sigs3 refl
          (appendLemma x sigs2 sigs3) refl refl refl refl refl refl
          (finalSigLemma s1 s' x sigs3 refl) refl refl)
    where
      s' = record { label = Collecting v pkh d (insert x sigs) ;
                    context = record { value = value₁ ;
                                       outVal = outVal₁ ;
                                       outAdr = outAdr₁ ;
                                       now = now₁ ;
                                       tsig = x }} 



prop' : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' asigs''' : List PubKeyHash)
         -> asigs ≡ (authSigs par)
         -> asigs ≡ (asigs' ++ asigs'' ++ asigs''')
         -> label s ≡ Collecting v pkh d sigs
         -> label s' ≡ Collecting v pkh d (insertList asigs'' sigs)
         -> outVal (context s) ≡ outVal (context s')
         -> outAdr (context s) ≡ outAdr (context s')
         -> now (context s) ≡ now (context s')
         -> value (context s) ≡ value (context s')
         -> tsig (context s') ≡ finalSig s (makeIs asigs'')
         -> stopped s ≡ False
         -> stopped s' ≡ False
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop' {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
           context = record { value = .value₁ ;
                              outVal = .outVal₁ ;
                              outAdr = .outAdr₁ ;
                              now = .now₁ ;
                              tsig = tsig₁ } ;
           stopped = False }
  record { label = .(Collecting v pkh d (insertList [] sigs)) ;
           context = record { value = value₁ ;
                              outVal = outVal₁ ;
                              outAdr = outAdr₁ ;
                              now = now₁ ;
                              tsig = .(finalSig (record { label = Collecting v pkh d sigs ;
                                                          context = record { value = value₁ ;
                                                                             outVal = outVal₁ ;
                                                                             outAdr = outAdr₁ ;
                                                                             now = now₁ ;
                                                                             tsig = tsig₁ } ;
                                                          stopped = False }) (makeIs [])) } ;
           stopped = False }
  record { authSigs = .(sigs2 ++ [] ++ sigs3) ;
           nr = nr₁ }
  .(sigs2 ++ [] ++ sigs3) sigs2 [] sigs3 refl refl refl refl refl refl refl refl refl refl refl = root 
  
prop' {v} {pkh} {d} {sigs}
  s1@(record { label = .(Collecting v pkh d sigs) ;
               context = record { value = .value₁ ;
                                  outVal = .outVal₁ ;
                                  outAdr = .outAdr₁ ;
                                  now = .now₁ ;
                                  tsig = tsig₁ } })
  s2@(record { label = .(Collecting v pkh d (insertList (x ∷ sigs3) sigs)) ;
               context = record { value = value₁ ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = .(finalSig s1 (makeIs (x ∷ sigs3))) } })
  par@(record { authSigs = .(sigs2 ++ x ∷ sigs3 ++ sigs4) ; nr = nr₁ })
  .(sigs2 ++ x ∷ sigs3 ++ sigs4) sigs2 (x ∷ sigs3) sigs4 refl refl refl refl refl refl refl refl refl refl refl
  
  = cons
    (TAdd (∈lemma sigs2 (sigs3 ++ sigs4) x) refl refl refl refl refl refl)
  
    (prop' s' s2 par (sigs2 ++ x ∷ sigs3 ++ sigs4) (sigs2 ++ [ x ]) sigs3 sigs4 refl 
          (appendLemma x sigs2 (sigs3 ++ sigs4)) refl refl refl refl refl refl
          (finalSigLemma s1 s' x sigs3 refl) refl refl)
    where
      s' = record { label = Collecting v pkh d (insert x sigs) ;
                    context = record { value = value₁ ;
                                       outVal = outVal₁ ;
                                       outAdr = outAdr₁ ;
                                       now = now₁ ;
                                       tsig = x }} 


--Actual Prop1 (Can add all signatures 1 by 1)
prop1 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (authSigs par) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (authSigs par))
        -> stopped s ≡ False
        -> stopped s' ≡ False
        -> par ⊢ s ~[ (makeIs (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 = prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8 p9




--Prop3 (Can add minimum nr of signatures 1 by 1)
prop3 : ∀ { v pkh d sigs } (s s' : State) (par : Params) 
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (take (nr par) (authSigs par)) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (take (nr par) (authSigs par)))
         -> stopped s ≡ False
         -> stopped s' ≡ False
        -> par ⊢ s ~[ (makeIs (take (nr par) (authSigs par))) ]~* s'
prop3 s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 = prop' s s' par (authSigs par) [] (take (nr par) (authSigs par)) (drop (nr par) (authSigs par)) refl (sym (take++drop (nr par) (authSigs par))) p1 p2 p3 p4 p5 p6 p7 p8 p9


--Prop3 (Can add minimum nr of signatures 1 by 1)
prop3' : ∀ { v pkh d sigs } (s s' : State) (par : Params) 
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (drop (length (authSigs par) - nr par) (authSigs par)) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (drop (length (authSigs par) - nr par) (authSigs par)))
         -> stopped s ≡ False
         -> stopped s' ≡ False
        -> par ⊢ s ~[ (makeIs (drop (length (authSigs par) - nr par) (authSigs par))) ]~* s'
prop3' s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 = prop s s' par (authSigs par) (take (length (authSigs par) - nr par) (authSigs par)) (drop (length (authSigs par) - nr par) (authSigs par)) refl (sym (take++drop (monusNat (foldr (λ _ → suc) zero (authSigs par)) (nr par)) (authSigs par))) p1 p2 p3 p4 p5 p6 p7 p8 p9

--prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8 p9



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
data ValidP : Params -> Set where

  Always : ∀ {par}
    -> Unique (authSigs par)
    -> length (authSigs par) ≥ nr par
    ------------------
    -> ValidP par


--Multi-Step lemma
lemmaMultiStep : ∀ (par : Params) (s s' s'' : State) (is is' : List Input)
                   -> par ⊢ s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep par s .s s'' [] is' root p2 = p2
lemmaMultiStep par s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)


--Prop2 (Can add signatures 1 by 1 and then pay)
prop2' : ∀ { v pkh d sigs } (s s' : State) (par : Params)
          -> ValidS s
          -> label s ≡ Collecting v pkh d sigs
          -> label s' ≡ Holding
          -> outVal (context s') ≡ v
          -> outAdr (context s') ≡ pkh
          -> value (context s) ≡ value (context s') + v
          -> ValidP par
          -> stopped s ≡ False
          -> stopped s' ≡ False
          -> tsig (context s') ≡ pkh
          -> par ⊢ s ~[ ((makeIs (authSigs par)) ++ [ Pay ]) ]~* s'
prop2' {d = d} {sigs = sigs}
  s1@(record { label = .(Collecting (outVal context₁) (outAdr context₁) d sigs) ;
               context = record { value = .(addNat (value context₁) (outVal context₁)) ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = tsig₁ } })
  s2@record { label = .Holding ; context = context₁ }
  par (Col p1 p2 p3 p6) refl refl refl refl refl (Always p4 p5) refl refl refl
  = lemmaMultiStep par s1 s' s2 (makeIs (authSigs par)) [ Pay ]   
    (prop1 s1 s' par refl refl refl refl refl refl refl refl refl)
    (cons (TPay refl refl (≤-trans p5 (uil (authSigs par) sigs p4)) refl refl refl refl refl refl) root)
      where
        s' = record { label = Collecting (outVal context₁) (outAdr context₁) d (insertList (authSigs par) sigs) ;
                       context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                          outVal = outVal₁ ;
                                          outAdr = outAdr₁ ;
                                          now = now₁ ;
                                          tsig = finalSig (record { label = (Collecting (outVal context₁) (outAdr context₁) d sigs) ;
                                                                    context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                                                              outVal = outVal₁ ;
                                                                              outAdr = outAdr₁ ;
                                                                              now = now₁ ;
                                                                              tsig = tsig₁ } }) (makeIs (authSigs par)) } }


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


prop2 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
          -> ValidS s
          -> label s ≡ Collecting v pkh d sigs
          -> label s' ≡ Holding
          -> outVal (context s') ≡ v
          -> outAdr (context s') ≡ pkh
          -> value (context s) ≡ value (context s') + v
          -> ValidP par
          -> stopped s ≡ False
          -> stopped s' ≡ False
          -> tsig (context s') ≡ pkh
          -> par ⊢ s ~[ ((makeIs (take (nr par) (authSigs par))) ++ [ Pay ]) ]~* s'
prop2 {d = d} {sigs = sigs}
  s1@(record { label = .(Collecting (outVal context₁) (outAdr context₁) d sigs) ;
               context = record { value = .(addNat (value context₁) (outVal context₁)) ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = tsig₁ } })
  s2@record { label = .Holding ; context = context₁ }
  par (Col p1 p2 p3 p6) refl refl refl refl refl (Always p4 p5) refl refl refl
  = lemmaMultiStep par s1 s' s2 (makeIs (take (nr par) (authSigs par))) [ Pay ]   
    (prop3 s1 s' par refl refl refl refl refl refl refl refl refl)
    (cons (TPay refl refl (≤-trans (takeLength p5) (uil (take (nr par) (authSigs par)) sigs (takeUnique p4))) refl refl refl refl refl refl) root)
    --(≤-trans p5 (uil (authSigs par) sigs p4))
      where
        s' = record { label = Collecting (outVal context₁) (outAdr context₁) d (insertList (take (nr par) (authSigs par)) sigs) ;
                       context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                          outVal = outVal₁ ;
                                          outAdr = outAdr₁ ;
                                          now = now₁ ;
                                          tsig = finalSig (record { label = (Collecting (outVal context₁) (outAdr context₁) d sigs) ;
                                                                    context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                                                              outVal = outVal₁ ;
                                                                              outAdr = outAdr₁ ;
                                                                              now = now₁ ;
                                                                              tsig = tsig₁ } }) (makeIs (take (nr par) (authSigs par))) } }




v≤v : ∀ (v : Value) -> v ≤ v
v≤v zero = z≤n
v≤v (suc v) = s≤s (v≤v v)


≤ᵇto≤ : ∀ {a b} -> (a <ᵇ b || a ≡ᵇ b) ≡ true -> a ≤ b
≤ᵇto≤ {zero} {zero} pf = z≤n
≤ᵇto≤ {zero} {suc b} pf = z≤n
≤ᵇto≤ {suc a} {suc b} pf = s≤s (≤ᵇto≤ pf)

n≤ᵇto> : ∀ {a b} -> (a <ᵇ b || a ≡ᵇ b) ≡ false -> a > b
n≤ᵇto> {suc a} {zero} pf = s≤s z≤n
n≤ᵇto> {suc a} {suc b} pf = s≤s (n≤ᵇto> pf)

--Weak Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> ValidS s -> ValidP par -> stopped s ≡ False
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value (context s') ≡ 0) )
          
liquidity' par s pkh d (Stp p1) valid p2 rewrite p1 = ⊥-elim (get⊥ p2)

liquidity' par
  s@(record { label = .Holding ;
              context = record { value = value ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol refl) (Always p2 p3) pf with minValue <= value in eq
...| false  = ⟨ s' , ⟨  [ Close ] , ⟨ cons (TClose refl (n≤ᵇto> eq) pf refl) root , refl ⟩ ⟩ ⟩
      where
        s' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = tsig } ;
                      stopped = True }
...| true  = ⟨ s'' , ⟨ (Propose value pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl pf refl)
    (prop2' s' s'' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p2 p3) refl refl refl ) , refl ⟩ ⟩ ⟩
      where
        s'' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = pkh } ;
                      stopped = false }
        s' = record { label = Collecting value pkh d [] ;
                       context = record { value = value ;
                                          outVal = outVal ;
                                          outAdr = outAdr ;
                                          now = now ;
                                          tsig = tsig } ;
                      stopped = false }



liquidity' par
  s@(record { label = (Collecting v' pkh' d' sigs') ;
             context = record { value = value ;
                                outVal = outVal ;
                                outAdr = outAdr ;
                                now = now ;
                                tsig = tsig } } )
  pkh d (Col refl p2 p3 p6) (Always p4 p5) pf with minValue <= value in eq
...| false  = ⊥-elim (≤⇒≯ (≤-trans p3 p2) (n≤ᵇto> eq))

...| true  = ⟨ s''' , ⟨ Cancel ∷ (Propose value pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TCancel {s' = s'}
    (s≤s (v≤v d')) refl refl refl pf refl)
    (cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl refl refl)
    (prop2' s'' s''' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p4 p5) refl refl refl)) , refl ⟩ ⟩ ⟩
      where
        s''' = record { label = Holding ;
                       context = record { value = zero ;
                                          outVal = value ;
                                          outAdr = pkh ;
                                          now = now ;
                                          tsig = pkh } ;
                      stopped = false }
        s' = record { label = Holding ;
                      context = record { value = value ;
                                         outVal = outVal ;
                                         outAdr = outAdr ;
                                         now = suc d' ;
                                         tsig = tsig } ;
                      stopped = false }
        s'' = record { label = Collecting value pkh d [] ;
                        context = record { value = value ;
                                           outVal = outVal ;
                                           outAdr = outAdr ;
                                           now = d + 1 ;
                                           tsig = tsig } ;
                      stopped = false }
                      



getSigNr : List Input -> Nat
getSigNr [] = 0
getSigNr ((Add x) ∷ xs) = 1 + getSigNr xs
getSigNr (x ∷ xs) = getSigNr xs

sigNrSum : ∀ (l1 l2 : List Input) -> getSigNr l1 + getSigNr l2 ≡ getSigNr (l1 ++ l2)
sigNrSum [] l2 = refl
sigNrSum (Propose x x₁ x₂ ∷ l1) l2 = sigNrSum l1 l2
sigNrSum (Add x ∷ l1) l2 = cong suc (sigNrSum l1 l2)
sigNrSum (Pay ∷ l1) l2 = sigNrSum l1 l2
sigNrSum (Cancel ∷ l1) l2 = sigNrSum l1 l2
sigNrSum (Close ∷ l1) l2 = sigNrSum l1 l2

sigNrRewrite : ∀ (sigs : List PubKeyHash) -> getSigNr (makeIs (sigs)) ≡ length sigs
sigNrRewrite [] = refl
sigNrRewrite (x ∷ sigs) = cong suc (sigNrRewrite sigs)

⊓Lemma : ∀ {n m} -> n ≤ m -> n ⊓ m ≡ n
⊓Lemma {.zero} {m} z≤n = refl
⊓Lemma {.(suc _)} {.(suc _)} (s≤s p) = cong suc (⊓Lemma p)

sigNrLemma : ∀ {n : Nat} {sigs : List PubKeyHash} {is : List Input}
  -> n ≤ length sigs
  -> getSigNr is ≡ 0
  -> getSigNr (makeIs (take n sigs) ++ is) ≤ n
sigNrLemma {n} {sigs} {is} p1 p2 rewrite sym (sigNrSum (makeIs (take n sigs)) is) | sigNrRewrite (take n sigs)
  | p2 | +-identityʳ (length (take n sigs)) | length-take n sigs | ⊓Lemma p1 = v≤v n

--Strong Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs containing at most n "honest
--participants" signing Add transitions such that we can transition
--there and have no value left in the contract)
liquidity : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> ValidS s -> ValidP par -> stopped s ≡ False
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') ×
            ((value (context s') ≡ 0) × (getSigNr is ≤ nr par) ) )

liquidity par s pkh d (Stp p1) valid p2 rewrite p1 = ⊥-elim (get⊥ p2)

liquidity par
  s@(record { label = .Holding ;
              context = record { value = value ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol refl) (Always p2 p3) pf with minValue <= value in eq
...| false  = ⟨ s' , ⟨  [ Close ] , ⟨ cons (TClose refl (n≤ᵇto> eq) pf refl) root , ⟨ refl , z≤n ⟩ ⟩ ⟩ ⟩
      where
        s' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = tsig } ;
                      stopped = True }
...| true = ⟨ s'' , ⟨ (Propose value pkh d) ∷ ((makeIs (take (nr par) (authSigs par))) ++ [ Pay ]) ,
    ⟨ cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl pf refl)
    (prop2 s' s'' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p2 p3) refl refl refl ) ,
    ⟨ refl , sigNrLemma p3 refl ⟩ ⟩ ⟩ ⟩
      where
        s'' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = pkh } ;
                      stopped = false }
        s' = record { label = Collecting value pkh d [] ;
                       context = record { value = value ;
                                          outVal = outVal ;
                                          outAdr = outAdr ;
                                          now = now ;
                                          tsig = tsig } ;
                      stopped = false }



liquidity par
  s@(record { label = (Collecting v' pkh' d' sigs') ;
             context = record { value = value ;
                                outVal = outVal ;
                                outAdr = outAdr ;
                                now = now ;
                                tsig = tsig } } )
  pkh d (Col refl p2 p3 p6) (Always p4 p5) pf with minValue <= value in eq
...| false  = ⊥-elim (≤⇒≯ (≤-trans p3 p2) (n≤ᵇto> eq))

...| true  = ⟨ s''' , ⟨ Cancel ∷ (Propose value pkh d) ∷ ((makeIs (take (nr par) (authSigs par))) ++ [ Pay ]) ,
    ⟨ cons (TCancel {s' = s'}
    (s≤s (v≤v d')) refl refl refl pf refl)
    (cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl refl refl)
    (prop2 s'' s''' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p4 p5) refl refl refl)) ,
    ⟨ refl , (sigNrLemma p5 refl) ⟩ ⟩ ⟩ ⟩
      where
        s''' = record { label = Holding ;
                       context = record { value = zero ;
                                          outVal = value ;
                                          outAdr = pkh ;
                                          now = now ;
                                          tsig = pkh } ;
                      stopped = false }
        s' = record { label = Holding ;
                      context = record { value = value ;
                                         outVal = outVal ;
                                         outAdr = outAdr ;
                                         now = suc d' ;
                                         tsig = tsig } ;
                      stopped = false }
        s'' = record { label = Collecting value pkh d [] ;
                        context = record { value = value ;
                                           outVal = outVal ;
                                           outAdr = outAdr ;
                                           now = d + 1 ;
                                           tsig = tsig } ;
                      stopped = false }

   


--sub-lemmas and helper functions for validator returning true implies transition

<ᵇto< : ∀ {a b} -> (a <ᵇ b) ≡ true -> a < b
<ᵇto< {zero} {suc b} pf = s≤s z≤n
<ᵇto< {suc a} {suc b} pf = s≤s (<ᵇto< pf)

3&&false : ∀ (a b c : Bool) -> (a && b && c && false) ≡ true -> ⊥
3&&false true true true ()

&&false : ∀ (a : Bool) -> (a && false) ≡ true -> ⊥
&&false true ()

get : ∀ (a : Bool) {b} -> (a && b) ≡ true -> a ≡ true
get true pf = refl

go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

==lto≡ : ∀ (a b : List PubKeyHash) -> (a == b) ≡ true -> a ≡ b
==lto≡ [] [] pf = refl
==lto≡ (x ∷ a) (y ∷ b) pf rewrite (==ito≡ x y (get (x == y) pf)) = cong (λ x -> y ∷ x) (==lto≡ a b (go (x == y) pf))

p1 : ∀ (a b c d e f : Bool) (x y : Value) -> ((x ≡ᵇ y) && a && b && c && d && e && f) ≡ true -> x ≡ y
p1 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y)  pf)

p2 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && (x <ᵇ y || x ≡ᵇ y) && b && c && d && e && f) ≡ true -> x ≤ y
p2 a b c d e f x y pf = ≤ᵇto≤ ( get ((x <ᵇ y || x ≡ᵇ y)) (go a pf) )

p3 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && b && (x <ᵇ y) && c && d && e && f) ≡ true -> x < y
p3 a b c d e f x y pf = <ᵇto< ( get (x <ᵇ y) (go b (go a pf)) )

p4 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && b && c && (x ≡ᵇ y) && d && e && f) ≡ true -> x ≡ y
p4 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) (go c (go b (go a pf))) )

p5 : ∀ (a b c d e f : Bool) (x y : PubKeyHash) -> (a && b && c && d && (x == y) && e && f) ≡ true -> x ≡ y
p5 a b c d e f x y pf = ==ito≡ x y (get (x == y) (go d (go c (go b (go a pf)))) )

p6 : ∀ (a b c d e f : Bool) (x y : Deadline) -> (a && b && c && d && e && (x ≡ᵇ y) && f) ≡ true -> x ≡ y
p6 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) (go e (go d (go c (go b (go a pf))))))

p7 : ∀ (a b c d e f : Bool) (x y : List PubKeyHash) -> (a && b && c && d && e && f && (x == y)) ≡ true -> x ≡ y
p7 a b c d e f x y pf = ==lto≡ x y (go f (go e (go d (go c (go b (go a pf))))))

orToSum : ∀ (a b : Bool) -> (a || b) ≡ true -> a ≡ true ⊎ b ≡ true
orToSum false true pf = inj₂ refl
orToSum true b pf = inj₁ refl

queryTo∈ : ∀ {sig sigs} -> (query sig sigs) ≡ true -> sig ∈ sigs
queryTo∈ {sig} {x ∷ sigs} pf with orToSum (x == sig) (query sig sigs) pf
... | inj₁ a = here (sym (==ito≡ x sig a))
... | inj₂ b = there (queryTo∈ b)

a2 : ∀ (a b c d e f : Bool) (x y : PubKeyHash) -> (a && (x == y) && b && c && d && e && f) ≡ true -> x ≡ y
a2 a b c d e f x y pf = ==ito≡ x y ( get (x == y) (go a pf) )

a3 : ∀ (a b c d e f : Bool) (sig : PubKeyHash) (sigs : List PubKeyHash) -> (a && b && (query sig sigs) && c && d && e && f) ≡ true -> sig ∈ sigs
a3 a b c d e f sig sigs pf = queryTo∈ ( get (query sig sigs) (go b (go a pf)) )

lengthNatToLength : ∀ (n : ℕ) (l : List PubKeyHash) -> (n <ᵇ lengthNat l || n ≡ᵇ lengthNat l ) ≡ true -> n ≤ length l
lengthNatToLength zero [] pf = z≤n
lengthNatToLength zero (x ∷ l) pf = z≤n
lengthNatToLength (suc n) (x ∷ l) pf = s≤s (lengthNatToLength n l pf)

y1 : ∀ (a b c : Bool) (n : ℕ) (sigs : List PubKeyHash) -> ((n <ᵇ lengthNat sigs || n ≡ᵇ lengthNat sigs) && (a && b) && c) ≡ true -> n ≤ length sigs
y1 a b c n sigs pf = lengthNatToLength n sigs (get (n <ᵇ lengthNat sigs || n ≡ᵇ lengthNat sigs) pf)

y2 : ∀ (a b c : Bool) (x y : PubKeyHash) -> (a && ((x == y) && b) && c) ≡ true -> x ≡ y
y2 a b c x y pf = ==ito≡ x y (get (x == y) (get ((x == y) && b) (go a pf)))

y3 : ∀ (a b c : Bool) (x y : Value) -> (a && (b && (x ≡ᵇ y)) && c) ≡ true -> x ≡ y
y3 a b c x y pf = ≡ᵇto≡ (go b (get (b && (x ≡ᵇ y)) (go a pf)))

y4 : ∀ (a b c : Bool) (x y : Value) -> (a && (b && c) && x ≡ᵇ y) ≡ true -> x ≡ y
y4 a b c x y pf = ≡ᵇto≡ (go (b && c) (go a pf))

c1 : ∀ (a : Bool) (x y : Value) -> (x ≡ᵇ y && a) ≡ true -> x ≡ y
c1 a x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) pf) 

c2 : ∀ (a : Bool) (x y : Deadline) -> (a && (x <ᵇ y)) ≡ true -> x < y
c2 a x y pf = <ᵇto< (go a pf)

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {oV oA t s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           outVal = oV ; outAdr = oA ; now = t ; tsig = s } ; stopped = false }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                           outVal = payAmt ctx ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx } ;
                           stopped = stopsCont ctx}

validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = ⊥-elim (3&&false (eqNat outputVal inputVal) (ltNat v inputVal || eqNat v inputVal) (ltNat 2 v || eqNat 2 v) pf)
validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = TPropose {!!} {!!} refl {!!} {!!} refl {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = ⊥-elim (3&&false (eqNat outputVal inputVal) (eqInteger sig signature) (query sig (authSigs par)) pf)
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = ⊥-elim (&&false (ltNat (nr par) (lengthNat sigs) || eqNat (nr par) (lengthNat sigs)) pf)
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = stopsCont } pf
  = ⊥-elim (&&false (eqNat outputVal inputVal) pf)
validatorImpliesTransition par Holding Close
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = outputLabel ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = false } pf
  = ⊥-elim (&&false (ltNat inputVal 2) pf)
validatorImpliesTransition par Holding Close
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = outputLabel ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature ;
           stopsCont = true } pf
  = {!!}


{-validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) ( (v <ᵇ inputVal || v ≡ᵇ inputVal)) (0 <ᵇ v) {!!})
validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  rewrite p1 (v <ᵇ inputVal || v ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) outputVal inputVal pf
  | sym (p4 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || v ≡ᵇ inputVal) (0 <ᵇ v) (pkh == pkh') (d ≡ᵇ d') (sigs' == []) v v' pf)
  | p5 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || v ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (d ≡ᵇ d') (sigs' == []) pkh pkh' pf
  | p6 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || v ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (sigs' == []) d d' pf
  | p7 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || v ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs' [] pf
  = TPropose (p2 (outputVal ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) v inputVal pf)
    (p3 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || v ≡ᵇ inputVal) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) 0 v pf) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) pf)
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  rewrite p1 (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) outputVal inputVal pf
  | sym (p4 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) v v' pf)
  | p5 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (d ≡ᵇ d') (sigs' == (insert sig sigs)) pkh pkh' pf
  | p6 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (sigs' == (insert sig sigs)) d d' pf
  | p7 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs' (insert sig sigs) pf
  = TAdd (a3 (outputVal ≡ᵇ inputVal) (sig == signature) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig (authSigs par) pf)
  (sym (a2 (outputVal ≡ᵇ inputVal) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig signature pf)) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = TPay (y4 (nr par <ᵇ lengthNat sigs || nr par ≡ᵇ lengthNat sigs) (pkh == payTo) (v ≡ᵇ payAmt) inputVal (outputVal + v) pf)
    (y1 (eqInteger pkh payTo) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) (nr par) sigs pf) refl refl
    (sym (y3 (nr par <ᵇ lengthNat sigs || nr par ≡ᵇ lengthNat sigs) (pkh == payTo) (inputVal ≡ᵇ outputVal + v) v payAmt pf))
    (sym (y2 (nr par <ᵇ lengthNat sigs || nr par ≡ᵇ lengthNat sigs) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) pkh payTo pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (&&false ((nr par <ᵇ lengthNat sigs || nr par ≡ᵇ lengthNat sigs )) pf) 
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = TCancel (c2 (outputVal ≡ᵇ inputVal) d time pf) refl refl (sym (c1 (d <ᵇ time) outputVal inputVal pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (&&false (outputVal ≡ᵇ inputVal) pf) -}


--sub-lemmas for transition implies validation returns true
≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a ≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl

≤to≤ᵇ : ∀ {a b} -> a ≤ b -> (a <ᵇ b || a ≡ᵇ b) ≡ true
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

lengthToLengthNat : ∀ (n : ℕ) (l : List PubKeyHash) -> n ≤ length l -> (n <ᵇ lengthNat l || n ≡ᵇ lengthNat l) ≡ true
lengthToLengthNat zero [] z≤n = refl
lengthToLengthNat zero (x ∷ l) z≤n = refl
lengthToLengthNat (suc n) (x ∷ l) (s≤s pf) = lengthToLengthNat n l pf



transitionImpliesValidator : ∀ {oV oA t s stp} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           outVal = oV ; outAdr = oA ; now = t ; tsig = s } ; stopped = stp }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                           outVal = payAmt ctx ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx } ;
                           stopped = stopsCont ctx })
                           -> agdaValidator par l i ctx ≡ true


transitionImpliesValidator = {!!}

{-
transitionImpliesValidator par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting _ _ _ []) ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature }
  (TPropose p1 p2 refl refl p5)
  rewrite ≡to≡ᵇ (sym p5) | ≤to≤ᵇ p1 | <to<ᵇ p2 | v=v v | i=i pkh | v=v d = refl
transitionImpliesValidator par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = .(inputVal) ;
           outputLabel = (Collecting .v .pkh .d .(insert sig sigs)) ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = .sig }
  (TAdd p1 refl refl refl refl)
  rewrite v=v inputVal | i=i sig | ∈toQuery p1 | v=v v | i=i pkh | v=v d | l=l (insert sig sigs) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) Pay
  record { inputVal = .(addNat outputVal v) ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = .pkh ;
           payAmt = .v ;
           signature = signature }
  (TPay refl p2 refl refl refl refl)
  rewrite i=i pkh | v=v v | lengthToLengthNat (nr par) sigs p2 | v=v (outputVal + v) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = .(inputVal) ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature }
  (TCancel p1 refl refl refl)
  rewrite v=v inputVal | <to<ᵇ p1 = refl


-}






----------------------------------------------------------

--Leftover code from previous attempts
{-                             

transitionImpliesValidator par (Collecting v pkh d sigs) .Pay
  record { inputVal = .(outputVal + v) ; outputVal = outputVal ; outputLabel = .Holding ; time = time ; payTo = .pkh ; payAmt = .v ; signature = signature }
  (TPay refl p2 refl refl refl refl)
 
transitionImpliesValidator par (Collecting v pkh d sigs) .Cancel
  record { inputVal = inputVal ; outputVal = inputVal ; outputLabel = .Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature }
  (TCancel p1 refl refl refl)
  

-}


--uil (x ∷ sigs) n (x₁ :: pf1) (s≤s pf2) = {!!}

{-
uil' : ∀ (sigs sigs' : List PubKeyHash) (n : Nat) (pf1 : Unique sigs ) (pf2 : IsTrue (lengthNat sigs > n))
                      -> (n < lengthNat (makeSigs' sigs' sigs)) ≡ True
uil' s1 s2 n pf1 pf2 = trustMe
--- assumed



lengthLemma : ∀ (par : Params) (sigs : List PubKeyHash) -> 
      (nr par < lengthNat (makeSigs' sigs (authSigs par))) ≡ True
lengthLemma record { authSigs = (x ∷ authSigs) ; nr = zero ; pfU = pfU ; pfL = pfL } sigs = insertLemma x (makeSigs' sigs authSigs)
lengthLemma record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = pfU ; pfL = pfL } sigs = uil' (x ∷ authSigs) sigs (suc nr) pfU pfL 


parLemma : ∀ (par : Params) (sigs : List PubKeyHash) ->
         ( ((nr par < lengthNat (makeSigs' sigs (authSigs par))) ||
         (lengthNat (makeSigs' sigs (authSigs par)) == nr par)) )  ≡  ( (True))
parLemma par sigs rewrite lengthLemma par sigs = refl

rewriteLemma : ∀ (par : Params) (sigs : List PubKeyHash) -> IsTrue
       ((nr par < lengthNat (makeSigs' sigs (authSigs par))) ||
       (lengthNat (makeSigs' sigs (authSigs par)) == nr par))
rewriteLemma par sigs rewrite parLemma par sigs = IsTrue.itsTrue

{-
insertLemma : ∀ (sig : PubKeyHash) (sigs : List PubKeyHash) -> sig ∉ sigs -> insert sig sigs ≡ sigs ++ [ sig ]
insertLemma sig [] pf = refl
insertLemma sig (x ∷ sigs) pf = {!!}


insertLemma : ∀ (sig : PubKeyHash) (sigs : List PubKeyHash) -> sig ∉ sigs ->
            insert sig (foldl (λ y x → x ∷ y) [] sigs) ≡ foldl (λ y x → x ∷ y) (sig ∷ []) sigs
insertLemma sig [] pf = refl
insertLemma sig (x ∷ sigs) pf rewrite (sym (insertLemma x sigs {!!}))= {!!}

msLemma : ∀ (sigs : List PubKeyHash) -> Unique sigs -> makeSigs' [] sigs ≡ reverse sigs
msLemma [] pf = refl
msLemma (x ∷ sigs) (p :: pf) = {!!} --rewrite msLemma sigs pf = {!!}

msLemma' : ∀ (sigs : List PubKeyHash) -> Unique sigs -> makeSigs [] sigs ≡ sigs
msLemma' [] pf = refl
msLemma' (x ∷ sigs) (p :: pf) = {!!}

appendEmpty : ∀ (a : List PubKeyHash) -> a ++ [] ≡ a
appendEmpty [] = refl
appendEmpty (x ∷ a) = cong (λ y -> x ∷ y) (appendEmpty a)

reverseDistrib : ∀ (a b : List PubKeyHash) -> reverse (a ++ b) ≡ reverse b ++ reverse a
reverseDistrib a [] rewrite appendEmpty a = refl
reverseDistrib a (x ∷ b) = {!!}

reverseLemma : ∀ (sig : PubKeyHash) (sigs : List PubKeyHash) -> reverse (sig ∷ sigs) ≡ (reverse sigs) ++ [ sig ]
reverseLemma sig [] = refl
reverseLemma sig (x ∷ sigs) = {!!}
-}

{-
prop1' : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par) -> asigs ≡ (asigs' ++ asigs'')
         -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Collecting v pkh d (makeSigs sigs asigs'')
         -> outVal s ≡ outVal s' -> outAdr s ≡ outAdr s' -> now s ≡ now s' -> tsig s' ≡ nextSig s (makeIs asigs'')
         -> value s ≡ value s' -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop1' {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }
  record { label = .(Collecting v pkh d (makeSigs sigs [])) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = .outAdr₁ ; now = .now₁ ;
  tsig = .(nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs [])) }
  record { authSigs = .(sigs2 ++ []) ; nr = nr₁ } .(sigs2 ++ []) sigs2 [] refl refl refl refl refl refl refl refl refl = root
prop1' {v} {pkh} {d} {sigs} record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ } record { label = .(Collecting v pkh d (makeSigs sigs (x ∷ sigs3))) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = .outAdr₁ ; now = .now₁ ; tsig = .(nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs (x ∷ sigs3))) } record { authSigs = .(sigs2 ++ x ∷ sigs3) ; nr = nr₁ } .(sigs2 ++ x ∷ sigs3) sigs2 (x ∷ sigs3) refl refl refl refl refl refl refl refl refl = cons (TAdd {s' = (record { label = Collecting v pkh d (insert x sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = x })} (∈lemma sigs2 sigs3 x) refl refl refl refl) (prop1' (record { label = Collecting v pkh d (insert x sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = x }) (record { label = (Collecting v pkh d (makeSigs sigs (x ∷ sigs3))) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = (nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs (x ∷ sigs3))) }) (record { authSigs = (sigs2 ++ x ∷ sigs3) ; nr = nr₁ }) (sigs2 ++ x ∷ sigs3) (sigs2 ++ [ x ]) sigs3 refl (appendLemma x sigs2 sigs3) refl refl refl refl refl {!!} refl)

-}
{-{v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = .outAdr₁ ; now = now₁ ; tsig = tsig₁ }
  record { label = .(Collecting _ _ _ (makeSigs _ [])) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = outAdr₁ ; now = .now₁ ;
  tsig = .(nextSig (record { label = (Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (makeIs [])) }
  record { authSigs = .(s1 ++ []) ; nr = nr₁ } .(s1 ++ []) s1 [] refl refl refl refl refl refl refl refl refl = root

prop1' {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = .outAdr₁ ; now = now₁ ; tsig = tsig₁ }
  record { label = .(Collecting _ _ _ (makeSigs sigs (x ∷ s2))) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = outAdr₁ ; now = .now₁ ;
  tsig = .(nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (makeIs' (x ∷ s2))) }
  record { authSigs = .(s1 ++ x ∷ s2) ; nr = nr₁ } .(s1 ++ x ∷ s2) s1 (x ∷ s2)
  refl refl refl refl refl refl refl refl refl = {!!} -}
  {-
  snoc (prop1' (record { label = (Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (record { label = (Collecting v pkh d (makeSigs' sigs s2)) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = (nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (makeIs' (s2)))})
  (record { authSigs = (s1 ++ x ∷ s2) ; nr = nr₁ }) (s1 ++ x ∷ s2) (s1 ++ [ x ]) s2 refl (appendLemma x s1 s2) refl refl refl refl refl refl refl)
  (TAdd (∈lemma s1 s2 x) refl refl refl refl) -}


liquidity : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> Valid s -> value s > 0 -> Unique (authSigs par) -> length (authSigs par) ≥ nr par
          -> ∃[ s' ] ∃[ is ] (par ⊢ s ~[ Pay ∷ is ]~* s')
liquidity par record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } pkh d (Hol x) p1 p2 p3
  = ⟨ (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig }) , ⟨ (makeIs' (authSigs par) ++ ((Propose value pkh d) ∷ [])) ,
  lemmaMultiStep par (record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  (((Propose value pkh d) ∷ [])) ( Pay ∷ makeIs' (authSigs par))
  (snoc root (TPropose (v≤v value) p1 refl refl refl))
  (prop2 (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  par (Col refl (v≤v value) p1) refl refl refl refl refl p2 p3) ⟩ ⟩
liquidity par record { label = (Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } _ _ (Col refl p2 p3) p4 p5 p6
  = ⟨ record { label = Holding ; value = (value ∸ v) ; outVal = v ; outAdr = pkh ; now = now ; tsig = tsig } , ⟨ makeIs' (authSigs par) ,
  prop2 (record { label = (Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = (value ∸ v) ; outVal = v ; outAdr = pkh ; now = now ; tsig = tsig }) par (Col refl p2 p3)
  refl refl refl refl (monusLemma value v p2) p5 p6 ⟩ ⟩ 

liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> Valid s -> value s > 0 -> Unique (authSigs par) -> length (authSigs par) ≥ nr par
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ 0) )
          
liquidity' par record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } pkh d (Hol x) p1 p2 p3
  = ⟨ (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig }) ,
  ⟨ (Pay ∷ makeIs' (authSigs par)) ++ ((Propose value pkh d) ∷ []) ,
  ⟨ lemmaMultiStep par (record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  (((Propose value pkh d) ∷ [])) ( Pay ∷ makeIs' (authSigs par))
  (snoc root (TPropose (v≤v value) p1 refl refl refl))
  (prop2 (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  par (Col refl (v≤v value) p1) refl refl refl refl refl p2 p3) , refl ⟩ ⟩ ⟩
  
liquidity' par record { label = (Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } _ _ (Col refl p2 p3) p4 p5 p6
  = ⟨ ((record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })) ,
  ⟨ ((Pay ∷ makeIs' (authSigs par)) ++ [ Propose value pkh d ]) ++ [ Cancel ] ,
  ⟨ lemmaMultiStep par (record { label = (Collecting v pkh d sigs) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = suc d ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  [ Cancel ] ((Pay ∷ makeIs' (authSigs par)) ++ [ Propose value pkh d ] ) (snoc root (TCancel (s≤s (v≤v d)) refl refl refl))
  (lemmaMultiStep par (record { label = Holding ; value = value ; outVal = outVal ; outAdr = outAdr ; now = suc d ; tsig = tsig })
  (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  (((Propose value pkh d) ∷ [])) ( Pay ∷ makeIs' (authSigs par))
  (snoc root (TPropose (v≤v value) p4 refl refl refl))
  (prop2 (record { label = (Collecting value pkh d []) ; value = value ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig })
  (record { label = Holding ; value = 0 ; outVal = value ; outAdr = pkh ; now = now ; tsig = tsig })
  par (Col refl (v≤v value) p4) refl refl refl refl refl p5 p6)) , refl ⟩ ⟩ ⟩

-}





{-
lem : (l1 l2 : List PubKeyHash) (x : PubKeyHash) -> x ∈ l1 -> x ∈ makeSigs l1 l2
lem l1 [] x pf = pf
lem l1 (y ∷ l2) x pf = lem (insert y l1) l2 x (insert-lem3 x y l1 pf)

sublem₁ : (l₁ l₂ : List PubKeyHash)(x : PubKeyHash) → l₁ ⊆ makeSigs l₁ l₂
  → l₁ ⊆ makeSigs (insert x l₁) l₂
sublem₁ [] l2 x [] = []
sublem₁ (y ∷ l1) l2 x (px ∷ pf) with x == y in eq
...| false = lem (y ∷ insert x l1) l2 y (here refl) ∷ {!!}
...| true rewrite ==ito≡ x y eq = px ∷ pf

makeSigs-lem₁ : (l₁ l₂ : List PubKeyHash) → l₁ ⊆ makeSigs l₁ l₂
makeSigs-lem₁ l₁ [] = ⊆-refl l₁
makeSigs-lem₁ l₁ (x₁ ∷ l₂) = {! !} 
--with makeSigs-lem₁ l₁ l₂ ...| IH = {!!}

--⊆-trans (insertList-lem₁ l₁ l₂) (insert-lem₁ x₁ (insertList l₁ l₂))




makeSigs-lem₂ : (l₁ l₂ : List PubKeyHash) → l₂ ⊆ makeSigs l₁ l₂
makeSigs-lem₂ l₁ [] = []
makeSigs-lem₂ l₁ (x₁ ∷ l₂) = {!!} ∷ {!!}
--insert-lem₂ x₁ (insertList l₁ l₂) ∷ ⊆-trans (insertList-lem₂ l₁ l₂) (insert-lem₁  x₁ (insertList l₁ l₂))
-}
{-
insertList : {{eqA : Eq a}} -> List a -> List a -> List a
insertList l1 [] = l1
insertList l1 (x ∷ l2) = insert x (insertList l1 l2)

makeSigs : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs sigs [] = sigs
makeSigs sigs (x ∷ asigs) = (makeSigs (insert x sigs) asigs)

insertList-lem₁ : {{eqA : Eq a}} → (l₁ l₂ : List a) → l₁ ⊆ insertList l₁ l₂
insertList-lem₁ ⦃ eqA = eqA ⦄ l₁ [] = ⊆-refl l₁
insertList-lem₁ ⦃ eqA = eqA ⦄ l₁ (x₁ ∷ l₂) 
  = ⊆-trans (insertList-lem₁ l₁ l₂) (insert-lem₁ x₁ (insertList l₁ l₂))

insertList-lem₂ : {{eqA : Eq a}} → (l₁ l₂ : List a) → l₂ ⊆ insertList l₁ l₂
insertList-lem₂ ⦃ eqA = eqA ⦄ l₁ [] = []
insertList-lem₂ ⦃ eqA = eqA ⦄ l₁ (x₁ ∷ l₂) 
  = insert-lem₂ x₁ (insertList l₁ l₂) ∷ ⊆-trans (insertList-lem₂ l₁ l₂) (insert-lem₁  x₁ (insertList l₁ l₂))

del : ∀{x} (l : List a) → x ∈ l → List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) → suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong suc (length-del p) 

∈-del : ∀{x y}{l₂ : List a} (p : x ∈ l₂) → x ≢ y →  y ∈  l₂ → y ∈ del l₂ p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l₁ l₂ : List a} (p : x ∈ l₂) → (x ∉ l₁) → l₁ ⊆ l₂ → l₁ ⊆ del l₂ p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e → n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {{eqA : Eq a}}{l₁ l₂ : List a} → l₁ ⊆ l₂ → Unique l₁ → length l₂ ≥ length l₁
unique-lem [] root = z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = s≤s (unique-lem (subset-del px x sub) un)

uil :  {{eqA : Eq a}} -> ∀ (l1 l2 : List a) (pf : Unique l2) -> (length (insertList l1 l2) ≥ length l2)
uil l1 l2 pf = unique-lem (insertList-lem₂ l1 l2) pf




aux : ∀ (x : Int) (l : List Int) -> (x == x && l == l) ≡ false -> ⊥
aux x l rewrite i=i x | l=l l = λ ()

=/=lto≢ : ∀ (a b : List PubKeyHash) -> (a == b) ≡ false -> a ≢ b
=/=lto≢ [] (x ∷ b) pf = λ ()
=/=lto≢ (x ∷ a) [] pf = λ ()
=/=lto≢ (x ∷ a) (y ∷ b) pf = λ {refl → aux x a pf}

-}

{-
insertPreserves∉ : ∀ {x y zs}
  -> x ∉ zs -> (y == x) ≡ false -> x ∉ insert y zs
insertPreserves∉ {zs = []} p1 p2 = λ { (here px) → ⊥-elim (=/=ito≢ p2 (sym px))}
insertPreserves∉ {x} {y} {zs = z ∷ zs} p1 p2 with y == x in eq
...| true = λ z → ⊥-elim (get⊥ p2)
...| false with y == z in eq2
...| true rewrite ==ito≡ y z eq2 = p1 
...| false = λ { (here refl) → p1 (here refl) ;
                 (there t) → p1 (there {!insertPreserves∉!})} --p1 (there {!insertPreserves∉!})

--insertPreserves∉ {!!} eq --λ t → {!!}

--λ z → {!!} --insertPreserves∉ {!!} {!!} {!!}-}


{-liquidity'
  record { authSigs = authSigs ; nr = nr }
  s@(record { label = label ;
              context = record { value = zero ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol p1) (Always p2 p3) pf
  = ⟨ s , ⟨ [] , ⟨ root , refl ⟩ ⟩ ⟩
liquidity' par
  s@(record { label = .Holding ;
              context = record { value = (suc value) ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol refl) (Always p2 p3) pf
  = ⟨ s'' , ⟨ (Propose (suc value) pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TPropose (s≤s (v≤v value)) {!!} refl refl refl {!!} {!!})
    (prop2 s' s'' par (Col refl (s≤s (v≤v value)) (s≤s z≤n) root) refl refl refl refl refl (Always p2 p3) {!!} {!!}) , refl ⟩ ⟩ ⟩
      where
        s'' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = suc value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = tsig } }
        s' = record { label = Collecting (suc value) pkh d [] ;
                       context = record { value = (suc value) ;
                                          outVal = outVal ;
                                          outAdr = outAdr ;
                                          now = now ;
                                          tsig = tsig } } -}

{-
liquidity'
  record { authSigs = authSigs ; nr = nr }
  s@(record { label = label ;
              context = record { value = zero ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig } })
  pkh d (Col p1 p2 p3 p6) (Always p4 p5) pf
  = ⟨ s , ⟨ [] , ⟨ root , refl ⟩ ⟩ ⟩
liquidity' par
  record { label = (Collecting v' pkh' d' sigs') ; context = record { value = (suc value) ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } }
  pkh d (Col refl p2 p3 p6) (Always p4 p5) pf
  = ⟨ s''' , ⟨ Cancel ∷ (Propose (suc value) pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TCancel {s' = s'}
    (s≤s (v≤v d')) refl refl refl {!!} {!!})
    (cons (TPropose (s≤s (v≤v value)) (s≤s {!!}) refl refl refl {!!} {!!})
    (prop2 s'' s''' par (Col refl (s≤s (v≤v value)) {!!} root) refl refl refl refl refl (Always p4 p5) {!!} {!!} {!!})) , refl ⟩ ⟩ ⟩
      where
        s''' = record { label = Holding ;
                       context = record { value = zero ;
                                          outVal = suc value ;
                                          outAdr = pkh ;
                                          now = now ;
                                          tsig = tsig } }
        s' = record { label = Holding ;
                      context = record { value = (suc value) ;
                                         outVal = outVal ;
                                         outAdr = outAdr ;
                                         now = suc d' ;
                                         tsig = tsig } }
        s'' = record { label = Collecting (suc value) pkh d [] ;
                        context = record { value = (suc value) ;
                                           outVal = outVal ;
                                           outAdr = outAdr ;
                                           now = d + 1 ;
                                           tsig = tsig } }

 -}  
