--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import MultiSig

open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Nat
open import Agda.Builtin.Int
open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
open import Data.Product
--open import Data.Maybe

open import Haskell.Prim hiding (⊥ ; All)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)

module MultiSigProofs where


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
    label         : Label --maybe just call it Datum 
    context       : Context
open State

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TPropose : ∀ {v pkh d s s' par} 
    -> value (context s) ≥ v
    -> v > emptyValue
    -> label s ≡ Holding
    -> label s' ≡ Collecting v pkh d []
    -> value (context s) ≡ value (context s') 
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'

  TAdd : ∀ {sig par s s' v pkh d sigs} 
    -> sig ∈ (authSigs par)
    -> tsig (context s') ≡ sig
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Collecting v pkh d (insert sig sigs)
    -> value (context s) ≡ value (context s') --value s ≡ value s' -- outValue s.Context ≡ outValue s'.Context
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'

  TPay : ∀ {v pkh d sigs s s' par} 
    -> value (context s) ≡ value (context s') + v
    -> length sigs ≥ nr par
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding
    -> outVal (context s') ≡ v
    -> outAdr (context s') ≡ pkh 
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par v pkh d sigs} 
    -> now (context s') > d
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding  
    -> value (context s) ≡ value (context s') --value s ≡ value s' 
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'

data Valid : State -> Set where

  Hol : ∀ {s}
    -> label s ≡ Holding
    ----------------
    -> Valid s

  Col : ∀ {s v pkh d sigs}
    -> label s ≡ Collecting v pkh d sigs
    -> value (context s) ≥ v
    -> v > 0
    --------------------------------
    -> Valid s


data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


diffLabels : ∀ {v pkh d sigs} (l : Label) -> l ≡ Holding
           -> l ≡ Collecting v pkh d sigs -> ⊥ 
diffLabels Holding p1 ()
diffLabels (Collecting v pkh d sigs) () p2

sameValue : ∀ {v v' pkh pkh' d d' sigs sigs'}
  -> Collecting v pkh d sigs ≡ Collecting v' pkh' d' sigs' -> v ≡ v'
sameValue refl = refl

validStateTransition : ∀ {s s' : State} {i par}
  -> Valid s
  -> par ⊢ s ~[ i ]~> s'
  -> Valid s'
validStateTransition iv (TPropose p1 p2 p3 p4 p5) rewrite p5 = Col p4 p1 p2
validStateTransition {s} (Hol pf) (TAdd p1 p2 p3 p4 p5) = ⊥-elim (diffLabels (label s) pf p3)
validStateTransition (Col pf1 pf2 pf3) (TAdd p1 p2 p3 p4 p5) rewrite pf1 | sameValue p3 | p5 = Col p4 pf2 pf3
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6) = Hol p4
validStateTransition iv (TCancel p1 p2 p3 p4) = Hol p3

validStateMulti : ∀ {s s' : State} {is par}
  -> Valid s
  -> par ⊢ s ~[ is ]~* s'
  -> Valid s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x 

--do it with normal lists, or define snocLists !!!!





makeIs : List PubKeyHash -> List Input
makeIs [] = []
makeIs (x ∷ pkhs) = Add x ∷ makeIs pkhs


makeSigs : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs sigs [] = sigs
makeSigs sigs (x ∷ asigs) = (makeSigs (insert x sigs) asigs)


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

prop : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par) -> asigs ≡ (asigs' ++ asigs'')
         -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Collecting v pkh d (makeSigs sigs asigs'')
         -> outVal (context s) ≡ outVal (context s') -> outAdr (context s) ≡ outAdr (context s') -> now (context s) ≡ now (context s')
         -> value (context s) ≡ value (context s') -> tsig (context s') ≡ finalSig s (makeIs asigs'')
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'
prop {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
  context = record { value = .value₁ ; outVal = .outVal₁ ; outAdr = .outAdr₁ ; now = .now₁ ; tsig = tsig₁ } }
  record { label = .(Collecting v pkh d (makeSigs sigs [])) ;
  context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = .(finalSig (record { label = Collecting v pkh d sigs ;
  context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ } }) (makeIs [])) } }
  record { authSigs = .(s2 ++ []) ; nr = nr₁ } .(s2 ++ []) s2 [] refl refl refl refl refl refl refl refl refl
  = root
  
prop {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
  context = record { value = .value₁ ; outVal = .outVal₁ ; outAdr = .outAdr₁ ; now = .now₁ ; tsig = tsig₁ } }
  record { label = .(Collecting v pkh d (makeSigs sigs (x ∷ s3))) ;
  context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = .(finalSig (record { label = Collecting v pkh d sigs ;
  context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ } }) (makeIs (x ∷ s3))) } }
  record { authSigs = .(s2 ++ x ∷ s3) ; nr = nr₁ } .(s2 ++ x ∷ s3) s2 (x ∷ s3) refl refl refl refl refl refl refl refl refl
  = cons ((TAdd (∈lemma s2 s3 x) refl refl refl refl))
    (prop (record { label = Collecting v pkh d (insert x sigs) ;
    context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = x }})
    (record { label = (Collecting v pkh d (makeSigs sigs (x ∷ s3))) ;
    context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
    tsig = (finalSig (record { label = Collecting v pkh d sigs ;
    context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ } })
    (makeIs (x ∷ s3))) } })
    (record { authSigs = (s2 ++ x ∷ s3) ; nr = nr₁ })
    (s2 ++ x ∷ s3) (s2 ++ [ x ]) s3 refl (appendLemma x s2 s3) refl refl refl refl refl refl
    (finalSigLemma (record { label = Collecting v pkh d sigs ;
    context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }})
    (record { label = Collecting v pkh d (insert x sigs) ;
    context = record { value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = x }}) x s3 refl ))



prop1 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
        -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Collecting v pkh d (makeSigs sigs (authSigs par))
        -> outVal (context s) ≡ outVal (context s') -> outAdr (context s) ≡ outAdr (context s') -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s') -> tsig (context s') ≡ finalSig s (makeIs (authSigs par))
        -> par ⊢ s ~[ (makeIs (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 = prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7


{- ??
axiom : ∀ (t : Set) (x y : t) {{ eqT : Eq t }} -> (x == y) ≡ true -> x ≡ y
axiom t x y = {!!}

axiom2 : {{eqA : Eq a}} -> ∀ (x y : a) -> (x == y) ≡ false -> ¬ x ≡ y
axiom2 = {!!}

-}


data Unique : List PubKeyHash → Set where
  root : Unique []
  _::_ : {x : PubKeyHash} {l : List PubKeyHash} → x ∉ l → Unique l → Unique (x ∷ l)

_⊆_ : List a → List a → Set
l₁ ⊆ l₂ = All (_∈ l₂) l₁

⊆-cons : (x : a){l₁ l₂ : List a} → l₁ ⊆  l₂ → l₁ ⊆ (x ∷ l₂)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : (l : List a) → l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷  ⊆-cons x (⊆-refl l)

⊆-trans : {l₁ l₂ l₃ : List a} → l₁ ⊆ l₂ → l₂ ⊆ l₃ → l₁ ⊆ l₃
⊆-trans [] p₂ = []
⊆-trans (px ∷ p₁) p₂ = All.lookup p₂ px ∷ ⊆-trans  p₁ p₂

≡ᵇto≡ : ∀ {a b} -> (a ≡ᵇ b) ≡ true -> a ≡ b
≡ᵇto≡ {zero} {zero} pf = refl
≡ᵇto≡ {suc a} {suc b} pf = cong suc (≡ᵇto≡ pf)

≤ᵇto≤ : ∀ {a b} -> (a <ᵇ b || b ≡ᵇ a) ≡ true -> a ≤ b
≤ᵇto≤ {zero} {zero} pf = z≤n
≤ᵇto≤ {zero} {suc b} pf = z≤n
≤ᵇto≤ {suc a} {suc b} pf = s≤s (≤ᵇto≤ pf)
--report this to Oresitis and James

<ᵇto< : ∀ {a b} -> (a <ᵇ b) ≡ true -> a < b
<ᵇto< {zero} {suc b} pf = s≤s z≤n
<ᵇto< {suc a} {suc b} pf = s≤s (<ᵇto< pf)

==ito≡ : ∀ (a b : Int) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong pos (≡ᵇto≡ pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (≡ᵇto≡ pf)

insert-lem₁ : (x : PubKeyHash)(l : List PubKeyHash) → l ⊆ insert x l
insert-lem₁ x [] = []
insert-lem₁ x (y ∷ l) with x == y in eq
... | false = (here refl) ∷ ⊆-cons y (insert-lem₁ x l) 
... | true rewrite (==ito≡ x y eq) = (here refl) ∷ (⊆-cons y (⊆-refl l))


insert-lem₂ : (x : PubKeyHash)(l : List PubKeyHash) → x ∈ insert x l
insert-lem₂ x [] = here refl
insert-lem₂ x (y ∷ l) with x == y in eq
... | false = there (insert-lem₂ x l) 
... | true = here refl


makeSigs-lem₁ : (l₁ l₂ : List PubKeyHash) → l₁ ⊆ makeSigs l₁ l₂
makeSigs-lem₁ l₁ [] = ⊆-refl l₁
makeSigs-lem₁ l₁ (x₁ ∷ l₂) 
  = {!!} --⊆-trans (insertList-lem₁ l₁ l₂) (insert-lem₁ x₁ (insertList l₁ l₂))

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
-}

{-


data Unique : List PubKeyHash → Set where
  [] : Unique []
  _::_ : {x : PubKeyHash} {l : List PubKeyHash} → x ∉ l → Unique l → Unique (x ∷ l)



postulate
  uil' : ∀ (sigs sigs' : List PubKeyHash) (n : ℕ) (pf1 : Unique sigs) (pf2 : (length sigs ≥ n))
                      -> (length (makeSigs' sigs' sigs) ≥ n)


--lists of EQ Stuff, not PubKeyHash (type variable with eq)

--prove it
--look at Fresh lists
--obvious property, if it doens't exists, it should be added to the Library



prop2 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
          -> Valid s
          -> label s ≡ Collecting v pkh d sigs
          -> label s' ≡ Holding
          -> outVal s' ≡ v
          -> outAdr s' ≡ pkh
          -> value s ≡ value s' + v
          -> Unique (authSigs par)
          -> length (authSigs par) ≥ nr par
          --collapse into Valid par
          -> par ⊢ s ~[ (Pay ∷ (makeIs' (authSigs par))) ]~* s'
prop2 {d = d} {sigs = sigs} (record { label = .(Collecting outVal₂ outAdr₂ d sigs) ; value = .(value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  record { label = .Holding ; value = value₁ ; outVal = outVal₂ ; outAdr = outAdr₂ ; now = now₂ ; tsig = tsig₂ } par (Col refl p2 p3) refl refl refl refl refl p4 p5
  = snoc (prop1 (record { label = (Collecting outVal₂ outAdr₂ d sigs) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (record { label = (Collecting outVal₂ outAdr₂ d (makeSigs' sigs (authSigs par))) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = nextSig (record { label = (Collecting outVal₂ outAdr₂ d sigs) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (makeIs' (authSigs par)) }) par refl refl refl refl refl refl refl) (TPay refl (uil' (authSigs par) sigs (nr par) p4 p5) refl refl refl refl)


lemmaMultiStep : ∀ (par : Params) (s s' s'' : State) (is is' : List Input)
                   -> par ⊢ s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is' ++ is ]~* s''
lemmaMultiStep par s s' .s' is [] p1 root = p1
lemmaMultiStep par s s' s'' is (x ∷ is') p1 (snoc {s' = s'''} p2 p3) = snoc (lemmaMultiStep par s s' s''' is is' p1 p2) p3

+0 : ∀ (v : Value) -> v ≡ v + zero
+0 zero = refl
+0 (suc v) = cong suc (+0 v)

+suc : ∀ (a b : Value) -> a + suc b ≡ suc (a + b)
+suc zero b = refl
+suc (suc a) b = cong suc (+suc a b)

monusLemma : ∀ (a b : Value) -> a ≥ b -> a ≡ a ∸ b + b
monusLemma zero zero z≤n = refl
monusLemma zero (suc b) ()
monusLemma (suc a) zero z≤n = cong suc (+0 a)
monusLemma (suc a) (suc b) (s≤s pf) rewrite +suc (a ∸ b) b = cong suc (monusLemma a b pf)

v≤v : ∀ (v : Value) -> v ≤ v
v≤v zero = z≤n
v≤v (suc v) = s≤s (v≤v v)


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



≡ᵇto≡ : ∀ {a b} -> (a ≡ᵇ b) ≡ true -> a ≡ b
≡ᵇto≡ {zero} {zero} pf = refl
≡ᵇto≡ {suc a} {suc b} pf = cong suc (≡ᵇto≡ pf)

≤ᵇto≤ : ∀ {a b} -> (a <ᵇ b || b ≡ᵇ a) ≡ true -> a ≤ b
≤ᵇto≤ {zero} {zero} pf = z≤n
≤ᵇto≤ {zero} {suc b} pf = z≤n
≤ᵇto≤ {suc a} {suc b} pf = s≤s (≤ᵇto≤ pf)
--report this to Oresitis and James

<ᵇto< : ∀ {a b} -> (a <ᵇ b) ≡ true -> a < b
<ᵇto< {zero} {suc b} pf = s≤s z≤n
<ᵇto< {suc a} {suc b} pf = s≤s (<ᵇto< pf)

==ito≡ : ∀ (a b : Int) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong pos (≡ᵇto≡ pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (≡ᵇto≡ pf)


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

p2 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && (x <ᵇ y || y ≡ᵇ x) && b && c && d && e && f) ≡ true -> x ≤ y
p2 a b c d e f x y pf = ≤ᵇto≤ ( get ((x <ᵇ y || y ≡ᵇ x)) (go a pf) )

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

lengthNatToLength : ∀ (n : ℕ) (l : List PubKeyHash) -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true -> n ≤ length l
lengthNatToLength zero [] pf = z≤n
lengthNatToLength zero (x ∷ l) pf = z≤n
lengthNatToLength (suc n) (x ∷ l) pf = s≤s (lengthNatToLength n l pf)

y1 : ∀ (a b c : Bool) (n : ℕ) (sigs : List PubKeyHash) -> ((n <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ n) && (a && b) && c) ≡ true -> n ≤ length sigs
y1 a b c n sigs pf = lengthNatToLength n sigs (get (n <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ n) pf)

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

--get rid of state? Datum and ScriptContext

--s -i-> s'

--ctx ⊢ dat -i-> (dat' ≡ outpuDatum ctx)

--prove that label = outputLabel ctx ?
--can we get a better solution where state = label (under our control) and stuff controlled by blockchain?
validatorImpliesTransition : ∀ {oV oA t s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; value = (inputVal ctx) ; outVal = oV ; outAdr = oA ; now = t ; tsig = s }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; value = (outputVal ctx) ; outVal = payAmt ctx
                           ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx }

validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) ( (v <ᵇ inputVal || inputVal ≡ᵇ v)) (0 <ᵇ v) pf)
validatorImpliesTransition par Holding (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting v' pkh' d' sigs) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
   rewrite p1 (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs == []) outputVal inputVal pf
   | sym (p4 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (pkh == pkh') (d ≡ᵇ d') (sigs == []) v v' pf)
   | p5 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (d ≡ᵇ d') (sigs == []) pkh pkh' pf
   | p6 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (sigs == []) d d' pf
   | p7 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs [] pf
   = TPropose (p2 (outputVal ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs == []) v inputVal pf)
     (p3 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs == []) 0 v pf) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) pf)
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting v' pkh' d' sigs') ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf 
  rewrite p1 (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) outputVal inputVal pf
  | sym (p4 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) v v' pf)
  | p5 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (d ≡ᵇ d') (sigs' == (insert sig sigs)) pkh pkh' pf
  | p6 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (sigs' == (insert sig sigs)) d d' pf
  | p7 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs' (insert sig sigs) pf
  = TAdd (a3 (outputVal ≡ᵇ inputVal) (sig == signature) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig (authSigs par) pf)
  (sym (a2 (outputVal ≡ᵇ inputVal) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig signature pf)) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = TPay (y4 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (pkh == payTo) (v ≡ᵇ payAmt) inputVal (outputVal + v) pf)
  (y1 (eqInteger pkh payTo) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) (nr par) sigs pf) refl refl
  (sym (y3 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (pkh == payTo) (inputVal ≡ᵇ outputVal + v) v payAmt pf))
  (sym (y2 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) pkh payTo pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting x x₁ x₂ x₃) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = ⊥-elim (&&false ((nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par)) pf) 
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = TCancel (c2 (outputVal ≡ᵇ inputVal) d time pf) refl refl (sym (c1 (d <ᵇ time) outputVal inputVal pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting x x₁ x₂ x₃) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = ⊥-elim (&&false (outputVal ≡ᵇ inputVal) pf)

≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a ≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl

≤to≤ᵇ : ∀ {a b} -> a ≤ b -> (a <ᵇ b || b ≡ᵇ a) ≡ true
≤to≤ᵇ {b = zero} z≤n = refl
≤to≤ᵇ {b = suc b} z≤n = refl
≤to≤ᵇ (s≤s pf) = ≤to≤ᵇ pf
--report this to Orestis and James

<to<ᵇ : ∀ {a b} -> a < b -> (a <ᵇ b) ≡ true
<to<ᵇ {zero} (s≤s pf) = refl
<to<ᵇ {suc a} (s≤s pf) = <to<ᵇ pf


v=v : ∀ (v : Value) -> (v ≡ᵇ v) ≡ true
v=v zero = refl
v=v (suc v) = v=v v

i=i : ∀ (i : Int) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = i=i (pos n)
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = i=i (pos n)

||true : ∀ {b} -> (b || true) ≡ true
||true {false} = refl
||true {true} = refl

∈toQuery : ∀ {sig sigs} -> sig ∈ sigs -> (query sig sigs) ≡ true
∈toQuery {sig} (here refl) rewrite i=i sig = refl
∈toQuery (there pf) rewrite ∈toQuery pf = ||true


l=l : ∀ (l : List PubKeyHash) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite i=i x = l=l l 

lengthToLengthNat : ∀ (n : ℕ) (l : List PubKeyHash) -> n ≤ length l -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true
lengthToLengthNat zero [] z≤n = refl
lengthToLengthNat zero (x ∷ l) z≤n = refl
lengthToLengthNat (suc n) (x ∷ l) (s≤s pf) = lengthToLengthNat n l pf

transitionImpliesValidator : ∀ {oV oA t s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : par ⊢
                           (record { label = l ; value = (inputVal ctx) ; outVal = oV ; outAdr = oA ; now = t ; tsig = s })
                           ~[ i ]~>
                           (record { label = (outputLabel ctx) ; value = (outputVal ctx) ; outVal = payAmt ctx
                           ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx }) )
                           -> agdaValidator par l i ctx ≡ true
                             
transitionImpliesValidator par Holding (Propose v pkh d)
  record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = .(Collecting _ _ _ []) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature }
  (TPropose p1 p2 p3 refl p5) 
  rewrite ≡to≡ᵇ (sym p5) | ≤to≤ᵇ p1 | <to<ᵇ p2 | v=v v | i=i pkh | v=v d = refl 
transitionImpliesValidator par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ; outputVal = inputVal ; outputLabel = .(Collecting v pkh d (insert sig sigs)) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = .sig }
  (TAdd p1 refl refl refl refl)
  rewrite v=v inputVal | i=i sig | ∈toQuery p1 | v=v v | i=i pkh | v=v d | l=l (insert sig sigs) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) .Pay
  record { inputVal = .(outputVal + v) ; outputVal = outputVal ; outputLabel = .Holding ; time = time ; payTo = .pkh ; payAmt = .v ; signature = signature }
  (TPay refl p2 refl refl refl refl)
  rewrite i=i pkh | v=v v | lengthToLengthNat (nr par) sigs p2 | v=v (outputVal + v) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) .Cancel
  record { inputVal = inputVal ; outputVal = inputVal ; outputLabel = .Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature }
  (TCancel p1 refl refl refl)
  rewrite v=v inputVal | <to<ᵇ p1 = refl



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

-}





