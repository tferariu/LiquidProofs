--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import MultiSig

open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Nat
--open import Agda.Builtin.Nat using (_-_)
open import Agda.Builtin.Int
--open import Data.Integer.Base
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
--open import Relation.Nullary.Negation

--open import Data.List.Membership.Setoid

--open import Data.Sum

--open import Haskell.Prelude
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)

module MultiSigProofs where


asdf : ∀ (v : Value) -> geq v v ≡ true
asdf zero = refl
asdf (suc v) = asdf v

-- TO DO:
-- complete spec
-- rewrite spec ∧ proofs in Agda only + add lemmas relating Haskell to Agda

record State : Set where
  field
    label         : Label
    value         : Value
    outVal        : Value
    outAdr        : PubKeyHash
    now           : Deadline
    tsig          : PubKeyHash
open State

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where

  
  TPropose : ∀ {v pkh d s s' par} --val par outV outA time sig outV' outA' time' sig'}
    -> value s ≥ v
    -> v > emptyValue
    -> label s ≡ Holding
    -> label s' ≡ Collecting v pkh d []
    -> value s ≡ value s'
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'

{-
    -> par ⊢ record { label = Holding ; value = val ; outVal = outV ; outAdr = outA ; now = time ; tsig = sig }
       ~[ (Propose v pkh d) ]~>
       record { label = Collecting v pkh d [] ; value = val ; outVal = outV' ; outAdr = outA' ; now = time' ; tsig = sig' }
-}

  TAdd : ∀ {sig par s s' v pkh d sigs} --{v pkh d sig sigs val par outV outD time sig' outV' outD' time' sig''}
    -> sig ∈ (authSigs par)
    -> tsig s' ≡ sig
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Collecting v pkh d (insert sig sigs)
    -> value s ≡ value s'
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'


{-
    -> par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
       ~[ (Add sig) ]~>
       record { label = (Collecting v pkh d (insert sig sigs)) ; value = val }
 -}      
--mem in haskell, but is is in Plutus?
--agda sets for proofs, lists for implementation

  TPay : ∀ {v pkh d sigs s s' par} -- {v pkh d sigs val val' par outV outD now tsig}
    -> value s ≡ value s' + v
    -> length sigs ≥ nr par
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding
    -> outVal s' ≡ v
    -> outAdr s' ≡ pkh
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'
{-
    -> par ⊢ record { label = Collecting v pkh d sigs ; value = val }
       ~[ Pay ]~>
       record { label = Holding ; value = val' }
       -}

  TCancel : ∀ {s s' par v pkh d sigs} -- {v pkh d sigs val par outV outD now tsig}
    -> now s' > d
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding  
    -> value s ≡ value s'
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'

{-
    -> par ⊢ record { label = Collecting v pkh d sigs ; value = val }
       ~[ Cancel ]~>
       record { label = Holding ; value = val}
-}
-- UNPLEASANT TO READ, MAKE BETTER
-- proof only side, so use Agda symbols to write nicely
-- elegance, easy to read while also minimizing lemma amounts

data Valid : State -> Set where

  Hol : ∀ {s}
    -> label s ≡ Holding
    ----------------
    -> Valid s

  Col : ∀ {s v pkh d sigs}
    -> label s ≡ Collecting v pkh d sigs
    -> value s ≥ v
    -> v > 0
    --------------------------------
    -> Valid s
    
data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  snoc : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ is ]~* s'
    -> par ⊢ s' ~[ i ]~> s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''

{-
  cons : ∀ { s s' i is s'' par }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -----------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''
-}


makeIs' : List PubKeyHash -> List Input
makeIs' [] = []
makeIs' (x ∷ pkhs) = Add x ∷ makeIs' pkhs

makeSigs' : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs' sigs [] = sigs
makeSigs' sigs (x ∷ asigs) = insert x (makeSigs' sigs asigs)

makeSigs : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs sigs [] = sigs
makeSigs sigs (x ∷ asigs) = (makeSigs (insert x sigs) asigs)

--queryLemma : ∀ (x : PubKeyHash) (y z : List PubKeyHash) -> IsTrue (query x (y ++ x ∷ z))
--queryLemma x [] z = why x
--queryLemma x (y ∷ ys) z = why' (eqInteger y x) x ys z (queryLemma x ys z)

appendLemma : ∀ (x : PubKeyHash) (a b : List PubKeyHash) -> a ++ x ∷ b ≡ (a ++ x ∷ []) ++ b
appendLemma x [] b = refl
appendLemma x (a ∷ as) b = cong (λ y → a ∷ y) (appendLemma x as b) 

∈lemma : ∀ (xs ys : List PubKeyHash) (z : PubKeyHash) -> z ∈ (xs ++ z ∷ ys)
∈lemma [] ys z = here refl
∈lemma (x ∷ xs) ys z = there (∈lemma xs ys z)

nextSig : ∀ (s : State) -> (ls : List Input) -> PubKeyHash
nextSig s [] = tsig s
nextSig s (Propose x x₁ x₂ ∷ ls) = tsig s
nextSig s (Add sig ∷ ls) = sig
nextSig s (Pay ∷ ls) = tsig s
nextSig s (Cancel ∷ ls) = tsig s

prop1' : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par) -> asigs ≡ (asigs' ++ asigs'')
         -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Collecting v pkh d (makeSigs' sigs asigs'')
         -> outVal s ≡ outVal s' -> outAdr s ≡ outAdr s' -> now s ≡ now s' -> tsig s' ≡ nextSig s (makeIs' asigs'')
         -> value s ≡ value s' -> par ⊢ s ~[ makeIs' asigs'' ]~* s'
 {-        
         ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
         ~[ makeIs' asigs'' ]~*
         record { label = (Collecting v pkh d (makeSigs' sigs asigs'')) ; value = val }) -}
prop1' {v} {pkh} {d} {sigs} record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = .outAdr₁ ; now = now₁ ; tsig = tsig₁ } record { label = .(Collecting _ _ _ (makeSigs' _ [])) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = outAdr₁ ; now = .now₁ ; tsig = .(nextSig (record { label = (Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs' [])) } record { authSigs = .(s1 ++ []) ; nr = nr₁ } .(s1 ++ []) s1 [] refl refl refl refl refl refl refl refl refl = root

prop1' {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = .outAdr₁ ; now = now₁ ; tsig = tsig₁ }
  record { label = .(Collecting _ _ _ (makeSigs' _ (x ∷ s2))) ; value = .value₁ ; outVal = .outVal₁ ; outAdr = outAdr₁ ; now = .now₁ ;
  tsig = .(nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs' (x ∷ s2))) }
  record { authSigs = .(s1 ++ x ∷ s2) ; nr = nr₁ } .(s1 ++ x ∷ s2) s1 (x ∷ s2)
  refl refl refl refl refl refl refl refl refl =
  snoc (prop1' (record { label = (Collecting v pkh d sigs) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (record { label = (Collecting v pkh d (makeSigs' sigs s2)) ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = (nextSig (record { label = Collecting v pkh d sigs ; value = value₁ ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ }) (makeIs' (s2)))})
  (record { authSigs = (s1 ++ x ∷ s2) ; nr = nr₁ }) (s1 ++ x ∷ s2) (s1 ++ [ x ]) s2 refl (appendLemma x s1 s2) refl refl refl refl refl refl refl)
  (TAdd (∈lemma s1 s2 x) refl refl refl refl)



prop1 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
        -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Collecting v pkh d (makeSigs' sigs (authSigs par))
        -> outVal s ≡ outVal s' -> outAdr s ≡ outAdr s' -> now s ≡ now s' -> tsig s' ≡ nextSig s (makeIs' (authSigs par))
        -> value s ≡ value s' -> par ⊢ s ~[ (makeIs' (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 = prop1' s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7


  

data Unique : List PubKeyHash → Set where
  [] : Unique []
  _::_ : {x : PubKeyHash} {l : List PubKeyHash} → x ∉ l → Unique l → Unique (x ∷ l)

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
postulate
  uil : ∀ (sigs : List PubKeyHash) (n : ℕ) (pf1 : Unique sigs) (pf2 : length sigs > n)
                      -> (n < length (makeSigs' [] sigs))

  uil' : ∀ (sigs sigs' : List PubKeyHash) (n : ℕ) (pf1 : Unique sigs) (pf2 : (length sigs ≥ n))
                      -> (length (makeSigs' sigs' sigs) ≥ n)
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
-}


prop2 : ∀ { v pkh d sigs } (s s' : State) (par : Params) -> Valid s
          -> label s ≡ Collecting v pkh d sigs -> label s' ≡ Holding
          -> outVal s' ≡ v -> outAdr s' ≡ pkh -> value s ≡ value s' + v
          -> Unique (authSigs par) -> length (authSigs par) ≥ nr par 
          -> par ⊢ s ~[ (Pay ∷ (makeIs' (authSigs par))) ]~* s'
prop2 {d = d} {sigs = sigs} (record { label = .(Collecting outVal₂ outAdr₂ d sigs) ; value = .(value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  record { label = .Holding ; value = value₁ ; outVal = outVal₂ ; outAdr = outAdr₂ ; now = now₂ ; tsig = tsig₂ } par (Col refl p2 p3) refl refl refl refl refl p4 p5
  = snoc (prop1 (record { label = (Collecting outVal₂ outAdr₂ d sigs) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (record { label = (Collecting outVal₂ outAdr₂ d (makeSigs' sigs (authSigs par))) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ;
  tsig = nextSig (record { label = (Collecting outVal₂ outAdr₂ d sigs) ; value = (value₁ + outVal₂) ; outVal = outVal₁ ; outAdr = outAdr₁ ; now = now₁ ; tsig = tsig₁ })
  (makeIs' (authSigs par)) }) par refl refl refl refl refl refl refl) (TPay refl (uil' (authSigs par) sigs (nr par) p4 p5) refl refl refl refl)

--snoc (prop1 {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}) (TPay {!!} {!!} {!!} {!!} {!!} {!!})


--prop2 {v} {val} {sigs = sigs} par (Col p1 p2) with ((parLemma par sigs))
--...| x rewrite x = snoc (prop1 par) (TPay ((lemma+- val v (lemmaLE v val p1))) (rewriteLemma par sigs))

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

{-
liquidity par record { label = Holding ; value = val } pkh d pf pf' =
          ⟨ record { label = Holding ; value = (val - val) {{lemmaLT val}} } , ⟨ makeIs' (authSigs par) ++ ((Propose val pkh d) ∷ []) ,
          lemmaMultiStep par (record { label = Holding ; value = val })
          (record { label = (Collecting val pkh d []) ; value = val })
          (record { label = Holding ; value = (val - val) {{lemmaLT val}} })
          (((Propose val pkh d) ∷ []))
          ( Pay ∷ makeIs' (authSigs par))
          (snoc root (TPropose (whyy (Integer.pos val)) pf')) (prop2 par (Col (whyy (Integer.pos val)) pf')) ⟩ ⟩
liquidity par record { label = (Collecting v pkh d sigs) ; value = val } _ _ pf _ = ⟨ record { label = Holding ; value = (val - v) {{lemmaOK pf}}  } , ⟨ makeIs' (authSigs par) , prop2 par pf ⟩ ⟩
-}

≡ᵇto≡ : ∀ {a b} -> (a ≡ᵇ b) ≡ true -> a ≡ b
≡ᵇto≡ {zero} {zero} pf = refl
≡ᵇto≡ {suc a} {suc b} pf = cong suc (≡ᵇto≡ pf)

3&&false : ∀ (a b c : Bool) -> (a && b && c && false) ≡ true -> ⊥
3&&false true true true ()

get : ∀ (a : Bool) {b} -> (a && b) ≡ true -> a ≡ true
get true pf = refl

go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

test : ∀ {a b c d e} ->  (a && b && c && d && e) ≡ true -> true ≡ false
test {a} {b} {c} {d} {e} pf with get c (go b ( go a pf))
...| x = {!!}

get6 : ∀ {a b c d e f} (x y : Deadline) -> (a && b && c && d && e && (x ≡ᵇ y) && f) ≡ true -> x ≡ y
get6 {a} {b} {c} {d} {e} x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) (go e (go d (go c (go b (go a pf))))))

validatorImpliesTransition : ∀ {oV oA t s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; value = (inputVal ctx) ; outVal = oV ; outAdr = oA ; now = t ; tsig = s }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; value = (outputVal ctx) ; outVal = payAmt ctx
                           ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx }

validatorImpliesTransition par Holding (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) ( (v <ᵇ inputVal || inputVal ≡ᵇ v)) (0 <ᵇ v) pf)
validatorImpliesTransition par Holding (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting x x₁ x₂ x₃) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } pf
  rewrite get6 d x₂ pf = TPropose {!!} {!!} refl {!!} {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig) ctx pf = {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) Pay ctx pf = {!!}
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel ctx pf = {!!}

≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a ≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl

≤to≤ᵇ : ∀ {a b} -> a ≤ b -> (a <ᵇ b || b ≡ᵇ a) ≡ true
≤to≤ᵇ {b = zero} z≤n = refl
≤to≤ᵇ {b = suc b} z≤n = refl
≤to≤ᵇ (s≤s pf) = ≤to≤ᵇ pf
--report this to Oresitis and James

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
                           -> agdaValidator par l i ctx ≡ true -- IsTrue instead of ≡ !! be consistent and use only 1
                             
transitionImpliesValidator par Holding (Propose v pkh d) record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = .(Collecting _ _ _ []) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } (TPropose p1 p2 p3 refl p5) 
  rewrite ≡to≡ᵇ (sym p5) | ≤to≤ᵇ p1 | <to<ᵇ p2 | v=v v | i=i pkh | v=v d = refl
transitionImpliesValidator par (Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal ; outputVal = inputVal ; outputLabel = .(Collecting v pkh d (insert sig sigs)) ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = .sig } (TAdd p1 refl refl refl refl)
  rewrite v=v inputVal | i=i sig | ∈toQuery p1 | v=v v | i=i pkh | v=v d | l=l (insert sig sigs) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) .Pay record { inputVal = .(outputVal + v) ; outputVal = outputVal ; outputLabel = .Holding ; time = time ; payTo = .pkh ; payAmt = .v ; signature = signature } (TPay refl p2 refl refl refl refl)
  rewrite i=i pkh | v=v v | lengthToLengthNat (nr par) sigs p2 | v=v (outputVal + v) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) .Cancel record { inputVal = inputVal ; outputVal = inputVal ; outputLabel = .Holding ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature } (TCancel p1 refl refl refl)
  rewrite v=v inputVal | <to<ᵇ p1 = refl



{-
 ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
 record { label = Holding ; value = (val - v) {{lemmaOK x}}  })

why : ∀ (x : PubKeyHash) {b : Bool} -> IsTrue (x == x || b)
why (Integer.pos zero) = IsTrue.itsTrue
why (Integer.pos (suc n)) = why (Integer.pos n)
why (Integer.negsuc zero) = IsTrue.itsTrue
why (Integer.negsuc (suc n)) = why (Integer.pos n)

whyy : ∀ (x : PubKeyHash) {b : Bool} -> IsTrue (b || x == x)
whyy (Integer.pos zero) {False} = IsTrue.itsTrue
whyy (Integer.pos (suc n)) {False} = whyy (Integer.pos n)
whyy (Integer.negsuc zero) {False} = IsTrue.itsTrue
whyy (Integer.negsuc (suc n)) {False} = whyy (Integer.pos n)
whyy x {True} = IsTrue.itsTrue

why' : ∀ (a : Bool) (x : PubKeyHash) (ys z : List PubKeyHash) -> IsTrue (query x (ys ++ x ∷ z)) -> IsTrue (a || query x (ys ++ x ∷ z) )
why' False x ys z pf = pf
why' True x ys z pf = IsTrue.itsTrue

why2 : ∀ (x : PubKeyHash) {b c : Bool} -> IsTrue (c || x == x || b)
why2 (Integer.pos zero) {c = False} = IsTrue.itsTrue
why2 (Integer.pos (suc n)) {c = False} = why (Integer.pos n)
why2 (Integer.negsuc zero) {c = False} = IsTrue.itsTrue
why2 (Integer.negsuc (suc n)) {c = False} = why (Integer.pos n)
why2 x {c = True} = IsTrue.itsTrue

-}



{-

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
        pfU :  (Unique authSigs)
        pfL :  IsTrue ((lengthNat authSigs) > nr)
open Params public

--mark them with @0 for correctness (in front of pfU pfL)
--extra argument instead of having it in Params
--model differently to model initial state being valid


--should be a property of state directly





--talk to Andre Knispel


--"fidelity" actual value ≡ what you think is the value
--fidelity doubly important
--Sophia Drossoupoulou imperial paper



validStateTransition : ∀ {s s' : State} {i par}
  -> label s ∻ value s
  -> par ⊢ s ~[ i ]~> s'
  -> label s' ∻ value s'
validStateTransition iv (TPropose x y) = Col x y
validStateTransition (Col x₁ x₂) (TAdd x) = Col x₁ x₂
validStateTransition iv (TPay x x₁) = Hol
validStateTransition iv TCancel = Hol

validStateMulti : ∀ {s s' : State} {is par}
  -> label s ∻ value s
  -> par ⊢ s ~[ is ]~* s'
  -> label s' ∻ value s'
validStateMulti iv root = iv
validStateMulti iv (snoc tr x) = validStateTransition (validStateMulti iv tr) x
--validStateMulti iv (cons x tr) = validStateMulti (validStateTransition iv x) tr









lemmaLE : ∀ (v val : Value) -> IsTrue ((v < val) || (val == v)) -> IsFalse (val < v)
lemmaLE zero val = λ _ → IsFalse.itsFalse
lemmaLE (suc v) zero = λ ()
lemmaLE (suc v) (suc val) = lemmaLE v val

lemmaOK : ∀ {v val pkh d sigs} -> (Collecting v pkh d sigs) ∻ val -> IsFalse (val < v)
lemmaOK {v} {val} (Col pf1 pf2) = lemmaLE v val pf1

lemmaZero : ∀ (val : Value) -> val ≡ (val + zero)
lemmaZero zero = refl
lemmaZero (suc val) = cong suc (lemmaZero val)

lemmaLEFalse : ∀ (a b : Value) -> IsFalse (a < (suc b)) -> IsFalse (a < b)
lemmaLEFalse (suc a) zero pf = IsFalse.itsFalse
lemmaLEFalse (suc a) (suc b) pf = lemmaLEFalse a b pf

lemmaSucMinus : ∀ (a b c : Value) -> (pff : IsFalse (a < (suc b))) -> suc ( (a - (suc b)) {{pff}} + c ) ≡ ((a - b) {{lemmaLEFalse a b pff}} + c)
lemmaSucMinus (suc a) zero c pff = refl
lemmaSucMinus (suc a) (suc b) c pff = lemmaSucMinus a b c pff

lemmaSucPlus : ∀ (a b : Value) -> a + (suc b) ≡ ((suc a) + b)
lemmaSucPlus zero b = refl
lemmaSucPlus (suc a) b = cong suc (lemmaSucPlus a b)

lemma+- : ∀ (val v : Value) -> (pff : IsFalse (val < v)) -> val ≡ (((val - v) {{pff}}) + v)
lemma+- val zero pf = lemmaZero val
lemma+- val (suc v) pf rewrite (lemmaSucPlus ((val - (suc v)) {{pf}}) v) | (lemmaSucMinus val v v pf) = lemma+- val v (lemmaLEFalse val v pf)


appendEmpty : ∀ (a : List PubKeyHash) -> a ≡ (a ++ [])
appendEmpty [] = refl
appendEmpty (a ∷ as) = cong (λ y → a ∷ y) (appendEmpty as) 


ifLemma : ∀ (x : PubKeyHash) (ys zs : List PubKeyHash) (b : Bool) -> (0 < lengthNat (if b then x ∷ ys else x ∷ zs)) ≡ True
ifLemma x ys zs False = refl
ifLemma x ys zs True = refl

insertLemma : ∀ (x : PubKeyHash) (xs : List PubKeyHash) -> (0 < lengthNat (insert x xs)) ≡ True 
insertLemma x [] = refl
insertLemma x (x' ∷ xs) rewrite ifLemma x' xs (insert x xs) (eqInteger x' x) = refl 

minLength : ∀ (x : PubKeyHash) (ys : List PubKeyHash) -> (zero < lengthNat (insert x ys)) ≡ True
minLength x [] = refl
minLength x (y ∷ ys) rewrite ifLemma y ys (insert x ys) (eqInteger y x) = refl








lemmaLT : ∀ (n : Nat) -> IsFalse (n < n)
lemmaLT zero = IsFalse.itsFalse
lemmaLT (suc n) = lemmaLT n




{-
liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> label s ∻ value s
          -> ∃[ is ] ∃[ v' ] ((par ⊢ s ~[ is ]~* record { label = Holding ; value = v' }) × v' ≡ 0)
liquidity' = {!!}

liquidity' par record { label = Holding ; value = zero } pkh d pf = ⟨ [] , root ⟩
liquidity' par record { label = Holding ; value = (suc val) } pkh d pf =  ⟨ (Pay ∷ makeIs' (authSigs par) ++ ((Propose (suc val) pkh d) ∷ [])) ,
           lemmaMultiStep par ( (record { label = Holding ; value = suc val }))
           ( (record { label = (Collecting (suc val) pkh d []) ; value = suc val })) ( (record { label = Holding ; value = (suc val - suc val) {{lemmaLT val}} }))
           ( (((Propose (suc val) pkh d) ∷ []))) (( Pay ∷ makeIs' (authSigs par))) (snoc root ( (TPropose (whyy (Integer.pos val)) IsTrue.itsTrue)))
           {!prop2!} ⟩
liquidity' par record { label = (Collecting v pkh d sigs) ; value = val } pkh' d' pf = {!!}
-}


v=v : ∀ (v : Value) -> (v == v) ≡ True
v=v zero = refl
v=v (suc v) = v=v v

i=i : ∀ (i : Integer) -> (i == i) ≡ True
i=i (Integer.pos zero) = refl
i=i (Integer.pos (suc n)) = i=i (Integer.pos n)
i=i (Integer.negsuc zero) = refl
i=i (Integer.negsuc (suc n)) = i=i (Integer.pos n)

l=l : ∀ (l : List PubKeyHash) -> (l == l) ≡ True
l=l [] = refl
l=l (x ∷ l) rewrite i=i x = l=l l

refactor : ∀ {b} -> IsTrue b -> b ≡ True
refactor {True} pf = refl

prop= : ∀ (val v : Value) (pkh : PubKeyHash) (d : Deadline) ->
        ((val == val) && (v == v) &&
        eqInteger pkh pkh && eqInteger d d && True) ≡ True
prop= zero zero pkh d rewrite i=i pkh | i=i d = refl
prop= zero (suc v) pkh d = prop= zero v pkh d
prop= (suc val) zero pkh d = prop= val zero pkh d
prop= (suc val) (suc v) pkh d = prop= val v pkh d

contradiction : ∀ {b} -> b ≡ True -> b ≡ False -> ⊥
contradiction {False} () p2
contradiction {True} p1 ()

&&False : ∀ {b} -> (b && False) ≡ False
&&False {False} = refl
&&False {True} = refl

2&&False : ∀ (b1 b2 : Bool) -> (b1 && b2 && False) ≡ False
2&&False False b2 = refl
2&&False True False = refl
2&&False True True = refl

3&&False : ∀ {b1 b2 b3} -> (b1 && b2 && b3 && False) ≡ False
3&&False {False} {b2} {b3} = refl
3&&False {True} {False} {b3} = refl
3&&False {True} {True} {False} = refl
3&&False {True} {True} {True} = refl

6&&False : ∀ {b1 b2 b3 b4 b5 b6} -> (( b1 ) && (b2) && b3 && b4 && b5 && b6 && False ) ≡ False
6&&False {False} {b2} {b3} {b4} {b5} {b6} = refl
6&&False {True} {False} {b3} {b4} {b5} {b6} = refl
6&&False {True} {True} {False} {b4} {b5} {b6} = refl
6&&False {True} {True} {True} {False } {b5} {b6} = refl
6&&False {True} {True} {True} {True} {False} {b6} = refl
6&&False {True} {True} {True} {True} {True} {False} = refl
6&&False {True} {True} {True} {True} {True} {True} = refl

g1 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((v == v') && (b1) && b2 && b3 && b4 && b5 && True) ≡ True -> v ≡ v'
g1 zero zero b1 b2 b3 b4 b5 pf = refl
g1 (suc v) (suc v') b1 b2 b3 b4 b5 pf = cong suc (g1 v v' b1 b2 b3 b4 b5 pf)

g2 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && ( (v < v') || (v' == v) ) && b2 && b3 && b4 && b5 && True) ≡ True ->
     IsTrue ( (v < v') || (v' == v) )
g2 zero zero True b2 b3 b4 b5 pf = IsTrue.itsTrue
g2 zero (suc v') True b2 b3 b4 b5 pf = IsTrue.itsTrue
g2 (suc v) (suc v') True b2 b3 b4 b5 pf = g2 v v' True b2 b3 b4 b5 pf

g3 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && b2 && (v < v') && b3 && b4 && b5 && True) ≡ True -> IsTrue (v < v')
g3 zero (suc v') True True b3 b4 b5 pf = IsTrue.itsTrue
g3 (suc v) (suc v') True True b3 b4 b5 pf = g3 v v' True True b3 b4 b5 pf

g4 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && b2 && b3 && (v == v') && b4 && b5 && True) ≡ True -> v ≡ v'
g4 zero zero True True True b4 b5 pf = refl
g4 (suc v) (suc v') True True True b4 b5 pf = cong suc (g4 v v' True True True b4 b5 pf)

aux5 : ∀ (n m : Nat) (b : Bool) -> ((n == m) && b && True) ≡ True -> n ≡ m
aux5 zero zero b pf = refl
aux5 (suc n) (suc m) b pf = cong suc (aux5 n m b pf)
 
g5 : ∀ (i i' : PubKeyHash) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && (b2)  && b3 && b4 && (i == i') && b5 && True) ≡ True -> i ≡ i'
g5 (Integer.pos zero) (Integer.pos zero) True True True True b5 pf = refl
g5 (Integer.pos (suc n)) (Integer.pos (suc m)) True True True True b5 pf = cong Integer.pos (cong suc (aux5 n m b5 pf) )
g5 (Integer.negsuc zero) (Integer.negsuc zero) True True True True b5 pf = refl
g5 (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) True True True True  b5 pf = cong Integer.negsuc (cong suc (aux5 n m b5 pf) )

aux6 : ∀ (n m : Nat) -> ((n == m) && True) ≡ True -> n ≡ m
aux6 zero zero pf = refl
aux6 (suc n) (suc m) pf = cong suc (aux6 n m pf)

g6 : ∀ (i i' : Deadline) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && (b2) && b3 && b4 && b5 && (i == i') && True) ≡ True -> i ≡ i'
g6 (Integer.pos zero) (Integer.pos zero) True True True True True pf = refl
g6 (Integer.pos (suc n)) (Integer.pos (suc m)) True True True True True pf = cong Integer.pos (cong suc (aux6 n m pf))
g6 (Integer.negsuc zero) (Integer.negsuc zero) True True True True True pf = refl
g6 (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) True True True True True pf = cong Integer.negsuc (cong suc (aux6 n m pf))

c1 : ∀ (v v' : Value) -> ((v == v') && True) ≡ True -> v ≡ v'
c1 zero zero pf = refl
c1 (suc v) (suc v') pf = cong suc (c1 v v' pf)

p1 : ∀ (n m : Nat) {b} -> ( ((n < m) || (m == n)) && b ) ≡ True -> IsTrue (((n < m) || (m == n)))
p1 zero zero pf = IsTrue.itsTrue
p1 zero (suc m) pf = IsTrue.itsTrue
p1 (suc n) (suc m) pf = p1 n m pf

p2 : ∀ (x y z : Nat) {b} -> (b && (x == (y + z))) ≡ True -> x ≡ y + z
p2 zero zero zero pf = refl
p2 zero zero (suc z) pf = magic (contradiction pf &&False)
p2 zero (suc y) z pf = magic (contradiction pf &&False)
p2 (suc x) zero zero pf = magic (contradiction pf &&False)
p2 (suc x) zero (suc z) pf = cong suc (p2 x zero z pf)
p2 (suc x) (suc y) zero pf = cong suc (p2 x y zero pf)
p2 (suc x) (suc y) (suc z) pf = cong suc (p2 x y (suc z) pf)

a1 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((v == v') && b1 && b2 && b3 && b4 && b5) ≡ True -> v ≡ v'
a1 zero zero b1 b2 b3 b4 b5 pf = refl
a1 (suc v) (suc v') b1 b2 b3 b4 b5 pf = cong suc (a1 v v' b1 b2 b3 b4 b5 pf)

a2 : ∀ (b b1 b2 b3 b4 b5 : Bool) -> ((b1) && ( b ) && b2 && b3 && b4 && b5) ≡ True -> IsTrue ( b )
a2 True True b2 b3 b4 b5 pf = IsTrue.itsTrue

a3 : ∀ (v  v' : Value) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && b2 && (v == v') && b3 && b4 && b5) ≡ True -> v ≡ v'
a3 zero zero True True b3 b4 b5 pf = refl
a3 (suc v) (suc v') True True b3 b4 b5 pf = cong suc (a3 v v' True True b3 b4 b5 pf)

aux4 : ∀ (n m : Nat) (b b' : Bool) -> ((n == m) && b && b') ≡ True -> n ≡ m
aux4 zero zero b b' pf = refl
aux4 (suc n) (suc m) b b' pf = cong suc (aux4 n m b b' pf)

a4 : ∀ (i i' : PubKeyHash) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && (b2)  && b3 && (i == i') && b4 && b5) ≡ True -> i ≡ i'
a4 (Integer.pos zero) (Integer.pos zero) True True True b4 b5 pf = refl
a4 (Integer.pos (suc n)) (Integer.pos (suc m)) True True True b4 b5 pf = cong Integer.pos (cong suc (aux4 n m b4 b5 pf) ) 
a4 (Integer.negsuc zero) (Integer.negsuc zero) True True True b4 b5 pf = refl
a4 (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) True True True b4 b5 pf = cong Integer.negsuc (cong suc (aux4 n m b4 b5 pf) )

aux' : ∀ (n m : Nat) {b} -> (((n == m) && b)) ≡ True -> n ≡ m
aux' zero zero pf = refl
aux' (suc n) (suc m) pf = cong suc (aux' n m pf)

a5 : ∀ (i i' : PubKeyHash) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && (b2)  && b3 && b4 && (i == i') && b5) ≡ True -> i ≡ i'
a5 (Integer.pos zero) (Integer.pos zero) True True True True b5 pf = refl
a5 (Integer.pos (suc n)) (Integer.pos (suc m)) True True True True b5 pf = cong Integer.pos (cong suc (aux' n m pf) )
a5 (Integer.negsuc zero) (Integer.negsuc zero) True True True True b5 pf = refl
a5 (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) True True True True b5 pf = cong Integer.negsuc (cong suc (aux' n m pf))


a' : ∀ (i i' : PubKeyHash) {b} -> ((i == i' && b)) ≡ True -> i ≡ i'
a' (Integer.pos zero) (Integer.pos zero) pf = refl
a' (Integer.pos (suc n)) (Integer.pos (suc m)) pf = cong Integer.pos (cong suc (aux' n m pf) )
a' (Integer.negsuc zero) (Integer.negsuc zero) pf = refl
a' (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) pf = cong Integer.negsuc (cong suc (aux' n m pf) )

a'' : ∀ (i i' : PubKeyHash) {b} -> ((i == i' && b)) ≡ True -> (b) ≡ True
a'' (Integer.pos zero) (Integer.pos zero) pf = pf
a'' (Integer.pos (suc n)) (Integer.pos (suc m)) pf = a'' (Integer.pos n) (Integer.pos m) pf
a'' (Integer.negsuc zero) (Integer.negsuc zero) {b} pf = pf
a'' (Integer.negsuc (suc n)) (Integer.negsuc (suc m)) pf = a'' (Integer.pos n) (Integer.pos m) pf

a6 : ∀ (l l' : List PubKeyHash) (b1 b2 b3 b4 b5 : Bool) -> ((b1) && (b2) && b3 && b4 && b5 && (l == l')) ≡ True -> l ≡ l'
a6 [] [] True True True True True pf = refl
a6 (x ∷ l) (x' ∷ l') True True True True True pf rewrite a' x x' pf = cong (λ y → x' ∷ y) (a6 l l' True True True True True (a'' x x' pf))


validatorImpliesTransition : ∀ (p : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                             -> (pf : agdaValidator p l i ctx ≡ True)
                             -> p ⊢ record { label = l ; value = (inputVal ctx) } ~[ i ]~>
                                record { label = (outputLabel ctx) ; value = (outputVal ctx) }


validatorImpliesTransition p Holding (Propose v pkh d) record { inputVal = iVal ; outputVal = oVal ; outputLabel = Holding } pf
                           = magic (contradiction pf (3&&False {oVal == iVal} {((v < iVal) || (iVal == v))} {(0 < v)}))
validatorImpliesTransition p Holding (Propose v pkh d) record { inputVal = iVal ; outputVal = oVal ; outputLabel
                           = (Collecting v' pkh' d' []) } pf 
                           rewrite g1 oVal iVal ((v < iVal) || (iVal == v)) (0 < v) (v == v') (pkh == pkh') (d == d') pf |
                           sym (g4 v v' (oVal == iVal) ((v < iVal) || (iVal == v)) (0 < v) (pkh == pkh') (d == d') pf) |
                           g5 pkh pkh' (oVal == iVal) ((v < iVal) || (iVal == v)) (0 < v) (v == v') (d == d') pf |
                           g6 d d' (oVal == iVal) ((v < iVal) || (iVal == v)) (0 < v) (v == v') (pkh == pkh') pf
                           = TPropose (g2 v iVal (oVal == iVal) (0 < v) (v == v') (pkh == pkh') (d == d') pf)
                             (g3 zero v (oVal == iVal) ((v < iVal) || (iVal == v)) (v == v') (pkh == pkh') (d == d') pf)
validatorImpliesTransition p Holding (Propose v pkh d) record { inputVal = iVal ; outputVal = oVal ; outputLabel
                           = (Collecting v' pkh' d' (x ∷ sigs')) } pf
                           = magic (contradiction pf (6&&False {oVal == iVal} {((v < iVal) || (iVal == v))} {(0 < v)} {v == v'} {pkh == pkh'} {d == d'}))
validatorImpliesTransition p (Collecting v pkh d sigs) (Add sig) record { inputVal = iVal ; outputVal = oVal ; outputLabel = Holding } pf
                           = magic (contradiction pf (2&&False (oVal == iVal) (query sig (authSigs p))))
validatorImpliesTransition p (Collecting v pkh d sigs) (Add sig) record { inputVal = iVal ; outputVal = oVal ; outputLabel = (Collecting v' pkh' d' sigs') } pf
                           rewrite a1 oVal iVal (query sig (authSigs p)) (v == v') (pkh == pkh') (d == d') (sigs' == (insert sig sigs)) pf |
                           a3 v v' (oVal == iVal) (query sig (authSigs p)) (pkh == pkh') (d == d') (sigs' == (insert sig sigs)) pf |
                           a4 pkh pkh' (oVal == iVal) (query sig (authSigs p)) (v == v') (d == d') (sigs' == (insert sig sigs)) pf |
                           a5 d d' (oVal == iVal) (query sig (authSigs p)) (v == v') (pkh == pkh') (sigs' == (insert sig sigs)) pf |
                           a6 sigs' (insert sig sigs) (oVal == iVal) (query sig (authSigs p)) (v == v') (pkh == pkh') (d == d') pf
                           = TAdd (a2 (query sig (authSigs p)) (oVal == iVal)  (v == v') (pkh == pkh') (d == d') (sigs' == (insert sig sigs)) pf)
validatorImpliesTransition p (Collecting v pkh d sigs) Pay record { inputVal = iVal ; outputVal = oVal ; outputLabel = Holding } pf
                           = TPay (p2 iVal oVal v pf) (p1 (nr p) (lengthNat sigs) pf)
validatorImpliesTransition p (Collecting v pkh d sigs) Pay record { inputVal = iVal ; outputVal = oVal ; outputLabel = (Collecting v' pkh' d' sigs') } pf
                           = magic (contradiction pf &&False )
validatorImpliesTransition p (Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = Holding } pf
                           rewrite c1 outputVal inputVal pf = TCancel
validatorImpliesTransition p (Collecting v pkh d sigs) Cancel record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = (Collecting x x₁ x₂ x₃) } pf
                           = magic (contradiction pf &&False)



-- don't expand ScirptContext, abstact and use functions to extract information from it
-- consistnecy p ≡ par



transitionImpliesValidator : ∀ (p : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                             -> (pf :
                                p ⊢ record { label = l ; value = (inputVal ctx) }
                                ~[ i ]~>
                                record { label = (outputLabel ctx) ; value = (outputVal ctx) })
                             -> agdaValidator p l i ctx ≡ True -- IsTrue instead of ≡ !! be consistent and use only 1
                             
transitionImpliesValidator p Holding (Propose v pkh d)
                           record { inputVal = inputVal₁ ; outputVal = .inputVal₁ ;
                           outputLabel = .(Collecting v pkh d []) } (TPropose p1 p2)
                           rewrite refactor p1 | refactor p2
                           = prop= inputVal₁ v pkh d
transitionImpliesValidator p (Collecting v pkh d sigs) (Add sig) record { inputVal = inputVal₁ ; outputVal = .inputVal₁ ;
                           outputLabel = .(Collecting v pkh d (insert sig sigs)) } (TAdd x)
                           rewrite l=l (insert sig sigs) | refactor x
                           = prop= inputVal₁ v pkh d
transitionImpliesValidator p (Collecting v pkh d sigs) Pay record { inputVal = inputVal₁ ; outputVal = outputVal₁ ;
                           outputLabel = .Holding } (TPay p1 p2)
                           rewrite p1 | (refactor p2) | v=v (outputVal₁ + v)
                           = refl
transitionImpliesValidator p (Collecting v pkh d sigs) Cancel
                           record { inputVal = inputVal₁ ; outputVal = .inputVal₁ ; outputLabel = .Holding } TCancel
                           rewrite v=v inputVal₁
                           = refl



--agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool


{- !!!
prop2' : ∀ (v val : Value) (pkh : PubKeyHash) (d : Deadline) (sigs : List PubKeyHash)
           (par : Params) (n : Nat) (asigs asigs' asigs'' : List PubKeyHash)
         -> n ≡ (nr par) -> asigs ≡ (authSigs par) -> asigs ≡ (asigs' ++ asigs'')
         -> (x : (Collecting v pkh d sigs) ∻ val) -> IsTrue (lengthNat asigs'' >= n) ->
         ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
         ~[ makeIsP asigs'' ]~*
         record { label = Holding ; value = (val - v) {{lemmaOK x}} })
prop2' v val pkh d sigs record { authSigs = .(a2 ++ a3) ; nr = nr₁ ; pfU = pfU₁ ; pfL = pfL₁ } .nr₁ .(a2 ++ a3) a2 a3 refl refl refl (Col p1 p2) pf5 = {!!} 
-}


{-
{v = v} {sigs = []} {val = val}  record { authSigs = .((x ∷ a2) ++ []) ; nr = zero ; pfU = pfU₁ ; pfL = pfL₁ } .zero .((x ∷ a2) ++ []) (x ∷ a2) [] refl refl refl (Col v0 vv) = cons (TPay (lemma+- val v (lemmaLE v val v0)) IsTrue.itsTrue) root
prop2' {v = v} {sigs = x₁ ∷ sigs} {val = val} record { authSigs = .((x ∷ a2) ++ []) ; nr = zero ; pfU = pfU₁ ; pfL = pfL₁ } .zero .((x ∷ a2) ++ []) (x ∷ a2) [] refl refl refl (Col v0 vv) =  cons (TPay (lemma+- val v (lemmaLE v val v0)) IsTrue.itsTrue) root


--cons (TPay {!!} {!!}) {!!}
prop2' record { authSigs = .((x ∷ a2) ++ []) ; nr = (suc n) ; pfU = pfU₁ ; pfL = pfL₁ } .(suc n) .((x ∷ a2) ++ []) (x ∷ a2) [] refl refl refl (Col v0 vv) = cons (TPay {!!} {!!}) root

{-
prop2' (record { authSigs = x ∷ a2 ++ [] ; nr = suc n ; pfU = pfU₁ ; pfL = pfL₁ }) (suc n) (x ∷ a2) (x ∷ a2) [] refl (appendEmpty (x ∷ a2)) (appendEmpty (x ∷ a2)) (Col v0 vv)
-}

--cons (TPay {!!} {!!}) {!!}
prop2' record { authSigs = .(a2 ++ x ∷ a3) ; nr = nr₁ ; pfU = pfU₁ ; pfL = pfL₁ } .nr₁ .(a2 ++ x ∷ a3) a2 (x ∷ a3) refl refl refl (Col v0 vv) = {!!} -}




{-prop2 : ∀ {v val pkh d sigs} (par : Params) -> (x : (Collecting v pkh d sigs) ∻ val) ->
         ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
         ~[ makeIsP (authSigs par) ]~*
         record { label = Holding ; value = (val - v) {{lemmaOK x}} })-}
{-{sigs = sigs} record { authSigs = (x ∷ authSigs) ; nr = zero ; pfU = pfU ; pfL = pfL } = root
prop1 {sigs = sigs} record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = cons (TAdd (why x)) {!prop1!} -}
{--}

--⟨  makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } , cons (TAdd (why x)) (proj₂ {A = makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL })} {!!}) ⟩

--(proj₂ {!((prop1 (record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL })) (makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL })))!})) ⟩ --cons (TAdd (why x)) {!prop1!}

-- (makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL }))
--⟨ makeSigs sigs (makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL }) , (cons (TAdd (why x)) {! (prop1 (record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL }) ( makeSigs sigs (makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL })) )!}) ⟩

{-
lemmaZero : ∀ (val : Value) -> val ≡ (val + zero)
lemmaZero zero = refl
lemmaZero (suc val) = cong suc (lemmaZero val)

lemmaLEFalse : ∀ (a b : Value) -> IsFalse (a < (suc b)) -> IsFalse (a < b)
lemmaLEFalse (suc a) zero pf = IsFalse.itsFalse
lemmaLEFalse (suc a) (suc b) pf = lemmaLEFalse a b pf

lemmaSucMinus : ∀ (a b c : Value) -> (pff : IsFalse (a < (suc b))) -> suc ( (a - (suc b)) {{pff}} + c ) ≡ ((a - b) {{lemmaLEFalse a b pff}} + c)
lemmaSucMinus (suc a) zero c pff = refl
lemmaSucMinus (suc a) (suc b) c pff = lemmaSucMinus a b c pff

lemmaSucPlus : ∀ (a b : Value) -> a + (suc b) ≡ ((suc a) + b)
lemmaSucPlus zero b = refl
lemmaSucPlus (suc a) b = cong suc (lemmaSucPlus a b)

lemma : ∀ (val v : Value) -> (pff : IsFalse (val < v)) -> val ≡ (((val - v) {{pff}}) + v)
lemma val zero pf = lemmaZero val
lemma val (suc v) pf rewrite (lemmaSucPlus ((val - (suc v)) {{pf}}) v) | (lemmaSucMinus val v v pf) = lemma val v (lemmaLEFalse val v pf)

whyy : ∀ (x : Nat) -> IsTrue (x == x)
whyy zero = IsTrue.itsTrue
whyy (suc x) = whyy x

why : ∀ (x : PubKeyHash) {b : Bool} -> IsTrue (x == x || b)
why (Integer.pos zero) = IsTrue.itsTrue
why (Integer.pos (suc n)) = why (Integer.pos n)
why (Integer.negsuc zero) = IsTrue.itsTrue
why (Integer.negsuc (suc n)) = why (Integer.pos n)

lema : ∀ (s : State) -> ∃[ s' ] ∃[ is ] (s ~[ is ]~* s')
lema record { label = Holding ; value = zero ; param = param ; pfG = pfG } = ⟨  record { label = (Collecting 0 999 1234 []) ; value = zero ; param = param ; pfG = Sometimes IsFalse.itsFalse } , ⟨  ( Propose 0 999 1234 ) ∷ [] , cons ( record { label = (Collecting 0 999 1234 []) ; value = zero ; param = param ; pfG = Sometimes IsFalse.itsFalse }) (TPropose refl refl refl IsTrue.itsTrue refl) root ⟩ ⟩
lema record { label = Holding ; value = (suc value) ; param = param ; pfG = pfG } = ⟨  record { label = (Collecting 0 999 1234 []) ; value = (suc value ) ; param = param ; pfG = Sometimes IsFalse.itsFalse } , ⟨  ( Propose 0 999 1234 ) ∷ [] , cons ( record { label = (Collecting 0 999 1234 []) ; value = (suc value) ; param = param ; pfG = Sometimes IsFalse.itsFalse }) (TPropose refl refl refl IsTrue.itsTrue refl) root ⟩ ⟩
lema record { label = (Collecting v pkh d sigs) ; value = value ; param = record { authSigs = (x ∷ authSigs₁) ; nr = nr ; pfU = pfU ; pfL = pfL } ; pfG = (Sometimes pff) } = ⟨ record { label = (Collecting v pkh d (insert x sigs)) ; value = value ; param = record { authSigs = (x ∷ authSigs₁) ; nr = nr ; pfU = pfU ; pfL = pfL } ; pfG = Sometimes pff } , ⟨ ((Add x) ∷ []) , cons (record { label = (Collecting v pkh d (insert x sigs)) ; value = value ; param = record { authSigs = (x ∷ authSigs₁) ; nr = nr ; pfU = pfU ; pfL = pfL } ; pfG = Sometimes pff }) (TAdd (why x)) root ⟩ ⟩


liquidity : ∀ (s : State) -> value s ≠ 0 -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (IsTrue (value s' < value s)))
liquidity record { label = Holding ; value = zero ; param = param ; pfG = pfG } pf = magic (pf refl)
liquidity record { label = Holding ; value = (suc value) ; param = param ; pfG = pfG } pf = {!!}
liquidity record { label = (Collecting v pkh d sigs) ; value = value ; param = record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL } ; pfG = pfG } pf = {!!}
-}
{-
pf with (lengthNat (sig ∷ sigs) >= (nr p) )
  ... | False = {!!}
  ... | True = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩

-----------NEEDS DEC!!!???

-- record { label = Holding ; value = (value - v) ; pfG = Always }
-}

{-
 ⟨ record { label = Holding ; value = ( value - v ) {{x}} ; pfG = Always } , ⟨  (Pay) ∷ [] ,
      ⟨ cons (record { label = Holding ; value = (value - v) {{x}} ; pfG = Always }) (TPay (lemma value v x) {!!}) root , {!!} ⟩ ⟩ ⟩

-}

{-
  TAdd : ∀ {val p v pkh d ctx sig sigs}
    -> IsTrue (agdaValidator p (Collecting v pkh d sigs) (Add sig) ctx)
    -------------------
    -> record {label = (Collecting v pkh d sigs) ; value = val ; param = p}
       ~> record {label = (Collecting v pkh d (insert sig sigs)) ; value = val ; param = p}

  TPay : ∀ {val p v pkh d ctx sigs}
    -> IsTrue (agdaValidator p (Collecting v pkh d sigs) Pay ctx)
    -------------------
    -> record {label = (Collecting v pkh d sigs) ; value = val ; param = p}
       ~> record {label = Holding ; value = (val - v) ; param = p}

  TCancel : ∀ {val p v pkh d ctx sigs}
    -> IsTrue (agdaValidator p (Collecting v pkh d sigs) Cancel ctx)
    -------------------
    -> record {label = (Collecting v pkh d sigs) ; value = val ; param = p}
       ~> record {label = Holding ; value = val ; param = p}
-}

{-





data _↓_ : State -> State -> Set where

  done : ∀ { s }
    ------------
    -> s ↓ s

  step : ∀ {s s''} (s' : State)
    -> s ~> s'
    -> s' ↓ s''
    ----------------
    -> s ↓ s''



test1 : IsTrue (agdaValidator (record { authSigs = "a" ∷ "b" ∷ "c" ∷ [] ; nr = 2}) Holding (Propose 1 "a" 10) (record { inputVal = 10 ; outputVal = 10 ; outputLabel = Collecting 1 "a" 10 [] })) 
test1 = IsTrue.itsTrue

liquidity : ∀ (s : State) ->  ∃[ s' ] ((s ↓ s') × (IsTrue (value s <= value s')))
liquidity record { label = Holding ; value = value ; param = param } = ⟨ record {label = Holding ; value = (value - 1) ; param = param} , ⟨ step ( (record { label = (Collecting 1 "a" 1 []) ; value = value ; param = param })) (TPropose {!!}) {!!} , {!!} ⟩ ⟩
liquidity record { label = (Collecting x x₁ x₂ x₃) ; value = value ; param = param } = {!!}



-}


{--}
{-
transition : Params -> Label -> Input -> ScriptContext -> State
transition p l i ctx =
    if agdaValidator p l i ctx
      then (case i of λ where
        (Propose v pkh d) -> record {label = newLabel ctx ; value = newValue ctx}
        (Add _) ->  record {label = newLabel ctx ; value = newValue ctx}
        Pay ->  record {label = newLabel ctx ; value = newValue ctx}
        Cancel ->  record {label = newLabel ctx ; value = newValue ctx} )
      else record {label = l ; value = oldValue ctx}
-}
{-
liquidity : ∀ (ctx : ScriptContext)
  -> ∃[ pkh ] ∃[ r ] ∃[ v ] (((query pkh (query r (omap1 s)) ≡ v) ⊎ (query pkh (query r (omap2 s)) ≡ v)) × (0ℤ Data.Integer.< v ) )
  -> ∃[ pkh ] ∃[ v ] ∃[ c ] ∃[ r ] ∃[ s' ] ( cancel s pkh v c r ≡ ( just s' ) × (v1 s' Data.Integer.< v1 s ⊎ v2 s' Data.Integer.< v2 s ) )


agdaValidator l s i t o s' = case s of λ where
  (Collecting v pkh d sigs) -> case i of λ where

    (Propose _ _ _) -> False
    (Add sig) -> True --wip
    Pay -> True --wip
    Cancel -> t > d 

  Holding -> case i of λ where

    (Propose v pkh d) -> case s' of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs) -> (v == v' && (pkh == pkh' && (d == d' && (sigs == []))))
    (Add _) -> False
    Pay -> False
    Cancel -> False-}
  
{-

case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v'

data _~>_ : Label -> Label -> Set where

    h~>c : ∀ (val : Value), (pkh : PubKeyHash), (deadline : Deadline) , (sigs : List PubKeyHash) 
    -------------------
    -> Holding ~> Collecting val pkh deadline sigs

    c~>c : ∀ val, pkh, deadline, sigs, sig
    -------------------
    -> Collecting val pkh deadline sigs ~> Collecting val pkh deadline (insert sig sigs)


module Sort (A : Set) where
  insert' : A → List A → List A
  insert' x [] = x ∷ []
  insert' x (y ∷ ys) = y ∷ insert' x ys

  sort' : List A → List A
  sort' []       = []
  sort' (x ∷ xs) = insert' x (sort' xs)

-}
--lengthSublemma
{-
postulate
  helper : ∀ (n : Nat) (x : PubKeyHash) (xs : List PubKeyHash) -> IsTrue (n < lengthNat xs) -> IsTrue (n < lengthNat (insert x xs)) 

uil : ∀ (sigs sigs' : List PubKeyHash) (n : Nat) (pf1 : Unique sigs) (pf2 : IsTrue (lengthNat sigs > n))
                      -> IsTrue (n < lengthNat (makeSigs' sigs' sigs))
uil (x ∷ s1) s2 n (pf :: pf1) pf2 = helper n x (makeSigs' s2 s1) {!!} --(uil s1 s2 n pf1 {!!})

{-
makeSigsLemma : ∀ (par : Params) (sigs : List PubKeyHash) ->
                IsTrue (nr par < lengthNat (makeSigs' sigs (authSigs par)))
makeSigsLemma record { authSigs = (x ∷ authSigs₁) ; nr = nr ; pfU = pfU ; pfL = pfL } sigs = {!!}
-}

lengthLemma record { authSigs = (x ∷ authSigs) ; nr = zero ; pfU = pfU ; pfL = IsTrue.itsTrue } sigs = {!!}
lengthLemma record { authSigs = (x ∷ authSigs) ; nr = (suc nr₁) ; pfU = pfU ; pfL = pfL } sigs = {!!}


uniqueInsertLemma : ∀ (sigs sigs' aux aux' : List PubKeyHash) (n : Nat) (pf1 : Unique sigs) (pf2 : IsTrue (lengthNat sigs > n))
                    -> (pf3 : sigs ≡ aux ++ aux') -> IsTrue (n < lengthNat (makeSigs' sigs' aux'))
uniqueInsertLemma .(_ ∷ _) s2 (x ∷ a1) [] n (pf :: pf1) pf2 pf3 = {!!}
uniqueInsertLemma .(_ ∷ _) s2 a1 (x ∷ a2) n (pf :: pf1) pf2 pf3 = {!!}

makeSigsLemma : ∀ (x : PubKeyHash) (ys : List PubKeyHash) (n : Nat) -> Unique ys
                -> IsTrue (lengthNat ys > n) -> IsTrue (n < lengthNat (makeSigs' [] ys))
makeSigsLemma x (y ∷ ys) n pf1 pf2 = {!!}

--helper n x (makeSigs' s2 s1) (uil' s1 s2 n pf1 {!!})

makeIs : Params -> List Input
makeIs record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = []
makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = Add x ∷ (makeIs (record
                                                                                                          { authSigs = authSigs
                                                                                                          ; nr = nr
                                                                                                          ; pfU = pfU 
                                                                                                          ; pfL = pfL
                                                                                                          }) ) 

makeSigs : List PubKeyHash -> List Input -> List PubKeyHash
makeSigs sigs [] = sigs
makeSigs sigs (Propose x x₁ x₂ ∷ is) = makeSigs sigs is
makeSigs sigs (Add x ∷ is) = makeSigs (insert x sigs) is
makeSigs sigs (Pay ∷ is) = makeSigs sigs is
makeSigs sigs (Cancel ∷ is) = makeSigs sigs is
-}
{-
expand : ∀ {authSigs x nr pfU pff pfL s i is s'} -> i ≠ (Pay) -> record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL } ⊢ s ~[ i ∷ is ]~* s' -> record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } ⊢ s ~[ i ∷ is ]~* s'
expand neq (cons (TPropose x x₁) root) = cons (TPropose x x₁) root
expand neq (cons (TPropose x x₁) (cons (TAdd x₂) pf)) = cons (TPropose x x₁) (expand (λ ()) (cons (TAdd x₂) pf))
expand neq (cons (TPropose x x₁) (cons (TPay x₂ x₃) pf)) = cons (TPropose x x₁) {!!}
expand neq (cons (TPropose x x₁) (cons TCancel pf)) = {!!}
expand neq (cons (TAdd x) pf) = {!!}
expand neq (cons (TPay x x₁) pf) = magic (neq refl)
expand neq (cons TCancel pf) = cons {!!} {!!} --(expand pf)
-}
--cons {!!} (expand pf)
{-
awful : ∀ {v pkh d sigs val x authSigs nr pfU pff pfL}
        -> record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL } ⊢
           record { label = Collecting v pkh d (insert x sigs) ; value = val }
           ~[ makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL }) ]~*
           record { label = Collecting v pkh d (makeSigs (insert x sigs) (makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL }))) ; value = val }
        -> record { authSigs = x ∷ authSigs ; nr = suc nr ; pfU = pff :: pfU ; pfL = pfL } ⊢
           record { label = Collecting v pkh d (insert x sigs) ; value = val }
           ~[ makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL }) ]~*
           record { label = Collecting v pkh d (makeSigs (insert x sigs) (makeIs (record { authSigs = authSigs ; nr = nr ; pfU = pfU ; pfL = pfL }))) ; value = val }
awful {nr = zero} root = root
awful {authSigs = x ∷ authSigs₁} {nr = suc nr₁} {x₁ :: pfU₁} (cons x₂ pf) = cons (TAdd {!!}) {!awful!}
-}
--awful1 : ∀ { v pkh d sigs val x authSigs nr pfU pff pfL } -> ( record { authSigs = x ∷ authSigs ; nr = suc nr ; pfU = pff :: pfU ; pfL = pfL } ⊢ record { label = (Collecting v pkh d sigs) ; value = val } ~[ makeIs par ]~* record { label = (Collecting v pkh d (makeSigs sigs (makeIs par))) ; value = val })

{-
insertLemma : ∀ (x y : PubKeyHash) (zs : List PubKeyHash) -> insert x (insert y zs) ≡ insert y (insert x zs)
insertLemma (Integer.pos n) (Integer.pos n₁) [] = {!!}
insertLemma (Integer.pos n) (Integer.negsuc n₁) [] = {!!}
insertLemma (Integer.negsuc n) y [] = {!!}
insertLemma x y (z ∷ zs) = {!!}

makeSigsLemma : ∀ (x : PubKeyHash) (sigs sigs' : List PubKeyHash)
                -> (makeSigs' (insert x sigs) sigs') ≡ insert x (makeSigs' sigs sigs')
makeSigsLemma x s1 [] = refl
makeSigsLemma x s1 (x₁ ∷ s2) = {!!} --makeSigsLemma x₁ (insert x s1) s2
-}
-}
