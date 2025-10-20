
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


module Example where

--open import ListInsertLib (PubKeyHash) (==ito≡) (=/=ito≢)

record Context : Set where
  field
    value         : Value  
    outVal        : Value
    outAdr        : PubKeyHash
    now           : Deadline
    tsig          : PubKeyHash
open Context

CommonInfo = Nat
InputInfo = Nat
OutputInfo = Nat

record State : Set where
  field
    input      : InputInfo
    common     : CommonInfo
    output     : OutputInfo
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
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s }

    -------------------
    -> par ⊢ s


data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TPropose : ∀ {v pkh d s s' par} 
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'

  TAdd : ∀ {sig par s s' } 

    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'

  TPay : ∀ { s s' par} 
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par} 

    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'


data _⊢_~[_]~|_ : Params -> State -> Input -> State -> Set where

  TClose : ∀ {par s s'}

    -------------------
    -> par ⊢ s ~[ Close ]~| s'


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

  fin : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~| s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''






inputIrrelevance : ∀ {par s i s'} (info : InputInfo)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ s ~[ i ]~> record s' {input = info}


outputIrrelevance : ∀ {par s i s'} (info : OutputInfo)
                 -> par ⊢ s                        ~[ i ]~> s'
                 -> par ⊢ record s {output = info} ~[ i ]~> s'



inputIrrelevance = {!!}
             
outputIrrelevance = {!!}


record StateIn : Set where
  field
    input      : InputInfo
    common     : CommonInfo
open StateIn

record StateOut : Set where
  field
    common     : CommonInfo
    output     : OutputInfo
open StateOut


data _⊢_-[_]->_ : Params -> StateIn -> Input -> StateOut -> Set where
 
  Whatever : ∀ { par s i s' } 
    -------------------
    -> par ⊢ s -[ i ]-> s'
    

data _≅_ : StateOut -> StateIn -> Set where

   placeholder : ∀ { outS inS }
     -> outS .common ≡ inS .common
     -----------------------------
     -> outS ≅ inS

data _⊢_-[_]-*_ : Params -> StateIn -> List Input -> StateOut -> Set where

  root : ∀ { s par s' }
    ------------------
    -> par ⊢ s -[ [] ]-* s'

  cons : ∀ { par s1 i s2 is s }
    -> par ⊢ s1 -[ i ]-> s2
    -> ∃[ s2' ] ((s2 ≅ s2') × par ⊢ s2' -[ i ]-> s)
    -------------------------
    -> par ⊢ s1 -[ (i ∷ is) ]-* s


{-par (tok , Holding) i adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = false ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = false ; mint = .-1 ; tokAssetClass = tokAssetClass } refl p1 p2 = TClose refl (<ᵇto< (get p1)) refl refl refl refl refl
bothImplyClose par (tok , Holding) i adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = .-1 ; tokAssetClass = tokAssetClass } refl () p2
bothImplyClose par (tok , Collecting x x₁ x₂ x₃) i adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; time = time ; payTo = payTo ; payAmt = payAmt ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = true ; hasTokenOut = true ; mint = .-1 ; tokAssetClass = tokAssetClass } refl () p2-}

{-
validatorImpliesTransition : ∀ {oV oA t s tok spn mnt} (par : Params) (d : Datum) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Close
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> par ⊢
                           record { datum = d ; value = (inputVal ctx) ;
                           outVal = oV ; outAdr = oA ; now = t ; tsig = s ; continues = true ;
                           spends = spn ; hasToken = hasTokenIn ctx ; mint = mnt ; token = tok}
                           ~[ i ]~>
                           record { datum = (outputDatum ctx) ; value = (outputVal ctx) ;
                           outVal = payAmt ctx ; outAdr = payTo ctx ; now = time ctx ; tsig = signature ctx ;
                           continues = continuing ctx ; spends = inputRef ctx ; hasToken = hasTokenOut ctx ;
                           mint = mint ctx ; token = tokAssetClass ctx}-}

{-
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
-}


{- MINSIG
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
         -> continues s ≡ true
         -> continues s' ≡ true
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop' {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
           context = record { value = .value₁ ;
                              outVal = .outVal₁ ;
                              outAdr = .outAdr₁ ;
                              now = .now₁ ;
                              tsig = tsig₁ } ;
           continues = True }
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
                                                          continues = true }) (makeIs [])) } ;
           continues = True }
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
                                       
--Prop3 (Can add minimum nr of signatures 1 by 1)
prop3 : ∀ { v pkh d sigs } (s s' : State) (par : Params) 
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (take (nr par) (authSigs par)) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (take (nr par) (authSigs par)))
        -> continues s ≡ true
        -> continues s' ≡ true
        -> par ⊢ s ~[ (makeIs (take (nr par) (authSigs par))) ]~* s'
prop3 s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 = prop' s s' par (authSigs par) [] (take (nr par) (authSigs par)) (drop (nr par) (authSigs par)) refl (sym (take++drop≡id (nr par) (authSigs par))) p1 p2 p3 p4 p5 p6 p7 p8 p9


--Prop3 (Can add minimum nr of signatures 1 by 1)
prop3' : ∀ { v pkh d sigs } (s s' : State) (par : Params) 
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (drop (length (authSigs par) - nr par) (authSigs par)) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (drop (length (authSigs par) - nr par) (authSigs par)))
        -> continues s ≡ true
        -> continues s' ≡ true
        -> par ⊢ s ~[ (makeIs (drop (length (authSigs par) - nr par) (authSigs par))) ]~* s'
prop3' s s' par p1 p2 p3 p4 p5 p6 p7 p8 p9 = prop s s' par (authSigs par) (take (length (authSigs par) - nr par) (authSigs par)) (drop (length (authSigs par) - nr par) (authSigs par)) refl (sym (take++drop≡id (monusNat (foldr (λ _ → suc) zero (authSigs par)) (nr par)) (authSigs par))) p1 p2 p3 p4 p5 p6 p7 p8 p9

--prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8 p9

prop2 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
          -> ValidS s
          -> label s ≡ Collecting v pkh d sigs
          -> label s' ≡ Holding
          -> outVal (context s') ≡ v
          -> outAdr (context s') ≡ pkh
          -> value (context s) ≡ value (context s') + v
          -> ValidP par
          -> continues s ≡ true
          -> continues s' ≡ true
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
liquidity : ∀ (par : Params) (s : State) (pkh : PubKeyHash)
          -> ValidS s -> ValidP par -> continues s ≡ true
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') ×
            ((value (context s') ≡ 0) × (getSigNr is ≤ nr par) ) )

liquidity par s pkh (Stp p1) valid p2 rewrite p1 = ⊥-elim (get⊥ (sym p2))

liquidity par
  s@(record { label = .Holding ;
              context = record { value = value ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh (Hol refl) (Always p2 p3) pf with minValue <= value in eq
...| false  = ⟨ s' , ⟨  [ Close ] , ⟨ cons (TClose refl (n≤ᵇto> eq) pf refl) root , ⟨ refl , z≤n ⟩ ⟩ ⟩ ⟩
      where
        s' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = tsig } ;
                      continues = false }
...| true = ⟨ s'' , ⟨ (Propose value pkh 0) ∷ ((makeIs (take (nr par) (authSigs par))) ++ [ Pay ]) ,
    ⟨ cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl z≤n pf refl)
    (prop2 s' s'' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p2 p3) refl refl refl ) ,
    ⟨ refl , sigNrLemma p3 refl ⟩ ⟩ ⟩ ⟩
      where
        s'' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = pkh } ;
                      continues = true }
        s' = record { label = Collecting value pkh 0 [] ;
                       context = record { value = value ;
                                          outVal = outVal ;
                                          outAdr = outAdr ;
                                          now = now ;
                                          tsig = tsig } ;
                      continues = true }



liquidity par
  s@(record { label = (Collecting v' pkh' d' sigs') ;
             context = record { value = value ;
                                outVal = outVal ;
                                outAdr = outAdr ;
                                now = now ;
                                tsig = tsig } } )
  pkh (Col refl p2 p3 p6) (Always p4 p5) pf with minValue <= value in eq
...| false  = ⊥-elim (≤⇒≯ (≤-trans p3 p2) (n≤ᵇto> eq))

...| true  = ⟨ s''' , ⟨ Cancel ∷ (Propose value pkh 0) ∷ ((makeIs (take (nr par) (authSigs par))) ++ [ Pay ]) ,
    ⟨ cons (TCancel {s' = s'}
    (s≤s (v≤v d')) refl refl refl pf refl)
    (cons (TPropose (v≤v value) (≤ᵇto≤ eq) refl refl refl z≤n refl refl)
    (prop2 s'' s''' par (Col refl (v≤v value) (≤ᵇto≤ eq) root) refl refl refl refl refl (Always p4 p5) refl refl refl)) ,
    ⟨ refl , (sigNrLemma p5 refl) ⟩ ⟩ ⟩ ⟩
      where
        s''' = record { label = Holding ;
                       context = record { value = zero ;
                                          outVal = value ;
                                          outAdr = pkh ;
                                          now = now ;
                                          tsig = pkh } ;
                      continues = true }
        s' = record { label = Holding ;
                      context = record { value = value ;
                                         outVal = outVal ;
                                         outAdr = outAdr ;
                                         now = suc d' ;
                                         tsig = tsig } ;
                      continues = true }
        s'' = record { label = Collecting value pkh 0 [] ;
                        context = record { value = value ;
                                           outVal = outVal ;
                                           outAdr = outAdr ;
                                           now = 0 + 1 ;
                                           tsig = tsig } ;
                      continues = true }

   

-}
