open import Validators.DEx
open import Lib
open import Value
open import ScriptContext Label Value renaming (payVal to payVal' ; buyVal to buyVal')

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer.Base --hiding (_+_; _-_)
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
import Data.Sign.Base as Sign

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

open import Haskell.Prim hiding (⊥) -- ; All)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup ; _<>_)


open import ProofLib

module Proofs.DExProofs where



record State : Set where
  field
    datum      : Label
    value      : Value  
    payVal     : Value
    payTo      : PubKeyHash
    buyVal     : Value
    buyTo      : PubKeyHash
    tsig       : PubKeyHash
    continues  : Bool
    spends     : TxOutRef
    hasToken   : Bool
    mint       : Integer
    token      : AssetClass
open State

record MParams : Set where
    field
        address   : Address
        outputRef : TxOutRef 
        sellC  : AssetClass
        buyC   : AssetClass
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s l}
    -> datum s ≡ ((token s) , l)
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> hasToken s ≡ true
    -> checkRational (ratio l) ≡ true
    -------------------
    -> par ⊢ s



data _⊢_~[_]~>_ : MParams -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {v r s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -> value s' ≡ v 
    -> datum s' ≡ ((fst (datum s)) , (record { ratio = r ; owner = owner (snd (datum s)) })) 
    -> checkRational r ≡ true 
    -> checkMinValue v ≡ true
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Update v r) ]~> s'


  TExchange : ∀ {amt pkh s s' par}
    -> value s ≡ value s' <> assetClassValue (sellC par) amt
    -> datum s' ≡ datum s
    -> payTo s' ≡ owner (snd (datum s))
    -> ratioCompare amt (assetClassValueOf (payVal s') (buyC par)) (ratio (snd (datum s))) ≡ true
    -> checkMinValue (payVal s') ≡ true
    -> buyTo s' ≡ pkh 
    -> assetClassValueOf (buyVal s') (sellC par) ≡ amt
    -> checkMinValue (buyVal s') ≡ true
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'



data _⊢_~[_]~|_ : MParams -> State -> Input -> State -> Set where

  TClose : ∀ {s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -> mint s' ≡ -1
    -> continues s ≡ true
    -> continues s' ≡ false
    -> hasToken s ≡ true
    -> hasToken s' ≡ false
    -------------------
    -> par ⊢ s ~[ Close ]~| s'
    


Valid : State -> Set 
Valid s = checkRational (ratio (snd (datum s))) ≡ true × continues s ≡ true × hasToken s ≡ true


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


--State Validity Invariant
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> Valid s
validStateInitial {record { datum = .(token₁ , _) ; value = value₁ ; payVal = payVal₁ ; payTo = payTo₁ ; buyVal = buyVal₁ ; buyTo = buyTo₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl p2 p3 p4 p5 p6) = p6 , p3 , p5

validStateTransition : ∀ {s s' : State} {i par}
  -> Valid s
  -> par ⊢ s ~[ i ]~> s'
  -> Valid s'
validStateTransition v (TUpdate x x₁ refl x₃ x₄ x₅ x₆ x₇ x₈) = x₃ , x₆ , x₈
validStateTransition (fst , snd , thd) (TExchange x refl x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = fst , x₉ , x₁₁


{- deprecated
validStateFinal : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~| s'
  -> ValidS s'
validStateFinal iv (TClose p1 p2 p3 p4 p5 p6) = Stp p4 

validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x
validStateMulti iv (fin pf x) = validStateMulti (validStateFinal iv pf) x-}


liquidity : ∀ (par : MParams) (s : State) 
          -> Valid s
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ MkMap []) )

liquidity par s (p1 , p2 , p3) = ⟨ s' , ⟨  Close ∷ [] , (fin (TClose refl refl p2 refl p3 refl) root , refl) ⟩ ⟩
  where
    s' = record
          { datum = datum s
          ; value = MkMap []
          ; payVal = MkMap []
          ; payTo = zero
          ; buyVal = MkMap []
          ; buyTo = zero
          ; tsig = owner (snd (datum s))
          ; continues = false
          ; spends = zero
          ; hasToken = false
          ; mint = -1
          ; token = fst (datum s)
          }



getS : Label -> ScriptContext -> State
getS d ctx = record
              { datum = d
              ; value = oldValue ctx
              ; payVal = MkMap [] --payVal' ctx
              ; payTo = 0 --payAdr ctx
              ; buyVal = MkMap [] --buyVal' ctx
              ; buyTo = 0 --buyAdr ctx
              ; tsig = 0 --sig ctx
              ; continues = true 
              ; spends = 0 --iRef ctx
              ; hasToken = (assetClassValueOf (oldValue ctx) (fst d)) == 1
              ; mint = 0 --getMintedAmount ctx
              ; token = 0 --ownAssetClass ctx
              }



getS' : ScriptContext -> State
getS' ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; payVal = payVal' ctx
             ; payTo = payAdr ctx
             ; buyVal = buyVal' ctx
             ; buyTo = buyAdr ctx
             ; tsig = sig ctx
             ; continues = continuing ctx
             ; spends = iRef ctx
             ; hasToken = (assetClassValueOf (newValue ctx) (fst (newDatum ctx))) == 1
             ; mint = getMintedAmount ctx
             ; token = ownAssetClass ctx
             }




==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ {record { num = num ; den = den }} {record { num = num' ; den = den' }} pf
  rewrite ==ito≡ num num' (get pf) | ==ito≡ den den' (go (eqInteger num num') pf) = refl


==pto≡ : {a b : (AssetClass × Integer)} -> (a == b) ≡ true -> a ≡ b
==pto≡ {ac , amt} {ac' , amt'} pf rewrite (==to≡ ac ac' (get pf)) | (==ito≡ amt amt' (go (ac == ac') pf)) = refl

==v'to≡ : {m m' : List (AssetClass × Integer)} -> (m == m') ≡ true -> m ≡ m'
==v'to≡ {[]} {[]} p = refl
==v'to≡ {x ∷ m} {y ∷ m'} pf rewrite (==pto≡ {x} {y} (get pf))= cong (λ z → y ∷ z) (==v'to≡ (go (x == y) pf))


==Lto≡ : ∀ (l l' : Info)
       -> (l == l') ≡ true
       -> l ≡ l' 
==Lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ owner owner' (go (ratio == ratio') pf) = refl

==dto≡ : {a b : Label} -> (a == b) ≡ true -> a ≡ b
==dto≡ {tok , l} {tok' , l'} p rewrite ==to≡ tok tok' (get p) | ==Lto≡ l l' (go (tok == tok') p) = refl

getPar : Params -> Address -> TxOutRef -> MParams
getPar record { sellC = sellC ; buyC = buyC } adr oref = record
                                                          { address = adr
                                                          ; outputRef = oref
                                                          ; sellC = sellC
                                                          ; buyC = buyC
                                                          }

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {adr oref} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Close
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> getPar par adr oref  ⊢ getS d ctx ~[ i ]~> getS' ctx
validatorImpliesTransition par d (Update v r) ctx p1 p2
  = TUpdate (==to≡ (owner (snd d)) (sig ctx) (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==vto≡ (newValue ctx) v (get (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==dto≡ (get (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))
  (get (go (checkRational r) (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))) refl
  (get (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get p2)
  (subst (λ x -> checkTokenOut x ctx ≡ true)
  (sym (==to≡ (newDatum ctx .fst) (d .fst) (get (get (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))))) 
  (go (continuing ctx) (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))) 
validatorImpliesTransition par d (Exchange amt pkh) ctx p1 p2
  = TExchange (==vto≡ (oldValue ctx) (addValue (newValue ctx) (assetClassValue (par .sellC) amt))
  (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==dto≡ (get (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))
  (==to≡ (payAdr ctx) (owner (snd d)) (get (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (get (go (payAdr ctx == owner (d .snd)) (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (go (ratioCompare amt (assetClassValueOf (payVal' ctx) (buyC par)) (ratio (snd d))) (go (payAdr ctx == owner (d .snd))
  (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==to≡ (buyAdr ctx) pkh (get (get (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (==ito≡ (assetClassValueOf (buyVal' ctx) (sellC par)) amt (get (go (buyAdr ctx == pkh)
  (get (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))))
  (go (assetClassValueOf (buyVal' ctx) (sellC par) == amt) (go (buyAdr ctx == pkh) (get (go (checkPayment par amt (d .snd) ctx)
  (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))) refl
  (get (go (checkBuyer par amt pkh ctx) (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (get p2) (subst (λ x -> checkTokenOut x ctx ≡ true)
  (sym (==to≡ (newDatum ctx .fst) (d .fst) (get (get (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt))
  (go (checkTokenIn (d .fst) ctx) p2))))))
  (go (continuing ctx) ((go (checkBuyer par amt pkh ctx) (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))))
validatorImpliesTransition par d Close ctx p1 p2 = ⊥-elim (p1 refl)




mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≢ -1
                           -> (pf : agdaPolicy adr oref top ctx ≡ true)
                           -> getPar par adr oref ⊢ getS' ctx
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 with getMintedAmount ctx == -1 in eq
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | True rewrite ==ito≡ mint' (negsuc 0) eq = ⊥-elim (p1 refl) --rewrite p1 = ⊥-elim (get⊥ eq)
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False with getMintedAmount ctx == 1 in eq'
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False | True rewrite ==to≡ tokAssetClass tok (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))) = TStart refl (==ito≡ mint' (+ 1) eq') (get p2) (==to≡ oref inputRef (get (go (continues) p2)))
                  (subst (λ x -> checkTokenOut x ctx ≡ true ) (==to≡ tokAssetClass tok (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))))
                  (go (checkDatum adr ctx) (go (consumes oref ctx)
                  (go (continuingAddr adr ctx) p2))))
                  (go (ownAssetClass ctx == tok)
                  (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))))
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False | False = ⊥-elim (get⊥ (sym p2))


bothImplyClose : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref top ctx) ≡ true
               -> getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx
bothImplyClose par d adr oref top ctx p with getMintedAmount ctx == 1 in eq
bothImplyClose par d adr oref top ctx p | True 
  = ⊥-elim (get⊥ (t=f (continuing ctx) (get (go (checkTokenIn (d .fst) ctx) (get p))) (get (go (agdaValidator par d Close ctx) p))))
bothImplyClose par d adr oref top ctx p | False with getMintedAmount ctx == -1 in eq'
bothImplyClose par d adr oref top ctx p | False | True
  = TClose (==to≡ (owner (snd d)) (sig ctx) (go (not (checkTokenOut (newDatum ctx .fst) ctx)) (go (not (continuing ctx))
    (go (checkTokenIn (d .fst) ctx) (get p))))) (==ito≡ (getMintedAmount ctx) (negsuc 0) eq') refl
    (unNot (continuing ctx) ((get (go ((checkTokenIn (d .fst) ctx)) (get p))))) (get (get p))
    (unNot ((eqInteger (assetClassValueOf (newValue ctx) (newDatum ctx .fst)) (+ 1)))
    ((get (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p)))))) 
bothImplyClose par d adr oref top ctx p | False | False
  = ⊥-elim (get⊥ (sym (go (eqInteger (assetClassValueOf (oldValue ctx) (d .fst)) (+ 1)
         && not (continuing ctx) && false) p)))



≡to==l : ∀ {a b : Info} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl

lst=lst : ∀ (lst : List (Nat × Integer)) -> (lst == lst) ≡ true
lst=lst [] = refl
lst=lst (x ∷ lst) rewrite n=n (x .fst) | i=i (x .snd) = lst=lst lst



transitionImpliesValidator : ∀ {adr oref} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
                           -> agdaValidator par d i ctx ≡ true
transitionImpliesValidator par d (Update v r) ctx (TUpdate refl refl refl p4 p5 p6 refl p8 p9)
  rewrite p4 | p5 | p6 | p6 | p8 | p9 | n=n (owner (d .snd)) | v=v v | n=n (d .fst) | i=i (num r) | i=i (den r) = p6
transitionImpliesValidator par d (Exchange amt pkh) ctx (TExchange refl refl refl p4 p5 refl refl p8 p9 refl p11 p12)
  rewrite p4 | p5 | p8 | p9 | p11 | p12
    | v=v (addValue (newValue ctx) (MkMap ((sellC par , assetClassValueOf (buyVal' ctx) (sellC par)) ∷ []))) 
    | n=n (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) | n=n pkh | i=i (assetClassValueOf (buyVal' ctx) (sellC par)) = p9


startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS' ctx
                           -> agdaPolicy adr oref top ctx ≡ true
startImpliesMinting adr oref top ctx (TStart refl refl refl refl p5 p6) rewrite p5 | p6 | n=n oref | n=n (ownAssetClass ctx) = refl 

closeImpliesBoth : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx
               -> ((agdaValidator par d Close ctx && agdaPolicy adr oref top ctx) ≡ true)
closeImpliesBoth par d adr oref top ctx (TClose refl refl refl refl p5 p6) rewrite p5 | p6 | n=n (owner (d .snd)) = refl --refl , refl


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



record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

Classifier : Argument -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } } = Initial
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Terminal



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


removeClose : ∀ (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx)
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Update x x₁) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Exchange x x₁) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx) (negsuc 0) (get (go (not (continuing ctx)) (go (checkTokenIn (fst dat) ctx) p2)))))

totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } }} x → mintingImpliesStart adr oref tt c (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat (Update a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → validatorImpliesTransition par dat (Exchange a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → bothImplyClose par dat adr oref tt c x }
                    ; from = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } }} x → startImpliesMinting adr oref tt c x  ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp c x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat inp c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat (Update a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → transitionImpliesValidator par dat (Exchange a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } }} x → closeImpliesBoth par dat adr oref tt c x } } 


