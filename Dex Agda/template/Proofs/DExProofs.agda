open import Validators.DEx
open import Lib
open import Value

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
        tokName   : TokenName
        sellC  : AssetClass
        buyC   : AssetClass
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s l}
    -> datum s ≡ ((token s) , l)
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s 
    -> token s .snd ≡ tokName par
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
    -> ratioCompare amt (assetClassValueOf (payVal s') (buyC par)) (ratio (snd (datum s))) ≡ true
    -> checkMinValue (payVal s') ≡ true
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
validStateInitial {record { datum = .(token₁ , _) ; value = value₁ ; payVal = payVal₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl p2 p3 p4 p5 p6 p7) = p7 , p3 , p6

validStateTransition : ∀ {s s' : State} {i par}
  -> Valid s
  -> par ⊢ s ~[ i ]~> s'
  -> Valid s'
validStateTransition v (TUpdate x x₁ refl x₃ x₄ x₅ x₆ x₇ x₈) = x₃ , x₆ , x₈
validStateTransition (fst , snd , thd) (TExchange x refl x₂ x₃ x₄ x₅ x₆ x₇) = fst , x₅ , x₇


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
          ; tsig = owner (snd (datum s))
          ; continues = false
          ; spends = zero
          ; hasToken = false
          ; mint = -1
          ; token = fst (datum s)
          }



getS : Label -> ScriptContext -> State
getS (tok , lab) ctx = record
              { datum = (tok , lab)
              ; value = oldValue ctx
              ; payVal = 0
              ; tsig = 0 --sig ctx
              ; continues = true 
              ; spends = 0 --iRef ctx
              ; hasToken = checkTokenIn tok ctx
              ; mint = 0 --getMintedAmount ctx
              ; token = (0 , 0) --ownAssetClass ctx
              }


getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; payVal = 0
             ; tsig = sig ctx
             ; continues = continuing ctx
             ; spends = iRef ctx
             ; hasToken = checkTokenOut (ownAssetClass tn ctx) ctx
             ; mint = getMintedAmount ctx
             ; token = ownAssetClass tn ctx
             }

getS' : Label -> ScriptContext -> State
getS' (tok , lab) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; payVal = getPayment (owner lab) ctx
             ; tsig = sig ctx
             ; continues = continuing ctx
             ; spends = iRef ctx
             ; hasToken = checkTokenOut tok ctx
             ; mint = getMintedAmount ctx
             ; token = tok
             }




==Lto≡ : ∀ (l l' : Info)
       -> (l == l') ≡ true
       -> l ≡ l' 
==Lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf
  rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ owner owner' (go (ratio == ratio') pf) = refl
  
==dto≡ : {a b : Label} -> (a == b) ≡ true -> a ≡ b
==dto≡ {tok , l} {tok' , l'} p rewrite ==tto≡ tok tok' (get p) | ==Lto≡ l l' (go (tok == tok') p) = refl

getPar : Params -> Address -> TxOutRef -> TokenName -> MParams
getPar record { sellC = sellC ; buyC = buyC } adr oref tn = record
                                                          { address = adr
                                                          ; outputRef = oref
                                                          ; tokName = tn
                                                          ; sellC = sellC
                                                          ; buyC = buyC
                                                          } 


--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {adr oref tn} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Close
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> getPar par adr oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
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
  (get p2) (go (continuing ctx) (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r) (go (checkSigned (owner (snd d)) ctx)
  (go (checkTokenIn (d .fst) ctx) p2))))))) 
validatorImpliesTransition {adr} {oref} record { sellC = sellC ; buyC = buyC } (tok , lab) (Exchange amt pkh) ctx p1 p2
  = TExchange (==vto≡ (oldValue ctx) (addValue (newValue ctx) (assetClassValue sellC amt))
  (get (go (checkTokenIn tok ctx) p2)))
  (==dto≡ (get (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2))))
  (get (get (go (newDatum ctx == (tok , lab)) (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2)))))
  (go (ratioCompare amt (assetClassValueOf (getPayment (owner lab) ctx) buyC) (ratio lab))
  (get (go (newDatum ctx == (tok , lab)) (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2))))) refl
  (get (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2))))) (get p2)
  (go (continuing ctx) (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2)))))
validatorImpliesTransition par d Close ctx p1 p2 = ⊥-elim (p1 refl)




mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≢ -1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> getPar par adr oref tn ⊢ getMintS tn ctx
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 with getMintedAmount ctx == -1 in eq
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | True rewrite ==ito≡ mint' (negsuc 0) eq = ⊥-elim (p1 refl) --rewrite p1 = ⊥-elim (get⊥ eq)
mintingImpliesStart adr oref rn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | False with getMintedAmount ctx == 1 in eq'
mintingImpliesStart {record { sellC = sellC ; buyC = buyC }} adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokCurrSymbol = cs } p1 p2 | False | True rewrite sym (==tto≡ (cs , tn) tok (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))))
  = TStart refl (==ito≡ mint' (+ 1) eq') (get p2) (==to≡ oref inputRef (get (go (continues) p2)))
    refl (go (checkDatum adr tn ctx) (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))
    (go (ownAssetClass tn ctx == tok) (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))))
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | False | False = ⊥-elim (get⊥ (sym p2))


bothImplyClose : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref tn top ctx) ≡ true
               -> getPar par adr oref tn ⊢ getS d ctx ~[ Close ]~| getS' d ctx
bothImplyClose par d adr oref tn top ctx p with getMintedAmount ctx == 1 in eq
bothImplyClose par d adr oref tn top ctx p | True 
  = ⊥-elim (get⊥ (t=f (continuing ctx) (get (go (checkTokenIn (d .fst) ctx) (get p))) (get (go (agdaValidator par d Close ctx) p))))
bothImplyClose par d adr oref tn top ctx p | False with getMintedAmount ctx == -1 in eq'
bothImplyClose par d adr oref tn top ctx p | False | True
  = TClose (==to≡ (owner (snd d)) (sig ctx) (go (not (checkTokenOut (newDatum ctx .fst) ctx)) (go (not (continuing ctx))
    (go (checkTokenIn (d .fst) ctx) (get p))))) (==ito≡ (getMintedAmount ctx) (negsuc 0) eq') refl
    (unNot ((get (go ((checkTokenIn (d .fst) ctx)) (get p))))) (get (get p))
    (unNot (get (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p)))))
bothImplyClose par d adr oref tn top ctx p | False | False
  = ⊥-elim (get⊥ (sym (get {b = false} (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p)))))) 


≡to==l : ∀ {a b : Info} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl


transitionImpliesValidator : ∀ {adr oref tn} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
                           -> agdaValidator par d i ctx ≡ true
transitionImpliesValidator par d (Update v r) ctx (TUpdate refl refl refl p4 p5 p6 refl p8 p9)
  rewrite p4 | p5 | p6 | p6 | p8 | p9 | n=n (owner (d .snd)) | v=v v | t=t (d .fst) | i=i (num r) | i=i (den r) = p6
transitionImpliesValidator record { sellC = sellC ; buyC = buyC } d (Exchange amt pkh) ctx (TExchange refl refl p3 p4 p5 refl p7 p8 )
  rewrite p3 | p4 | p5 | p7 | p8 
    | v=v (addValue (newValue ctx) (MkMap ((sellC , amt) ∷ []))) 
    | t=t (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) = refl


startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getPar par adr oref tn ⊢ getMintS tn ctx
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting {record { sellC = sellC ; buyC = buyC }} adr oref tn top ctx (TStart refl refl refl refl p5 p6 p7)
  rewrite p5 | p6 | t=t (ownAssetClass tn ctx) | n=n oref | p7 = refl
  
closeImpliesBoth : ∀ (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
               -> getPar par adr oref tn ⊢ getS d ctx ~[ Close ]~| getS' d ctx
               -> ((agdaValidator par d Close ctx && agdaPolicy adr oref tn top ctx) ≡ true)
closeImpliesBoth par d adr oref tn top ctx (TClose refl refl refl refl p5 p6) rewrite p5 | p6 | n=n (owner (d .snd)) = refl


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



record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

Classifier : Argument -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } } = Initial
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Terminal



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
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Update x x₁) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Exchange x x₁) ctx (λ ()) p2
removeClose record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx) (negsuc 0) (get (go (not (continuing ctx)) (go (checkTokenIn (fst dat) ctx) p2)))))

totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } }} x → mintingImpliesStart {par} adr oref tn tt c (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } }} x → removeClose arg (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } }} x → removeClose arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Update a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Exchange a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = Close ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → bothImplyClose par dat adr oref tn tt c x }
                    ; from = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } }} x → transitionImpliesValidator par dat inp c x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } }} x → startImpliesMinting {par} adr oref tn tt c x  ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } }} x → transitionImpliesValidator par dat inp c x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } }} x → transitionImpliesValidator par dat inp c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Update a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Exchange a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = Close ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → closeImpliesBoth par dat adr oref tn tt c x } } 



