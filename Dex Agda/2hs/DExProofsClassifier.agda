open import DEx2

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


module DExProofsClassifier where



record State : Set where
  field
    datum      : Datum
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

data _⊢~[_]~>_ : MParams -> Input -> State -> Set where

  TStart : ∀ {par s l}
    -> datum s ≡ ((token s) , l)
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> hasToken s ≡ true
    -> checkRational (ratio l) ≡ true
    -------------------
    -> par ⊢~[ Start ]~>  s



data _⊢_~[_]~>_ : MParams -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {v r s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -> value s' ≡ v --record { amount = amt ; currency = sellC par }
    -> datum s' ≡ ((fst (datum s)) , (record { ratio = r ; owner = owner (snd (datum s)) })) 
    -> checkRational r ≡ true -- automate this maybe?
    -> checkMinValue v ≡ true
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Update v r) ]~> s'


  TExchange : ∀ {amt pkh s s' par}
    -> value s ≡ value s' <> assetClassValue (sellC par) amt --MkMap (((sellC par) , amt) ∷ []) --record { amount = amt ; currency = sellC par }
    -> datum s' ≡ datum s
    -> payTo s' ≡ owner (snd (datum s))
    -> ratioCompare amt (assetClassValueOf (payVal s') (buyC par)) (ratio (snd (datum s))) ≡ true
    --amt * num (ratio (label s)) ≤ payAmt (context s') * den (ratio (label s))
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
    

--Valid State
data ValidS : State -> Set where

  Stp : ∀ {s}
    -> continues s ≡ false
    ----------------
    -> ValidS s

  Oth : ∀ {s}
    -> checkRational (ratio (snd (datum s))) ≡ true
    ----------------
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


get⊥ : true ≡ false -> ⊥
get⊥ ()


--State Validity Invariant
validStateInitial : ∀ {i s par}
  -> par ⊢~[ i ]~> s
  -> ValidS s
validStateInitial {i} {record { datum = .(token₁ , _) ; value = value₁ ; payVal = payVal₁ ; payTo = payTo₁ ; buyVal = buyVal₁ ; buyTo = buyTo₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl p2 p3 p4 p5 p6) = Oth p6

validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition {s} {s' = record { datum = .(fst (datum s) , record { ratio = _ ; owner = owner (snd (datum s)) }) ; value = value₁ ; payVal = payVal₁ ; payTo = payTo₁ ; buyVal = buyVal₁ ; buyTo = buyTo₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} iv (TUpdate p1 p2 refl p4 p5 p6 p7 p8 p9) = Oth p4
validStateTransition (Stp x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite x = ⊥-elim (get⊥ (sym p9))
validStateTransition (Oth x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite sym p2 = Oth x
--validStateTransition iv (TClose p1 p2 p3 p4 p5) = Stp p3

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
validStateMulti iv (fin pf x) = validStateMulti (validStateFinal iv pf) x


liquidity : ∀ (par : MParams) (s : State) 
          -> ValidS s -> continues s ≡ true -> hasToken s ≡ true
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ MkMap []) )

liquidity par s (Stp x) p2 rewrite p2 = ⊥-elim (get⊥ x)
liquidity par s (Oth x) p2 p3 = ⟨ s' , ⟨  Close ∷ [] , (fin (TClose refl refl p2 refl p3 refl) root , refl) ⟩ ⟩
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


go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl


{-
rewriteMulCheck : ∀ (r : Rational) (ctx : ScriptContext) (val) ->
  ((mulInteger val (num r)) <= (mulInteger (payAmt ctx) (den r))) ≡ true ->
  (((sign val Sign.* sign (num r)) ◃ mulNat ∣ val ∣ ∣ num r ∣) ≤
  ((sign (payAmt ctx) Sign.* sign (den r)) ◃ mulNat ∣ payAmt ctx ∣ ∣ den r ∣))
rewriteMulCheck r ctx val p rewrite mul≡ val (num r) | mul≡ (payAmt ctx) (den r) = <=ito≤ p 
-}

getS : Datum -> ScriptContext -> State
getS d ctx = record
              { datum = d
              ; value = inputVal ctx
              ; payVal = MkMap [] --payVal ctx
              ; payTo = 0 --payTo ctx
              ; buyVal = MkMap [] --buyVal ctx
              ; buyTo = 0 --buyTo ctx
              ; tsig =  0 --signature ctx
              ; continues = true --continues ctx
              ; spends = 0 --inputRef ctx
              ; hasToken = (assetClassValueOf (inputVal ctx) (fst d)) == 1
              ; mint = 0 --mint ctx
              ; token =  0 --tokAssetClass ctx
              }

--capture what isn't needed
--capture what changes only slightly

{-
record ScriptContext : Set where
    field
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Datum
        payTo         : PubKeyHash
        payVal        : Value
        buyTo         : PubKeyHash
        buyVal        : Value
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokAssetClass : AssetClass
open ScriptContext public-}


getS' : ScriptContext -> State
getS' ctx = record
             { datum = outputDatum ctx
             ; value = outputVal ctx
             ; payVal = payVal ctx
             ; payTo = payTo ctx
             ; buyVal = buyVal ctx
             ; buyTo = buyTo ctx
             ; tsig = signature ctx
             ; continues = continues ctx
             ; spends = inputRef ctx
             ; hasToken = (assetClassValueOf (outputVal ctx) (fst (outputDatum ctx))) == 1
             ; mint = mint ctx
             ; token = tokAssetClass ctx
             }



==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p)

==ito≡ : ∀ {a b : Integer} -> (a == b) ≡ true -> a ≡ b
==ito≡ {(pos n)} {(pos m)} pf = cong +_ (==to≡ pf) --cong pos (==to≡ pf)
==ito≡ {(negsuc n)} {(negsuc m)} pf = cong negsuc (==to≡ pf) 

==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ {record { num = num ; den = den }} {record { num = num' ; den = den' }} pf
  rewrite ==ito≡ {num} {num'} (get pf) | ==ito≡ {den} {den'} (go (eqInteger num num') pf) = refl

unNot : ∀ {b : Bool} -> not b ≡ true -> b ≡ false
unNot {false} pf = refl

==pto≡ : {a b : (AssetClass × Integer)} -> (a == b) ≡ true -> a ≡ b
==pto≡ {ac , amt} {ac' , amt'} pf rewrite (==to≡ {ac} {ac'} (get pf)) | (==ito≡ {amt} {amt'} (go (ac == ac') pf)) = refl

==v'to≡ : {m m' : List (AssetClass × Integer)} -> (m == m') ≡ true -> m ≡ m'
==v'to≡ {[]} {[]} p = refl
==v'to≡ {x ∷ m} {y ∷ m'} pf rewrite (==pto≡ {x} {y} (get pf))= cong (λ z → y ∷ z) (==v'to≡ (go (x == y) pf))

==vto≡ : {a b : Value} -> (a == b) ≡ true -> a ≡ b
==vto≡ {MkMap x} {MkMap y} p = cong MkMap (==v'to≡ p)

==lto≡ : ∀ (l l' : Label)
       -> (l == l') ≡ true
       -> l ≡ l' 
==lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ {owner} {owner'} (go (ratio == ratio') pf) = refl

==dto≡ : {a b : Datum} -> (a == b) ≡ true -> a ≡ b
==dto≡ {tok , l} {tok' , l'} p rewrite ==to≡ {tok} {tok'} (get p) | ==lto≡ l l' (go (tok == tok') p) = refl

getPar : Params -> Address -> TxOutRef -> MParams
getPar record { sellC = sellC ; buyC = buyC } adr oref = record
                                                          { address = adr
                                                          ; outputRef = oref
                                                          ; sellC = sellC
                                                          ; buyC = buyC
                                                          }

--Validator returning true implies transition relation is inhabited

validatorImpliesTransition : ∀ {adr oref v r amt pkh} (par : Params) (d : Datum)
                               (i : Input) (ctx : ScriptContext)
                           -> i ≡ (Update v r) ⊎ i ≡ (Exchange amt pkh)
                           -> agdaValidator par d i ctx ≡ true
                           -> getPar par adr oref  ⊢ getS d ctx ~[ i ]~> getS' ctx


validatorImpliesTransition par d (Update v r) ctx p1 p2
  = TUpdate (==to≡ (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==vto≡ (get (go (checkMinValue v) (go (checkRational r) (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==dto≡ (get (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))
  (get (go (checkRational r) (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))) refl
  (get (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get p2) (subst (λ x -> checkTokenOut x ctx ≡ true)
  (sym (==to≡ {outputDatum ctx .fst} {d .fst} (get (get (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))))) 
  (go (continuing ctx) (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))))
validatorImpliesTransition par d (Exchange amt pkh) ctx p1 p2
  = TExchange (==vto≡ (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==dto≡ (get (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))
  (==to≡ (get (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (get (go (payTo ctx == owner (d .snd)) (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (go (ratioCompare amt (assetClassValueOf (payVal ctx) (buyC par)) (ratio (snd d))) (go (payTo ctx == owner (d .snd))
  (get (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==to≡ (get (get (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (==ito≡ (get (go (buyTo ctx == pkh) (get (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))))
  (go (assetClassValueOf (buyVal ctx) (sellC par) == amt) (go (buyTo ctx == pkh) (get (go (checkPayment par amt (d .snd) ctx)
  (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))) refl
  (get (go (checkBuyer par amt pkh ctx) (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))
  (get p2) (subst (λ x -> checkTokenOut x ctx ≡ true)
  (sym (==to≡ {outputDatum ctx .fst} {d .fst} (get (get (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt))
  (go (checkTokenIn (d .fst) ctx) p2))))))
  (go (continuing ctx) ((go (checkBuyer par amt pkh ctx) (go (checkPayment par amt (d .snd) ctx) (go (newDatum ctx == ((d .fst) , (d .snd)))
  (go (oldValue ctx == newValue ctx <> (assetClassValue (sellC par) amt)) (go (checkTokenIn (d .fst) ctx) p2))))))))
validatorImpliesTransition par d Close ctx (inj₁ ()) p2
validatorImpliesTransition par d Close ctx (inj₂ ()) p2
validatorImpliesTransition par d Start ctx p1 p2 = ⊥-elim (get⊥ (sym (go (checkTokenIn (d .fst) ctx) p2))) 



mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
                           -> (pf : agdaPolicy adr oref Start ctx ≡ true)
                           -> getPar par adr oref ⊢~[ Start ]~>  getS' ctx


mintingImpliesStart adr oref ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } p1 rewrite ==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p1)))))
  = TStart refl (==ito≡ (go (isInitial adr oref ctx) (go (continuingAddr adr ctx) p1))) (get p1)
    (==to≡ (get (get (go (continuingAddr adr ctx) p1))))
    (subst (λ x -> checkTokenOut x ctx ≡ true ) (==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p1))))))
    (go (checkDatum adr ctx) (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p1)))))
    (go (ownAssetClass ctx == tok) (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p1)))))

{-
mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (i : Input) (ctx : ScriptContext)
                           -> i ≡ Start
                           -> (pf : agdaPolicy adr oref i ctx ≡ true)
                           -> getPar par adr oref ⊢~[ i ]~>  getS' ctx
mintingImpliesStart adr oref Close ctx () p2
mintingImpliesStart adr oref Start ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } p1 p2 rewrite ==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p2)))))
  = TStart refl (==ito≡ (go (isInitial adr oref ctx) (go (continuingAddr adr ctx) p2))) (get p2)
    (==to≡ (get (get (go (continuingAddr adr ctx) p2))))
    (subst (λ x -> checkTokenOut x ctx ≡ true ) (==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p2))))))
    (go (checkDatum adr ctx) (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p2)))))
    (go (ownAssetClass ctx == tok) (get (go (consumes oref ctx) (get (go (continuingAddr adr ctx) p2)))))
-}
{-
consumes oref ctx &&
                          checkDatum addr ctx &&
(get (go (consumes oref ctx) (go (continuingAddr adr ctx) {!p2!}))))
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 with mint ctx == -1 in eq
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | True rewrite ==ito≡ {mint'} {negsuc 0} eq = ⊥-elim (p1 refl) --rewrite p1 = ⊥-elim (get⊥ eq)
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False with mint ctx == 1 in eq'
mintingImpliesStart adr oref top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False | True rewrite ==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) {!!})))) = {!!}
{-TStart refl (==ito≡ eq') (get p2) (==to≡ (get (go (continues) p2)))
                  (subst (λ x -> checkTokenOut x ctx ≡ true ) (==to≡ (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))))
                  (go (checkDatum adr ctx) (go (consumes oref ctx)
                  (go (continuingAddr adr ctx) p2))))
                  (go (ownAssetClass ctx == tok)
                  (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))) -}
mintingImpliesStart adr oref i ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokAssetClass = tokAssetClass } p1 p2 | False | False = {!!} -}
--⊥-elim (get⊥ (sym {!!}))

--= TStart {!!} {!!} {!!} {!!} {!!} {!!}

--rewrite ==to≡ {tokAssetClass} {tok} (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) {!!}))))
                 -- = {!!}
                  {-TStart refl ? (get p2) (==to≡ (get (go (continues) p2)))
                  (subst (λ x -> checkTokenOut x ctx ≡ true ) (==to≡ (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))))
                  (go (checkDatum adr ctx) (go (consumes oref ctx)
                  (go (continuingAddr adr ctx) p2))))
                  (go (ownAssetClass ctx == tok)
                  (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))))-}
                  


t=f : ∀ (a : Bool) -> not a ≡ true -> a ≡ true -> true ≡ false
t=f false p1 p2 = sym p2
t=f true p1 p2 = sym p1


bothImplyClose : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
               -> (agdaValidator par d Close ctx && agdaPolicy adr oref Close ctx) ≡ true
               -> getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx
               
bothImplyClose par d adr oref ctx p
  = TClose (==to≡ (go (not (checkTokenOut (newDatum ctx .fst) ctx)) (go (eqInteger (mint ctx) (negsuc 0))
    (go (not (continues ctx)) (go (eqInteger (assetClassValueOf (inputVal ctx) (fst d)) (+ 1)) (get p))))))
    (==ito≡ (go (not (continues ctx)) (go (agdaValidator par d Close ctx) p))) refl (unNot (get (go (agdaValidator par d Close ctx) p)))
    (get (get p)) (unNot (get (go (eqInteger (mint ctx) (negsuc 0))
    (go (not (continues ctx)) (go (eqInteger (assetClassValueOf (inputVal ctx) (fst d)) (+ 1)) (get p))))))

{-
bothImplyClose : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (i : Input) (ctx : ScriptContext)
               -> (agdaValidator par d i ctx && agdaPolicy adr oref i ctx) ≡ true
               -> getPar par adr oref ⊢ getS d ctx ~[ i ]~| getS' ctx
bothImplyClose par d adr oref (Update x x₁) ctx p = ⊥-elim (get⊥ (sym (go (agdaValidator par d (Update x x₁) ctx) p)))
bothImplyClose par d adr oref (Exchange x x₁) ctx p = ⊥-elim (get⊥ (sym (go (agdaValidator par d (Exchange x x₁) ctx) p)))
bothImplyClose par d adr oref Close ctx p
  = TClose (==to≡ (go (not (checkTokenOut (newDatum ctx .fst) ctx)) (go (eqInteger (mint ctx) (negsuc 0))
    (go (not (continues ctx)) (go (eqInteger (assetClassValueOf (inputVal ctx) (fst d)) (+ 1)) (get p))))))
    (==ito≡ (go (not (continues ctx)) (go (agdaValidator par d Close ctx) p))) refl (unNot (get (go (agdaValidator par d Close ctx) p)))
    (get (get p)) (unNot (get (go (eqInteger (mint ctx) (negsuc 0))
    (go (not (continues ctx)) (go (eqInteger (assetClassValueOf (inputVal ctx) (fst d)) (+ 1)) (get p))))))
bothImplyClose par d adr oref Start ctx p = ⊥-elim (get⊥ (sym (go (checkTokenIn (d .fst) ctx) (get p))))
-}
{-
not (continuing ctx) && checkTokenBurned tok ctx &&
           not (checkTokenOut (newDatum ctx .fst) ctx) && checkSigned (owner lab) ctx 

bothImplyClose par d adr oref top ctx p with mint ctx == 1 in eq
bothImplyClose par d adr oref top ctx p | True 
  = ⊥-elim (get⊥ (t=f (continues ctx) (get (go (checkTokenIn (d .fst) ctx) (get p))) (get (go (agdaValidator par d Close ctx) p))))
bothImplyClose par d adr oref top ctx p | False with mint ctx == -1 in eq'
bothImplyClose par d adr oref top ctx p | False | True
  = TClose (==to≡ (go (not (checkTokenOut (newDatum ctx .fst) ctx)) (go (not (continuing ctx))
    (go (checkTokenIn (d .fst) ctx) (get p))))) (==ito≡ eq') refl
    (unNot (get (go ((checkTokenIn (d .fst) ctx)) (get p)))) (get (get p))
    (unNot (get (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p)))))
bothImplyClose par d adr oref top ctx p | False | False
  = ⊥-elim (get⊥ (sym (go (eqInteger (assetClassValueOf (inputVal ctx) (d .fst)) (+ 1)
         && not (continues ctx) && false) p)))-}

--⊥-elim (neq (==ito≡ eq)) -- TClose {!!} {!!} {!!} {!!} {!!} {!!}

≡to== : ∀ {a b : Nat} -> a ≡ b -> (a == b) ≡ true
≡to== {zero} refl = refl
≡to== {suc a} refl = ≡to== {a} refl

n=n : ∀ (n : Nat) -> (n == n) ≡ true
n=n zero = refl
n=n (suc n) = n=n n

≡to==i : ∀ {a b : Integer} -> a ≡ b -> (a == b) ≡ true
≡to==i {pos n} refl = n=n n
≡to==i {negsuc n} refl = n=n n

i=i : ∀ (i : Int) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = n=n n 
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = n=n n

≡to==l : ∀ {a b : Label} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl

lst=lst : ∀ (lst : List (Nat × Integer)) -> (lst == lst) ≡ true
lst=lst [] = refl
lst=lst (x ∷ lst) rewrite n=n (x .fst) | i=i (x .snd) = lst=lst lst

v=v : ∀ (v : Value) -> (v == v) ≡ true
v=v (MkMap x) = lst=lst x



transitionImpliesValidator : ∀ {adr oref v r amt pkh} (par : Params) (d : Datum)
                               (i : Input) (ctx : ScriptContext)
                           -> i ≡ (Update v r) ⊎ i ≡ (Exchange amt pkh)
                           -> getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
                           -> agdaValidator par d i ctx ≡ true


transitionImpliesValidator par d (Update v r) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } p (TUpdate refl refl refl p4 p5 p6 refl p8 p9)
  rewrite p4 | p5 | p6 | p6 | p8 | p9 | n=n (owner (d .snd)) | v=v v | n=n (d .fst) | i=i (num r) | i=i (den r) = p6
transitionImpliesValidator par d (Exchange amt pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } p (TExchange refl refl refl p4 p5 refl refl p8 p9 refl p11 p12)
  rewrite p4 | p5 | p8 | p9 | p11 | p12
    | v=v (addValue outputVal (MkMap ((sellC par , assetClassValueOf buyVal (sellC par)) ∷ []))) 
    | n=n (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) | n=n pkh | i=i (assetClassValueOf buyVal (sellC par)) = p9

{-
transitionImpliesValidator : ∀ {adr oref} (par : Params) (d : Datum) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
                           -> agdaValidator par d i ctx ≡ true
transitionImpliesValidator par d (Update v r) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TUpdate refl refl refl p4 p5 p6 refl p8 p9)
  rewrite p4 | p5 | p6 | p6 | p8 | p9 | n=n (owner (d .snd)) | v=v v | n=n (d .fst) | i=i (num r) | i=i (den r) = p6
transitionImpliesValidator par d (Exchange amt pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TExchange refl refl refl p4 p5 refl refl p8 p9 refl p11 p12)
  rewrite p4 | p5 | p8 | p9 | p11 | p12
    | v=v (addValue outputVal (MkMap ((sellC par , assetClassValueOf buyVal (sellC par)) ∷ []))) 
    | n=n (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) | n=n pkh | i=i (assetClassValueOf buyVal (sellC par)) = p9
-}


startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢~[ Start ]~> getS' ctx
                           -> agdaPolicy adr oref Start ctx ≡ true
                           
startImpliesMinting adr oref record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TStart refl refl refl refl p5 p6) rewrite p5 | p6 | n=n oref | n=n tokAssetClass = refl 

{-
startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢~[ i ]~> getS' ctx
                           -> agdaPolicy adr oref i ctx ≡ true
startImpliesMinting adr oref i record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TStart refl refl refl refl p5 p6) rewrite p5 | p6 | n=n oref | n=n tokAssetClass = refl 
-}


closeImpliesBoth : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
               -> getPar par adr oref ⊢ getS d ctx ~[ Close ]~| getS' ctx
               -> ((agdaValidator par d Close ctx && agdaPolicy adr oref Close ctx) ≡ true)


closeImpliesBoth par d adr oref record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TClose refl refl refl refl p5 p6) rewrite p5 | p6 | n=n (owner (d .snd)) = refl

{-
closeImpliesBoth : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (i : Input) (ctx : ScriptContext)
               -> getPar par adr oref ⊢ getS d ctx ~[ i ]~| getS' ctx
               -> ((agdaValidator par d i ctx && agdaPolicy adr oref i ctx) ≡ true)
closeImpliesBoth par d adr oref i record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokAssetClass = tokAssetClass } (TClose refl refl refl refl p5 p6) rewrite p5 | p6 | n=n (owner (d .snd)) = refl --refl , refl
-}

--AParam = 

--Argument = Params × Address × TxOutRef × Datum × Input × ScriptContext

 -- (v : Value) (r : Rational) (amt : Integer) (pkh : PubKeyHash)

record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


--write as 3 predicates
data Argument : Set where
  Initial : ∀ (par : Params) (adr : Address)
              (oref : TxOutRef) (d : Datum)
              (i : Input) (ctx : ScriptContext)
    -> i ≡ Start --p1
    ----------------
    -> Argument

  Running : ∀ {v r amt pkh}
              (par : Params) (adr : Address)
              (oref : TxOutRef) (d : Datum)
              (i : Input) (ctx : ScriptContext)        
    -> i ≡ (Update v r) ⊎ i ≡ (Exchange amt pkh) --p2
    ----------------
    -> Argument

  Final : ∀ (par : Params) (adr : Address)
            (oref : TxOutRef) (d : Datum)
            (i : Input) (ctx : ScriptContext)
    -> i ≡ Close --p3
    ----------------
    -> Argument


--exactly 1 holds

--input -> classifier one of 3 things
--then ... with Classifier i
--think about it

totalF : Argument -> Bool
totalF (Initial par adr oref d i ctx x) = agdaPolicy adr oref i ctx
totalF (Running par adr oref d i ctx x) = agdaValidator par d i ctx
totalF (Final par adr oref d i ctx x) = agdaValidator par d i ctx && agdaPolicy adr oref i ctx

--make adr + oref into mintParam

totalR : Argument -> Set
totalR (Initial par adr oref d i ctx x) = getPar par adr oref ⊢~[ i ]~> getS' ctx
totalR (Running par adr oref d i ctx x) = getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
totalR (Final par adr oref d i ctx x) = getPar par adr oref ⊢ getS d ctx ~[ i ]~| getS' ctx

totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {Initial par adr oref d .Start ctx refl} x → mintingImpliesStart adr oref ctx x ;
                               {Running par adr oref d i ctx p} x → validatorImpliesTransition par d i ctx p x ;
                               {Final par adr oref d .Close ctx refl} x → bothImplyClose par d adr oref ctx x } ;
                    from = λ { {Initial par adr oref d .Start ctx refl} x → startImpliesMinting adr oref ctx x ;
                               {Running par adr oref d i ctx p} x → transitionImpliesValidator par d i ctx p x ;
                               {Final par adr oref d .Close ctx refl} x → closeImpliesBoth par d adr oref ctx x } }


data Phase : Set where
  Initial : Phase
  Running : Phase
  Final   : Phase

record Argument' : Set where
  field
    par  : Params
    adr  : Address
    oref : TxOutRef
    dat  : Datum
    inp  : Input
    ctx  : ScriptContext 
open Argument'

Classifier : Argument' -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Update x x₁) ; ctx = ctx } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = (Exchange x x₁) ; ctx = ctx } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx } = Final
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Start ; ctx = ctx } = Initial

totalF' : Argument' -> Bool
totalF' arg with Classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) (arg .inp) (arg .ctx)
... | Running = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) 
... | Final = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) &&
              agdaPolicy (arg .adr) (arg .oref) (arg .inp) (arg .ctx)

totalR' : Argument' -> Set
totalR' arg with Classifier arg
... | Initial = getPar (arg .par) (arg .adr) (arg .oref) ⊢~[ (arg .inp) ]~> getS' (arg .ctx)
... | Running = getPar (arg .par) (arg .adr) (arg .oref) ⊢
                       getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx) 
... | Final = getPar (arg .par) (arg .adr) (arg .oref) ⊢
                       getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .ctx) 


tE' : totalF' ≈ totalR'
tE' = record { to = λ { {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Update v r ; ctx = ctx }} x →
                        validatorImpliesTransition {amt = 0} {pkh = 0} par dat (Update v r) ctx (inj₁ refl) x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Exchange amt pkh ; ctx = ctx }} x →
                        validatorImpliesTransition {v = MkMap []} {r = record { num = 0 ; den = 0 }} par dat (Exchange amt pkh) ctx (inj₂ refl) x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx }} x →
                        bothImplyClose par dat adr oref ctx x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Start ; ctx = ctx }} x →
                        mintingImpliesStart adr oref ctx x } ; 
               from = λ { {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Update v r ; ctx = ctx }} x →
                        transitionImpliesValidator {amt = 0} {pkh = 0} par dat (Update v r) ctx (inj₁ refl) x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Exchange amt pkh ; ctx = ctx }} x →
                        transitionImpliesValidator {v = MkMap []} {r = record { num = 0 ; den = 0 }} par dat (Exchange amt pkh) ctx (inj₂ refl) x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Close ; ctx = ctx }} x →
                        closeImpliesBoth par dat adr oref ctx x ;
                        {record { par = par ; adr = adr ; oref = oref ; dat = dat ; inp = Start ; ctx = ctx }} x →
                        startImpliesMinting adr oref ctx x } }





{-
totalF : Argument -> Bool
totalF (par , adr , oref , d , i@(Update v r) , ctx) = agdaValidator par d i ctx
totalF (par , adr , oref , d , i@(Exchange amt pkh) , ctx) = agdaValidator par d i ctx
totalF (par , adr , oref , d , i@Close , ctx) = agdaValidator par d i ctx && agdaPolicy adr oref i ctx
totalF (par , adr , oref , d , i@Start , ctx) = agdaPolicy adr oref i ctx

totalR : Argument -> Set
totalR (par , adr , oref , d , i@(Update v r) , ctx) = getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
totalR (par , adr , oref , d , i@(Exchange amt pkh) , ctx) = getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx
totalR (par , adr , oref , d , i@Close , ctx) = getPar par adr oref ⊢ getS d ctx ~[ i ]~| getS' ctx
totalR (par , adr , oref , d , i@Start , ctx) = getPar par adr oref ⊢~[ i ]~> getS' ctx

totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ{ {par , adr , oref , d , i@(Update v r) , ctx} x → validatorImpliesTransition par d i ctx (λ ()) x ;
                              {par , adr , oref , d , i@(Exchange amt pkh) , ctx} x → validatorImpliesTransition par d i ctx (λ ()) x ;
                              {par , adr , oref , d , i@Close , ctx} x → bothImplyClose par d adr oref i ctx x ;
                              {par , adr , oref , d , i@Start , ctx} x → mintingImpliesStart adr oref i ctx (λ ()) x } ;
                      from = λ{ {par , adr , oref , d , i@(Update v r) , ctx} x → transitionImpliesValidator par d i ctx x ;
                                {par , adr , oref , d , i@(Exchange amt pkh) , ctx} x → transitionImpliesValidator par d i ctx x ;
                                {par , adr , oref , d , i@Close , ctx} x → closeImpliesBoth par d adr oref i ctx x ;
                                {par , adr , oref , d , i@Start , ctx} x → startImpliesMinting adr oref i ctx x } }

-}


---------------------------------------------
{-

runtimeF : Argument -> Bool
runtimeF (par , adr , oref , d , i@(Update x x₁) , ctx) = agdaValidator par d i ctx
runtimeF (par , adr , oref , d , i@(Exchange x x₁) , ctx) = agdaValidator par d i ctx
runtimeF (par , adr , oref , d , Close , ctx) = false

runtimeR : Argument -> Set
runtimeR (par , adr , oref , d , i , ctx) = getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' ctx

runtimeEquiv : runtimeF ≈ runtimeR
runtimeEquiv = record { to = λ { {par , adr , oref , d , Update x₁ x₂ , ctx} x → validatorImpliesTransition par d (Update x₁ x₂) ctx (λ ()) x ; {par , adr , oref , d , Exchange x₁ x₂ , ctx} x → validatorImpliesTransition par d (Exchange x₁ x₂) ctx (λ ()) x } ; from = λ { {par , adr , oref , d , Update x₁ x₂ , ctx} x → transitionImpliesValidator par d (Update x₁ x₂) ctx x ; {par , adr , oref , d , Exchange x₁ x₂ , ctx} x → transitionImpliesValidator par d (Exchange x₁ x₂) ctx x }}

startF : Argument -> Bool
startF (par , adr , oref , d , i , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = (+_ n) ; tokAssetClass = tokAssetClass₁ }) = agdaPolicy adr oref tt ctx
startF (par , adr , oref , d , i , record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = negsuc zero ; tokAssetClass = tokAssetClass₁ }) = false
startF (par , adr , oref , d , i , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = negsuc (N.suc n) ; tokAssetClass = tokAssetClass₁ }) = agdaPolicy adr oref tt ctx

startR : Argument -> Set
startR (par , adr , oref , d , i , ctx) = getPar par adr oref ⊢ getS' ctx

startEquiv : startF ≈ startR
startEquiv = record { to = λ { {par , adr , oref , d , i , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = (+_ n) ; tokAssetClass = tokAssetClass₁ }} x → mintingImpliesStart adr oref tt ctx (λ ()) x ; {par , adr , oref , d , i , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = negsuc (N.suc n) ; tokAssetClass = tokAssetClass₁ }} x → mintingImpliesStart adr oref tt ctx (λ ()) x} ; from = λ { {par , adr , oref , d , i , ctx} p@(TStart x refl x₂ x₃ x₄ x₅) → startImpliesMinting adr oref tt ctx p } }

finalF : Argument -> Bool
finalF (par , adr , oref , d , Update x x₁ , ctx) = false
finalF (par , adr , oref , d , Exchange x x₁ , ctx) = false
finalF (par , adr , oref , d , Close , ctx) = agdaValidator par d Close ctx && agdaPolicy adr oref tt ctx

{-
finalF (par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = +_ zero ; tokAssetClass = tokAssetClass₁ }) = agdaValidator par d Close ctx && agdaPolicy adr oref tt ctx
finalF (par , adr , oref , d , Close , record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass₁ }) = false
finalF (par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass₁ }) = agdaValidator par d Close ctx && agdaPolicy adr oref tt ctx
finalF (par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = negsuc n ; tokAssetClass = tokAssetClass₁ }) = agdaValidator par d Close ctx && agdaPolicy adr oref tt ctx-}

finalR : Argument -> Set
finalR (par , adr , oref , d , i , ctx) = getPar par adr oref ⊢ getS d ctx ~[ i ]~| getS' ctx

finalEquiv : finalF ≈ finalR
finalEquiv = record { to = λ { {par , adr , oref , d , Close , ctx} x → bothImplyClose par d adr oref tt ctx x} ; from = λ { {par , adr , oref , d , Close , ctx} x →  closeImpliesBoth par d adr oref tt ctx x } }
{-record { to = λ { {par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = +_ zero ; tokAssetClass = tokAssetClass₁ }} x → bothImplyClose par d adr oref tt ctx (λ ()) x ; {par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass₁ }} x → bothImplyClose par d adr oref tt ctx (λ ()) x ; {par , adr , oref , d , Close , ctx@record { inputVal = inputVal₁ ; outputVal = outputVal₁ ; outputDatum = outputDatum₁ ; payTo = payTo₁ ; payVal = payVal₁ ; buyTo = buyTo₁ ; buyVal = buyVal₁ ; signature = signature₁ ; continues = continues₁ ; inputRef = inputRef₁ ; mint = negsuc n ; tokAssetClass = tokAssetClass₁ }} x → bothImplyClose par d adr oref tt ctx (λ ()) x } ; from = λ { {par , adr , oref , d , Close , ctx} p@(TClose refl refl refl refl x x') → closeImpliesBoth par d adr oref tt ctx p } }
-}

totalR : Argument -> Set
totalR (par , adr , oref , d , i , record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +_ zero ; tokAssetClass = tokAssetClass }) = {!!}
totalR (par , adr , oref , d , i , record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ n ] ; tokAssetClass = tokAssetClass }) = {!!}
totalR (par , adr , oref , d , i , record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = negsuc zero ; tokAssetClass = tokAssetClass }) = {!!}
totalR (par , adr , oref , d , i , record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; payTo = payTo ; payVal = payVal ; buyTo = buyTo ; buyVal = buyVal ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = negsuc (N.suc n) ; tokAssetClass = tokAssetClass }) = {!!}
-}

