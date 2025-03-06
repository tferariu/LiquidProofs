open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)


module MultiSigTransition where


magic : {A : Set} → ⊥ → A
magic ()

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

PubKeyHash = String
Value = Nat
Deadline = Integer

data Label : Set where
  Holding : Label
  Collecting : Value -> PubKeyHash -> Deadline -> List PubKeyHash -> Label

record TxInfo : Set where
  field
    txInfoInputs                : Placeholder --[V2.TxInInfo]
    txInfoReferenceInputs       : Nat --[V2.TxInInfo]
    txInfoOutputs               : Placeholder --[V2.TxOut]
    txInfoValidRange            : POSIXTimeRange
    txInfoSignatories           : Placeholder --[V2.PubKeyHash]
    txInfoRedeemers             : Nat --Map ScriptPurpose V2.Redeemer
    txInfoData                  : Nat --Map V2.DatumHash V2.Datum
    txInfoId                    : Nat --V2.TxId
    payTo  : PubKeyHash
    payAmt : Value
    
open TxInfo public

record ScriptContext : Set where
    field
 --       scriptContextTxInfo  : TxInfo
 --       scriptContextPurpose : ScriptPurpose
        inputVal    : Nat
        outputVal   : Nat
        outputLabel : Label
        
open ScriptContext public



{-# COMPILE AGDA2HS Deadline #-}



{-# COMPILE AGDA2HS Label #-}
 
data Input : Set where
  Propose : Value -> PubKeyHash -> Deadline -> Input
  Add     : PubKeyHash -> Input
  Pay     : Input
  Cancel  : Input

{-# COMPILE AGDA2HS Input #-}

query : PubKeyHash -> List PubKeyHash -> Bool
query pkh [] = False
query pkh (x ∷ l') = (x == pkh) || query pkh l'

check : List Input -> Bool
check (Pay ∷ is) = False
check (_ ∷ is) = check is
check [] = True

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

count : List PubKeyHash -> Integer
count [] = 0
count (x ∷ l) = 1 + (count l)

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS count #-}

{-
postulate
 -- txSignedBy : TxInfo -> PubKeyHash -> Bool
  checkSigned : PubKeyHash -> ScriptContext -> Bool
  checkPayment : PubKeyHash -> Value -> TxInfo -> Bool
  expired : Deadline -> TxInfo -> Bool
  newLabel : ScriptContext -> Label
  oldValue : ScriptContext -> Value
  -- postulate foreign block
  newValue : ScriptContext -> Value
  geq : Value -> Value -> Bool
--  checkToken : ThreadToken -> ScriptContext -> Bool -}

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned _ _ = True

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment _ _ _ = True

expired : Deadline -> ScriptContext -> Bool
expired _ _ = True

newLabel : ScriptContext -> Label
newLabel ctx = outputLabel ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

geq : Value -> Value -> Bool
geq _ _ = True



data _∉_ : PubKeyHash -> List PubKeyHash -> Set where

  empty : ∀ {pkh : PubKeyHash}
    ------------
    -> pkh ∉ []

  cons : ∀ { pkh pkh' l }
    -> pkh ≠ pkh'
    -> pkh ∉ l
    ---------------
    -> pkh ∉ (pkh' ∷ l)
  

data Unique : List PubKeyHash → Set where
  [] : Unique []
  _::_ : {x : PubKeyHash} {l : List PubKeyHash} → x ∉ l → Unique l → Unique (x ∷ l)


record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
        pfU : Unique authSigs
        pfL : IsTrue ((lengthNat authSigs) > nr)
open Params public

{-# COMPILE AGDA2HS Params #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param oldLabel red ctx = case oldLabel of λ where
  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && (pkh == pkh' && (d == d' && (sigs' == insert sig sigs ))) )

    Pay -> (lengthNat sigs) >= (nr param) && (case (newLabel ctx) of λ where
      Holding -> checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v)
      (Collecting _ _ _ _) -> False )
      
    Cancel -> newValue ctx == oldValue ctx && (case (newLabel ctx) of λ where
      Holding -> expired d ctx
      (Collecting _ _ _ _) -> False ) 
  
  Holding -> case red of λ where

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && (v > 0) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> (v == v' && (pkh == pkh' && (d == d' && (sigs' == [])))) )
    (Add _) -> False
    Pay -> False
    Cancel -> False

{-# COMPILE AGDA2HS agdaValidator #-}

data _∻_ : Label -> Value -> Set where

  Hol : ∀ {v}
    ----------------
    -> Holding ∻ v

  Col : ∀ {val v pkh d sigs}
    -> IsTrue (val >= v)
    -> IsTrue (v > 0) --IsFalse (val <= v) --IsTrue (val >= v)
    --------------------------------
    -> (Collecting v pkh d sigs) ∻ val


record State : Set where
  field
    label : Label
    value : Value
 --   param : Params      --remove
 --   pfP : IsNonNegativeInteger value
 --   pfG : label ∻ value  -- remove this
    
open State



module Liquidity (p : Params) where

  data _~[_]~>_ : State -> Input -> State -> Set where

    TPropose : ∀ {v pkh d val}
      -> IsTrue (val >= v)
      -> IsTrue (v > 0)
      -------------------
      -> record { label = Holding ; value = val }
         ~[ (Propose v pkh d) ]~>
         record { label = Collecting v pkh d [] ; value = val}
      

    TAdd : ∀ {v pkh d sig sigs val}
      -> IsTrue (query sig (authSigs p) )
      -------------------
      -> record { label = (Collecting v pkh d sigs) ; value = val }
         ~[ (Add sig) ]~>
         record { label = (Collecting v pkh d (insert sig sigs)) ; value = val }

    TPay : ∀ {v pkh d sigs val val'}
      -> val ≡ val' + v
      -> IsTrue (lengthNat sigs >= (nr p))
      -------------------
      -> record { label = Collecting v pkh d sigs ; value = val}
         ~[ Pay ]~>
         record { label = Holding ; value = val' }

    TCancel : ∀ {v pkh d sigs val}
      -------------------
      -> record { label = Collecting v pkh d sigs ; value = val }
         ~[ Cancel ]~>
         record { label = Holding ; value = val}


  data _~[_]~*_ : State -> List Input -> State -> Set where

    root : ∀ { s }
      ------------------
      -> s ~[ [] ]~* s

    cons : ∀ (s' : State) { s i is s'' }
      -> s ~[ i ]~> s'
      -> s' ~[ is ]~* s''
      -----------------------
      -> s ~[ (i ∷ is) ]~* s''



  validStateTransition : ∀ {s s' : State} {i}
    -> label s ∻ value s
    -> s ~[ i ]~> s'
    -> label s' ∻ value s'
  validStateTransition iv (TPropose x y) = Col x y
  validStateTransition (Col x₁ x₂) (TAdd x) = Col x₁ x₂
  validStateTransition iv (TPay x x₁) = Hol
  validStateTransition iv TCancel = Hol

  validStateMulti : ∀ {s s' : State} {is}
    -> label s ∻ value s
    -> s ~[ is ]~* s'
    -> label s' ∻ value s'
  validStateMulti iv root = iv
  validStateMulti iv (cons s' x tr) = validStateMulti (validStateTransition iv x) tr

  invariant2 : ∀ {s s' : State} {i}
    -> IsTrue (value s > 0)
    -> s ~[ i ]~> s'
    -> i ≠ Pay
    -> IsTrue (value s' > 0)
  invariant2 iv (TPropose x x₁) pf = iv
  invariant2 iv (TAdd x) pf = iv
  invariant2 iv (TPay x x₁) pf = magic (pf refl)
  invariant2 iv TCancel pf = iv

  invariant2Multi : ∀ {s s' : State} {is}
    -> IsTrue (value s > 0)
    -> s ~[ is ]~* s'
    -> IsTrue (check is)
    -> IsTrue (value s' > 0)
  invariant2Multi iv root pf = iv
  invariant2Multi iv (cons s' {i = Propose x₁ x₂ x₃} x t) pf = invariant2Multi (invariant2 iv x λ ()) t pf
  invariant2Multi iv (cons s' {i = Add x₁} x t) pf = invariant2Multi (invariant2 iv x λ ()) t pf
  invariant2Multi iv (cons s' {i = Cancel} x t) pf = invariant2Multi (invariant2 iv x λ ()) t pf

--invariant2Multi (invariant2 iv x {!!}) t {!!}

{-
  makeIs : Params -> List Input
  makeIs record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = []
  makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = Add x ∷ (makeIs (record
                                                                                                            { authSigs = authSigs
                                                                                                            ; nr = nr
                                                                                                            ; pfU = pfU 
                                                                                                            ; pfL = pfL
                                                                                                            }) ) 


  prop1 : ∀ { v pkh d sigs val } -> (par : Params) -> ∃[ sigs' ] record { label = (Collecting v pkh d sigs) ; value = val } ~[ makeIs par ]~* record { label = (Collecting v pkh d sigs') ; value = val }
  prop1 {sigs = sigs} record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = ⟨ sigs , root ⟩
  prop1 {v} {pkh} {d} {sigs} {val} record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = ⟨ {!!} , (cons ( record { label = (Collecting v pkh d (insert x sigs)) ; value = val }) (TAdd {!!}) {!!}) ⟩ 

  prop1' : ∀ { v pkh d sigs val } -> ∃[ sigs' ] record { label = (Collecting v pkh d sigs) ; value = val } ~[ makeIs p ]~* record { label = (Collecting v pkh d sigs') ; value = val }
  prop1' = prop1 p
  -}
{-
  lema : ∀ (s : State) -> ∃[ s' ] (s ~[ makeIs p ]~* s')
  lema record { label = Holding ; value = value } = {!!}
  lema record { label = (Collecting v pkh d sigs) ; value = value } = ⟨ (record { label = (Collecting v pkh d sigs) ; value = value }) , {!!} ⟩
-}

  liq : ∀ (s : State) ->  ∃[ s' ] ∃[ is ] (s ~[ (is ++ (Pay ∷ [])) ]~* s')
  liq s = {!!}

  liquidity : ∀ (s : State) -> label s ∻ value s -> IsTrue (value s > 0) -> ∃[ s' ] ∃[ is ] (s ~[ (is ++ (Pay ∷ [])) ]~* s')
  liquidity record { label = Holding ; value = (suc value₁) } pf1 pf2 = {!!} --⟨ {!!} , ⟨ {!!} , (cons {!!} (TPropose {!!} {!!}) (cons {!!} (TAdd {!!}) {!!})) ⟩ ⟩
  liquidity record { label = (Collecting x x₁ x₂ x₃) ; value = value } pf1 pf2 = {!!}

  prop' : ∀ {s i s'} -> s ~[ i ]~*  s'
  prop' = {!!}

-- authSigs


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


open Liquidity

makeIs : Params -> List Input
makeIs record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = []
makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = Add x ∷ (makeIs (record
                                                                                                            { authSigs = authSigs
                                                                                                            ; nr = nr
                                                                                                            ; pfU = pfU 
                                                                                                            ; pfL = pfL
                                                                                                            }) ) 


prop0 : ∀ {s i s' p} -> ((s ~[ i ]~* s') p)
prop0 {s} {i} {s'} {p} = {!cons!}

{-
prop1 : ∀ { v pkh d sigs val } -> (par : Params) -> ∃[ sigs' ] ((record { label = (Collecting v pkh d sigs) ; value = val } ~[ (makeIs par) ]~* record { label = (Collecting v pkh d sigs') ; value = val }) par)
prop1 {sigs = sigs} record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = ⟨ sigs , root ⟩
prop1 {v} {pkh} {d} {sigs} {val} record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = ⟨ {!!} , (cons ( record { label = (Collecting v pkh d (insert x sigs)) ; value = val }) (TAdd {!!}) {!!}) ⟩ 
-}
{-
  

-- × (IsTrue (value s' < value s))) make values > 0

  liquidity record { label = Holding ; value = value ; pfG = pfG } pf = {!!}
  liquidity record { label = (Collecting v pkh d sigs) ; value = value ; pfG = pfG } pf = ⟨ {!!} , ⟨ {!foo authSigs!} , {!!} ⟩ ⟩
-}
-- record { label = Holding ; value = value - v }      [Add x ; Add y ; .... Add z ; Pay] | <- authSigs params



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



  lemmaLT : ∀ (a b : Nat) -> IsTrue (a < b) -> IsTrue (a < suc b)
  lemmaLT zero (suc b) pf = IsTrue.itsTrue
  lemmaLT (suc a) (suc b) pf = lemmaLT a b pf

-}
