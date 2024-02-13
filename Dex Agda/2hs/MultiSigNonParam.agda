open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Char

module MultiSigNonParam where


magic : {A : Set} → ⊥ → A
magic ()

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

PubKeyHash = Integer --Not string because of memes
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

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && (case (newLabel ctx) of λ where
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
open State


data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where

  TPropose : ∀ {v pkh d val par}
    -> IsTrue (val >= v)
    -> IsTrue (v > 0)
    -------------------
    -> par ⊢ record { label = Holding ; value = val }
       ~[ (Propose v pkh d) ]~>
       record { label = Collecting v pkh d [] ; value = val}


  TAdd : ∀ {v pkh d sig sigs val par}
    -> IsTrue (query sig (authSigs par) )
    -------------------
    -> par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
       ~[ (Add sig) ]~>
       record { label = (Collecting v pkh d (insert sig sigs)) ; value = val }

  TPay : ∀ {v pkh d sigs val val' par}
    -> val ≡ val' + v
    -> IsTrue (lengthNat sigs >= (nr par))
    -------------------
    -> par ⊢ record { label = Collecting v pkh d sigs ; value = val}
       ~[ Pay ]~>
       record { label = Holding ; value = val' }

  TCancel : ∀ {v pkh d sigs val par}
    -------------------
    -> par ⊢ record { label = Collecting v pkh d sigs ; value = val }
       ~[ Cancel ]~>
       record { label = Holding ; value = val}


data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { s s' i is s'' par }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -----------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


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
validStateMulti iv (cons x tr) = validStateMulti (validStateTransition iv x) tr


makeIs : Params -> List Input
makeIs record { authSigs = authSigs ; nr = zero ; pfU = pfU ; pfL = pfL } = []
makeIs record { authSigs = (x ∷ authSigs) ; nr = (suc nr) ; pfU = (pff :: pfU) ; pfL = pfL } = Add x ∷ (makeIs (record
                                                                                                          { authSigs = authSigs
                                                                                                          ; nr = nr
                                                                                                          ; pfU = pfU 
                                                                                                          ; pfL = pfL
                                                                                                          }) ) 

--keep parameters same?

makeIs' : List PubKeyHash -> List Input
makeIs' [] = []
makeIs' (x ∷ pkhs) = Add x ∷ makeIs' pkhs

makeSigs' : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs' sigs [] = sigs
makeSigs' sigs (x ∷ asigs) = makeSigs' (insert x sigs) asigs

makeSigs : List PubKeyHash -> List Input -> List PubKeyHash
makeSigs sigs [] = sigs
makeSigs sigs (Propose x x₁ x₂ ∷ is) = makeSigs sigs is
makeSigs sigs (Add x ∷ is) = makeSigs (insert x sigs) is
makeSigs sigs (Pay ∷ is) = makeSigs sigs is
makeSigs sigs (Cancel ∷ is) = makeSigs sigs is

why : ∀ (x : PubKeyHash) {b : Bool} -> IsTrue (x == x || b)
why (Integer.pos zero) = IsTrue.itsTrue
why (Integer.pos (suc n)) = why (Integer.pos n)
why (Integer.negsuc zero) = IsTrue.itsTrue
why (Integer.negsuc (suc n)) = why (Integer.pos n)

why' : ∀ (a : Bool) (x : PubKeyHash) (ys z : List PubKeyHash) -> IsTrue (query x (ys ++ x ∷ z)) -> IsTrue (a || query x (ys ++ x ∷ z) )
why' False x ys z pf = pf
why' True x ys z pf = IsTrue.itsTrue

why2 : ∀ (x : PubKeyHash) {b c : Bool} -> IsTrue (c || x == x || b)
why2 (Integer.pos zero) {c = False} = IsTrue.itsTrue
why2 (Integer.pos zero) {c = True} = IsTrue.itsTrue
why2 (Integer.pos (suc n)) {c = False} = why (Integer.pos n) --why2 (Integer.pos n)
why2 (Integer.pos (suc n)) {c = True} = IsTrue.itsTrue
why2 (Integer.negsuc zero) {c = False} = IsTrue.itsTrue
why2 (Integer.negsuc zero) {c = True} = IsTrue.itsTrue
why2 (Integer.negsuc (suc n)) {c = False} = why (Integer.pos n)
why2 (Integer.negsuc (suc n)) {c = True} = IsTrue.itsTrue

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




toby : ∀ (x : PubKeyHash) (y z : List PubKeyHash) -> IsTrue (query x (y ++ x ∷ z))
toby x [] z = why x
toby x (y ∷ ys) z = why' (eqInteger y x) x ys z (toby x ys z)


appendLemma : ∀ (x : PubKeyHash) (a b : List PubKeyHash) -> a ++ x ∷ b ≡ (a ++ x ∷ []) ++ b
appendLemma x [] b = refl
appendLemma x (a ∷ as) b = cong (λ y → a ∷ y) (appendLemma x as b) 


prop1' : ∀ { v pkh d sigs val } (par : Params) (n : Nat) (asigs asigs' asigs'' : List PubKeyHash)
         -> n ≡ (nr par) -> asigs ≡ (authSigs par) -> asigs ≡ (asigs' ++ asigs'') ->
         ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val }
         ~[ makeIs' asigs'' ]~*
         record { label = (Collecting v pkh d (makeSigs' sigs asigs'')) ; value = val })
prop1' record { authSigs = .(asigs' ++ []) ; nr = nr₁ ; pfU = pfU₁ ; pfL = pfL₁ } .nr₁ .(asigs' ++ []) asigs' [] refl refl refl = root
prop1' record { authSigs = .(asigs' ++ x ∷ asigs'') ; nr = n ; pfU = pfU₁ ; pfL = pfL₁ } .n .(asigs' ++ x ∷ asigs'') asigs' (x ∷ asigs'') refl refl refl
       = cons (TAdd (toby x asigs' asigs'')) (prop1' (record { authSigs = (asigs' ++ x ∷ asigs'') ; nr = n ; pfU = pfU₁ ; pfL = pfL₁ })
         n ((asigs' ++ x ∷ asigs'')) (asigs' ++ (x ∷ [])) asigs'' refl refl (appendLemma x asigs' asigs''))


prop1 : ∀ { v pkh d sigs val } (par : Params) -> ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val } ~[ (makeIs' (authSigs par)) ]~*
                                                 record { label = (Collecting v pkh d (makeSigs' sigs (authSigs par))) ; value = val })
prop1 par = prop1' par (nr par) (authSigs par) [] (authSigs par) refl refl refl


makeIsP : List PubKeyHash -> List Input
makeIsP [] = Pay ∷ []
makeIsP (x ∷ pkhs) = Add x ∷ makeIs' pkhs

{-
makeSigs' : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
makeSigs' sigs [] = sigs
makeSigs' sigs (x ∷ asigs) = makeSigs' (insert x sigs) asigs
-}

lemmaLE : ∀ (v val : Value) -> IsTrue ((v < val) || (val == v)) -> IsFalse (val < v)
lemmaLE zero val = λ _ → IsFalse.itsFalse
lemmaLE (suc v) zero = λ ()
lemmaLE (suc v) (suc val) = lemmaLE v val

lemmaOK : ∀ {v val pkh d sigs} -> (Collecting v pkh d sigs) ∻ val -> IsFalse (val < v)
lemmaOK {v} {val} (Col pf1 pf2) = lemmaLE v val pf1


prop2 : ∀ { v pkh d sigs val } (par : Params) -> (x : (Collecting v pkh d sigs) ∻ val)  -> ( par ⊢ record { label = (Collecting v pkh d sigs) ; value = val } ~[ (makeIsP (authSigs par)) ]~*
                                                 record { label = Holding ; value = (val - v) {{lemmaOK x}}  })
prop2 par pf = {!!}

{--}
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
