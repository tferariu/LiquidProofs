module DEx where

open import Haskell.Prelude


Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Integer
TokenName = Integer

PubKeyHash = Integer --no longer string because of equality issues
Value = List (CurrencySymbol × (List TokenName × Integer)) 


AssetClass = CurrencySymbol × TokenName

assetClass : CurrencySymbol -> TokenName -> AssetClass
assetClass cs tn = cs , tn

record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r


record State : Set where
  field
    c1    : AssetClass
    c2    : AssetClass
    cmap1 : List ((Rational × PubKeyHash) × Integer)
    cmap2 : List ((Rational × PubKeyHash) × Integer)
open State public


eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 

instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

eqState : State -> State -> Bool
eqState b c = (c1 b     == c1 c) &&
              (c2 b     == c2 c) &&
              (cmap1 b  == cmap1 c)  &&
              (cmap2 b  == cmap2 c)

instance
  iEqState : Eq State
  iEqState ._==_ = eqState


{-# COMPILE AGDA2HS State #-}

record ScriptContext : Set where
    field
        inputVal    : Value
        outputVal   : Value
        outputState : State
        payTo       : PubKeyHash
        payAmt      : Value
        signature   : PubKeyHash
open ScriptContext public

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx



data Input : Set where
  Offer   : PubKeyHash -> Int -> CurrencySymbol -> TokenName -> Rational -> Input
  Request : PubKeyHash -> CurrencySymbol -> TokenName -> List ((Rational × PubKeyHash) × Integer) -> Input
  Cancel  : PubKeyHash -> Int -> CurrencySymbol -> TokenName -> Rational -> Input

{-# COMPILE AGDA2HS Input #-}

newState : ScriptContext -> State
newState ctx = outputState ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

checkOffer : PubKeyHash -> Int -> CurrencySymbol -> TokenName -> Rational -> State -> Bool
checkOffer a b c d e f = True

agdaValidator : State -> Input -> ScriptContext -> Bool
agdaValidator dat red ctx = case red of λ where
  (Offer pkh v cs tn r) -> checkSigned pkh ctx && v > 0 && (numerator r * denominator r) > 0 && checkOffer pkh v cs tn r dat --WRONG NEEDS FIXING 

{-
(Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs ) -}

  (Request pkh cs tn map) -> True
  (Cancel pkh v cs tn r) -> True
{-
query : PubKeyHash -> List PubKeyHash -> Bool
query pkh [] = False
query pkh (x ∷ l') = (x == pkh) || query pkh l'

insert : PubKeyHash -> List PubKeyHash -> List PubKeyHash
insert pkh [] = (pkh ∷ [])
insert pkh (x ∷ l') = if (x == pkh)
  then (x ∷ l')
  else (x ∷ (insert pkh l'))

{-# COMPILE AGDA2HS query #-}
{-# COMPILE AGDA2HS insert #-}



checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = pkh == payTo ctx && v == payAmt ctx

expired : Deadline -> ScriptContext -> Bool
expired d ctx = (time ctx) > d



geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

record Params : Set where
    field
        authSigs  : List PubKeyHash
        nr : Nat
open Params public


{-# COMPILE AGDA2HS Params #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx = case dat of λ where

  Holding -> case red of λ where

    (Propose v pkh d) -> (newValue ctx == oldValue ctx) && geq (oldValue ctx) v && gt v emptyValue && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == [] )
    (Add _) -> False
    Pay -> False
    Cancel -> False 

  (Collecting v pkh d sigs) -> case red of λ where

    (Propose _ _ _) -> False

    (Add sig) -> newValue ctx == oldValue ctx && checkSigned sig ctx && query sig (authSigs param) && (case (newLabel ctx) of λ where
      Holding -> False
      (Collecting v' pkh' d' sigs') -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs )

    Pay -> (lengthNat sigs) >= (nr param) && (case (newLabel ctx) of λ where
      Holding -> checkPayment pkh v ctx && oldValue ctx == ((newValue ctx) + v)
      (Collecting _ _ _ _) -> False )
      
    Cancel -> newValue ctx == oldValue ctx && (case (newLabel ctx) of λ where
      Holding -> expired d ctx
      (Collecting _ _ _ _) -> False)
  

{-# COMPILE AGDA2HS agdaValidator #-}


-}
