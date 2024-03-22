module DEx where

open import Haskell.Prelude

variable
  k v : Set

Placeholder = String
POSIXTimeRange = Placeholder
ScriptPurpose = Placeholder
ThreadToken = Placeholder

CurrencySymbol = Integer
TokenName = Integer

PubKeyHash = Integer --no longer string because of equality issues


Value = List (CurrencySymbol × (List (TokenName × Integer))) 


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
{-# COMPILE AGDA2HS State #-}

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b

lookup' : {{Eq k}} -> k -> List (k × v) -> Maybe v
lookup' x [] = Nothing
lookup' x ( ( x' , y ) ∷ xs ) = if (x == x')
  then Just y
  else lookup' x xs

insert' : {{Ord k}} -> k -> Integer -> List (k × Integer) -> List (k × Integer)
insert' key val [] = ( key , val ) ∷ []
insert' key val ( ( k , v ) ∷ xs ) = if (key < k)
  then ( key , val ) ∷ ( ( k , v ) ∷ xs )
  else if (key == k)
       then (key , (v + val)) ∷ xs
       else (k , v) ∷ (insert' key val xs)

reduce' : {{Ord k}} -> k -> Integer -> List (k × Integer) -> List (k × Integer)
reduce' key val [] = ( key , val ) ∷ []
reduce' key val ( ( k , v ) ∷ xs ) = if (key < k)
  then ( key , val ) ∷ ( ( k , v ) ∷ xs )
  else if (key == k)
       then (key , (v - val)) ∷ xs
       else (k , v) ∷ (reduce' key val xs)

delete' : {{Eq k}} -> k -> List (k × v) -> List (k × v)
delete' x [] = []
delete' x ( ( x' , y ) ∷ xs ) = if (x == x')
  then xs
  else delete' x xs



singleton : CurrencySymbol -> TokenName -> Integer -> Value
singleton cs tn v = (cs , ( (tn , v)  ∷ [])) ∷ []

instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

  iOrdRational : Ord Rational
  iOrdRational = ordFromLessThan ltRational


eqState : State -> State -> Bool
eqState b c = (c1 b     == c1 c) &&
              (c2 b     == c2 c) &&
              (cmap1 b  == cmap1 c)  &&
              (cmap2 b  == cmap2 c)

instance
  iEqState : Eq State
  iEqState ._==_ = eqState







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
  Offer   : PubKeyHash -> Integer -> CurrencySymbol -> TokenName -> Rational -> Input
  Request : PubKeyHash -> CurrencySymbol -> TokenName -> List ((Rational × PubKeyHash) × Integer) -> Input
  Cancel  : PubKeyHash -> Integer -> CurrencySymbol -> TokenName -> Rational -> Input

{-# COMPILE AGDA2HS Input #-}

newState : ScriptContext -> State
newState ctx = outputState ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx



checkOffer : PubKeyHash -> Integer -> CurrencySymbol -> TokenName -> Rational -> State -> ScriptContext -> Bool
checkOffer pkh val cs tn r st ctx
  = if ( cs , tn ) == c1 st
       then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ;
            cmap1 = insert' (r , pkh) val (cmap1 st) ; cmap2 = cmap2 st}
       else if ( cs , tn ) == c2 st
            then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ; cmap1 = cmap1 st ;
            cmap2 = insert' (r , pkh) val (cmap2 st) }
            else False

checkValue : PubKeyHash -> Integer -> CurrencySymbol -> TokenName -> Rational -> State -> ScriptContext -> Bool
checkValue pkh val cs tn r st ctx
  = if ( cs , tn ) == c1 st
       then (case (lookup' (r , pkh) (cmap1 st)) of λ where
            Nothing -> False
            (Just val') -> val' >= val)
       else if ( cs , tn ) == c2 st
            then (case (lookup' (r , pkh) (cmap1 st)) of λ where
                 Nothing -> False
                 (Just val') -> val' >= val)
            else False

checkCancel : PubKeyHash -> Integer -> CurrencySymbol -> TokenName -> Rational -> State -> ScriptContext -> Bool
checkCancel pkh val cs tn r st ctx
  = if ( cs , tn ) == c1 st
       then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ;
            cmap1 = reduce' (r , pkh) val (cmap1 st) ; cmap2 = cmap2 st}
       else if ( cs , tn ) == c2 st
            then newState ctx ==
            record { c1 = c1 st ; c2 = c2 st ; cmap1 = cmap1 st ;
            cmap2 = reduce' (r , pkh) val (cmap2 st) }
            else False

agdaValidator : State -> Input -> ScriptContext -> Bool
agdaValidator dat red ctx = case red of λ where
  (Offer pkh v cs tn r) -> checkSigned pkh ctx && v > 0
                           && (numerator r * denominator r) > 0
                           && checkOffer pkh v cs tn r dat ctx
                           && oldValue ctx <> singleton cs tn v == newValue ctx


  (Request pkh cs tn map) -> True
  (Cancel pkh v cs tn r) -> checkSigned pkh ctx
                            && checkValue pkh v cs tn r dat ctx
                            && checkCancel pkh v cs tn r dat ctx
                            && oldValue ctx == newValue ctx <> singleton cs tn v
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


{-
appendSubValue : List (TokenName × Integer) -> List (TokenName × Integer) -> List (TokenName × Integer)
appendSubValue [] l = l
appendSubValue ((x , y) ∷ zs) l = insert' x y (appendSubValue zs l)

insertSubValue : CurrencySymbol -> List (TokenName × Integer) -> Value -> Value
insertSubValue key val [] =  ( key , val ) ∷ []
insertSubValue key val ( ( k , v ) ∷ xs ) = if (key == k)
       then (key , (appendSubValue v val)) ∷ xs
       else (k , v) ∷ (insertSubValue key val xs)

appendValue : Value -> Value -> Value
appendValue [] v = v
appendValue ((x , y) ∷ zs) v = insertSubValue x y (appendValue zs v)

--  iSemigroupValue : Semigroup Value
--  iSemigroupValue ._<>_ = appendValue

-}
