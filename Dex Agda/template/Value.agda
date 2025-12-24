open import Lib
open import Haskell.Prelude

module Value where

-- Defining an abstract Value, does not get exported since Value exists in Plinth
-- We cannot use the same definitions as Plinth because they are optimized for
-- Blockchain use and not amenable to proofs.
-- https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-ledger-api/src/PlutusLedgerApi.V1.Value.html#Value

Value = Map AssetClass Integer

addValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then (ac , val + val') ∷ (addValueAux xs ys)
                   else (if (ac < ac') then (ac , val) ∷ (addValueAux xs v2)
                                       else (ac' , val') ∷ (addValueAux v1 ys))

addValue : Value -> Value -> Value
addValue (MkMap v1) (MkMap v2) = MkMap (addValueAux v1 v2)

negValue : Value -> Value
negValue (MkMap xs) = MkMap (map (λ (k , v) → (k , (negateInteger v))) xs)

subValue : Value -> Value -> Value
subValue v1 v2 = addValue v1 (negValue v2)

eqValue : Value -> Value -> Bool
eqValue (MkMap x) (MkMap y) = x == y

leq : Value -> Value -> Bool
leq (MkMap x) (MkMap y) = x <= y

lt : Value -> Value -> Bool
lt (MkMap x) (MkMap y) = x < y 

geq : Value -> Value -> Bool
geq (MkMap x) (MkMap y) = x >= y 

gt : Value -> Value -> Bool
gt (MkMap x) (MkMap y) = x > y 

emptyValue : Value
emptyValue = MkMap []

minValue : Value
minValue = MkMap ((ada , 3) ∷ [])

2xMinValue : Value
2xMinValue = MkMap ((ada , 6) ∷ [])

lovelaces : Value -> Integer
lovelaces (MkMap []) = 0
lovelaces (MkMap ((ac , amt) ∷ xs)) = if ac == ada then amt
                                         else lovelaces (MkMap xs)

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

  iOrdFromLessThanValue : OrdFromLessThan Value
  iOrdFromLessThanValue .OrdFromLessThan._<_ = lt

  iOrdVal : Ord Value
  iOrdVal = record
    { OrdFromLessThan iOrdFromLessThanValue }

  iNumberValue : Number Value
  iNumberValue = record { Constraint = λ x → ⊤ ; fromNat = λ n → MkMap ((ada , (Integer.pos n)) ∷ []) }

  iNumValue : Num Value
  iNumValue .MinusOK _ _         = ⊤
  iNumValue .NegateOK _          = ⊤
  iNumValue .Num.FromIntegerOK _ = ⊤
  iNumValue ._+_ x y             = addValue x y 
  iNumValue ._-_ x y             = subValue x y 
  iNumValue ._*_ x y             = x 
  iNumValue .negate x            = negValue x 
  iNumValue .abs x               = x 
  iNumValue .signum x            = x 
  iNumValue .fromInteger n       = (MkMap ((ada , n) ∷ [])) --integerToInt n


assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (MkMap []) ac = 0
assetClassValueOf (MkMap ((ac' , amt) ∷ vs)) ac = if ac' == ac then amt else assetClassValueOf (MkMap vs) ac

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = MkMap ((ac , amt) ∷ [])

checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 5

--Postulated properties of Value. 

postulate
  commVal : ∀ (a b : Value) -> a + b ≡ b + a
  assocVal : ∀ (a b c : Value) -> (a + b) + c ≡ a + (b + c)
  v=v : ∀ (v : Value) -> (v == v) ≡ True
  ==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
  ≡vto== : ∀ (a b : Value) -> a ≡ b -> (a == b) ≡ True
  addValIdL : ∀ (a : Value) -> emptyValue + a ≡ a
  addValIdR : ∀ (a : Value) -> a + emptyValue ≡ a
  switchSides : ∀ (a b c : Value) -> a + b ≡ c -> a ≡ c - b
  switchSides' :  ∀ (a b c : Value) -> a - b ≡ c -> a ≡ b + c
  v-v : ∀ (a : Value) -> subValue a a ≡ emptyValue
  geq-refl : ∀ (a : Value) -> geq a a ≡ True 
  notGeqToLt : ∀ (a b : Value) -> geq a b ≡ False -> lt a b ≡ True
  ltToGt : ∀ (a b : Value) -> lt a b ≡ True -> gt b a ≡ True
  geqTrans : ∀ (a b c : Value) -> geq a b ≡ True -> geq b c ≡ True -> geq a c ≡ True
  sumLemma : ∀ (a b : Value) -> geq a emptyValue ≡ True -> geq b emptyValue ≡ True -> geq (addValue a b) emptyValue ≡ True
  diffLemma : ∀ (a b : Value) -> geq a b ≡ True -> geq b emptyValue ≡ True -> geq (subValue a b) emptyValue ≡ True
  lovelaceLemma : ∀ (a b : Value) -> geq a b ≡ True -> (lovelaces a >= lovelaces b) ≡ True

  
