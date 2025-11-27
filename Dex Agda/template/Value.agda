open import Lib
open import Haskell.Prelude

open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary hiding (True ; False)

open import Data.Integer.Properties

--open import Data.Integer 
--open import Data.Integer.Properties

open import ProofLib

module Value where



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
addValue (MkMap v1) (MkMap v2) = MkMap (v1 ++ v2)
--MkMap (addValueAux v1 v2)


negValue : Value -> Value
negValue (MkMap xs) = MkMap (map (λ (k , v) → (k , (negateInteger v))) xs)

subValue : Value -> Value -> Value
subValue v1 v2 = addValue v1 (negValue v2)

auxCompare : (Integer -> Integer -> Bool) -> List (AssetClass × Integer) -> List (AssetClass × Integer) -> Bool
auxCompare f [] [] = True
auxCompare f [] ((ac , val) ∷ vs) = val == 0 && auxCompare f [] vs
auxCompare f ((ac , val) ∷ vs) [] = val == 0 && auxCompare f vs [] 
auxCompare f v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if (ac == ac') then f val val' && auxCompare f xs ys --(ac , val + val') ∷ (addValueAux xs ys)
                   else if (ac < ac') then val == 0 && auxCompare f xs v2 --(ac , val) ∷ (addValueAux xs v2)
                                      else val' == 0 && auxCompare f v1 ys --(ac' , val') ∷ (addValueAux v1 ys))

{-
compareWith : (Integer -> Integer -> Bool) -> Value -> Value -> Bool
compareWith f (MkMap ls) (MkMap rs) = auxCompare f ls rs


eqValue : Value -> Value -> Bool
eqValue v1 v2 = compareWith _==_ v1 v2

leq : Value -> Value -> Bool
leq v1 v2 = compareWith _<=_ v1 v2

lt : Value -> Value -> Bool
lt v1 v2 = compareWith _<=_ v1 v2 && not (eqValue v1 v2)

geq : Value -> Value -> Bool
geq v1 v2 = compareWith _>=_ v1 v2

gt : Value -> Value -> Bool
gt v1 v2 =  compareWith _>=_ v1 v2 && not (eqValue v1 v2)
-}

eqValue : Value -> Value -> Bool
eqValue (MkMap x) (MkMap y) = x == y

leq : Value -> Value -> Bool
leq (MkMap x) (MkMap y) = x <= y --_<=_

lt : Value -> Value -> Bool
lt (MkMap x) (MkMap y) = x < y -- _<_

geq : Value -> Value -> Bool
geq (MkMap x) (MkMap y) = x >= y --_>=_

gt : Value -> Value -> Bool
gt (MkMap x) (MkMap y) = x > y --= _>_

emptyValue : Value
emptyValue = MkMap []

minValue : Value
minValue = MkMap ((ada , 5) ∷ [])

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


sumLemma : ∀ (v1 v2 : Value) -> geq v1 emptyValue ≡ True -> geq v2 emptyValue ≡ True -> geq (addValue v1 v2) emptyValue ≡ True
sumLemma (MkMap []) (MkMap []) p1 p2 = refl
sumLemma (MkMap []) (MkMap (x ∷ y)) p1 p2 = refl
sumLemma (MkMap (x ∷ x₁)) (MkMap []) p1 p2 = refl
sumLemma (MkMap (x ∷ x₁)) (MkMap (x₂ ∷ y)) p1 p2 = refl


diffLemma : ∀ (v1 v2 : Value) -> geq v1 v2 ≡ True -> geq v2 emptyValue ≡ True -> geq (subValue v1 v2) emptyValue ≡ True
diffLemma (MkMap []) (MkMap []) p1 p2 = refl
diffLemma (MkMap (x ∷ x₁)) (MkMap []) p1 p2 = refl
diffLemma (MkMap (x ∷ x₁)) (MkMap (x₂ ∷ y)) p1 p2 = refl


postulate
  commVal : ∀ (a b : Value) -> a + b ≡ b + a
  assocVal : ∀ (a b c : Value) -> (a + b) + c ≡ a + (b + c)
  v=v : ∀ (v : Value) -> (v == v) ≡ True
  ==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
  ≡vto== : ∀ (a b : Value) -> a ≡ b -> (a == b) ≡ True
  addValIdL : ∀ (v : Value) -> emptyValue + v ≡ v
  addValIdR : ∀ (v : Value) -> v + emptyValue ≡ v
  switchSides : ∀ (a b c : Value) -> a + b ≡ c -> a ≡ c - b
  switchSides' :  ∀ (a b c : Value) -> a - b ≡ c -> a ≡ b + c

  v-v : ∀ (i : Value) -> subValue i i ≡ emptyValue
  geq-refl : ∀ (v : Value) -> geq v v ≡ True
  
  notGeqToLt : ∀ (a b : Value) -> geq a b ≡ False -> lt a b ≡ True
  ltToGt : ∀ (a b : Value) -> lt a b ≡ True -> gt b a ≡ True
  geqTrans : ∀ (a b c : Value) -> geq a b ≡ True -> geq b c ≡ True -> geq a c ≡ True


  

  


{- --not true
==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
==vto≡ (MkMap []) (MkMap []) pf = refl
==vto≡ (MkMap []) (MkMap ((k , Integer.pos zero) ∷ y)) pf = {!!}
==vto≡ (MkMap (x ∷ x₁)) (MkMap []) pf = {!!}
==vto≡ (MkMap (x ∷ x₁)) (MkMap (x₂ ∷ y)) pf = {!!}
-}

{-
auxv=v : ∀ {xs} -> auxCompare eqInteger xs xs ≡ True
auxv=v {[]} = refl
auxv=v {x ∷ xs} rewrite n=n (x .fst) | i=i (x .snd) = auxv=v {xs}

addValIdL : ∀ (a : Value) -> addValue emptyValue a ≡ a
addValIdL (MkMap []) = refl
addValIdL (MkMap (x ∷ xs)) = refl

addValIdR : ∀ (a : Value) -> addValue a emptyValue ≡ a
addValIdR (MkMap []) = refl
addValIdR (MkMap (x ∷ xs)) = refl 



commValAux : ∀ {x y} -> addValueAux x y ≡ addValueAux y x
commValAux {[]} {[]} = refl
commValAux {[]} {x ∷ ys} = refl
commValAux {x ∷ xs} {[]} = refl
commValAux {x ∷ xs} {y ∷ ys} with x.fst == y .fst in eq
...| True = ?
...| False = {!!}


commVal : ∀ (a b : Value) -> eqValue (addValue a b) (addValue b a) ≡ True
commVal (MkMap x) (MkMap y) = {!!}

-}



{--}
{-
subAddVal : ∀ {x xs b} -> addValue (MkMap (x ∷ xs)) b ≡ addValue (MkMap (x ∷ [])) (addValue (MkMap xs) b)
subAddVal {x} {[]} {MkMap x₁} = {!!}
subAddVal {x} {x₁ ∷ xs} {MkMap x₂} = {!!}

addValAssoc : ∀ (a b c : Value) -> addValue (addValue a b) c ≡ addValue a (addValue b c)
addValAssoc (MkMap []) b c rewrite addValIdL b | addValIdL (addValue b c) = refl
addValAssoc (MkMap (x ∷ xs)) b c = {!!}
-}
{-
==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
==vto≡ (MkMap []) (MkMap []) pf = refl
==vto≡ (MkMap []) (MkMap ((k , Integer.pos zero) ∷ y)) pf = {!!}
==vto≡ (MkMap (x ∷ x₁)) (MkMap []) pf = {!!}
==vto≡ (MkMap (x ∷ x₁)) (MkMap (x₂ ∷ y)) pf = {!!}
-}





{-
test :
  addValue
  (MkMap ((1 , 100) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap (((6 , 200) ∷ ((5 , 100) ∷ (77 , 77) ∷ []))))
  ≡ MkMap ((1 , 100) ∷ ((5 , 200) ∷ ((6 , 400) ∷ (77 , 77) ∷ [])))
test = {!!} --refl

test2 :
  subValue
  (MkMap ((1 , 100) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 77) ∷ ((6 , 200) ∷ ((5 , 100) ∷ []))))
  ≡ MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test2 = {!!} --refl

test3 :
  eqValue
  (MkMap ((1 , 0) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 0) ∷ ((6 , 200) ∷ ((5 , 100) ∷ []))))
  ≡ True --MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test3 = refl

test4 :
  lt
  (MkMap ((1 , 0) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 77) ∷ ((6 , 2001) ∷ ((5 , 1001) ∷ []))))
  ≡ True --MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test4 = refl --refl

test5 :
  leq
  (MkMap ((1 , 0) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 77) ∷ ((6 , 200) ∷ ((5 , 100) ∷ []))))
  ≡ True --MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test5 = refl --refl

test6 :
  geq
  (MkMap ((1 , 10) ∷ ((5 , 1100) ∷ ((6 , 2200) ∷ []))))
  (MkMap ((77 , 0) ∷ ((6 , 2001) ∷ ((5 , 1001) ∷ []))))
  ≡ True --MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test6 = refl --refl

test7 :
  gt
  (MkMap ((1 , 0) ∷ ((5 , 1100) ∷ ((6 , 2200) ∷ []))))
  (MkMap ((77 , 0) ∷ ((6 , 2001) ∷ ((5 , 1001) ∷ []))))
  ≡ True --MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test7 = refl --refl
-}
