open import Lib
open import Haskell.Prelude 
open import Relation.Binary.PropositionalEquality.Core

open import ProofLib

module ValueOld where

Value = Map AssetClass Integer


plus : Integer -> Maybe Integer -> Integer
plus a Nothing = a
plus a (Just x) = a + x

addValue : Value -> Value -> Value
addValue (MkMap ls) (MkMap rs) = MkMap (ls' ++ rs')
  where
--  plus : Integer -> Maybe Integer -> Integer
--  plus a Nothing = a
--  plus a (Just x) = a + x
  ls' = map (λ (k , v) -> (k , (plus v (lookup k rs)))) ls
  rs' = filter (λ (k , v) -> lookup k ls == Nothing) rs



negValue : Value -> Value
negValue (MkMap xs) = MkMap (map (λ (k , v) → (k , (negateInteger v))) xs)

subValue : Value -> Value -> Value
subValue v1 v2 = addValue v1 (negValue v2)

compareWith : (Integer -> Integer -> Bool) -> Value -> Value -> Bool
compareWith f (MkMap ls) (MkMap rs) = ls' && rs'
  where
  maybeCompare : Integer -> Maybe Integer -> Bool
  maybeCompare a Nothing = f a 0
  maybeCompare a (Just x) = f a x
  ls' = all (λ (k , v) -> (maybeCompare v (lookup k rs))) ls 
  rs' = all (λ (k , v) -> (f 0 v)) (filter (λ (k , v) -> lookup k ls == Nothing) rs) 


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


test :
  addValue
  (MkMap ((1 , 100) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 77) ∷ ((6 , 200) ∷ ((5 , 100) ∷ []))))
  ≡ MkMap ((1 , 100) ∷ ((5 , 200) ∷ ((6 , 400) ∷ (77 , 77) ∷ [])))
test = refl

test2 :
  subValue
  (MkMap ((1 , 100) ∷ ((5 , 100) ∷ ((6 , 200) ∷ []))))
  (MkMap ((77 , 77) ∷ ((6 , 200) ∷ ((5 , 100) ∷ []))))
  ≡ MkMap ((1 , 100) ∷ ((5 , 0) ∷ ((6 , 0) ∷ (77 , -77) ∷ [])))
test2 = refl

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



{-
  let
    f :: a -> Maybe a -> a
    f a b' = case b' of
      Nothing -> a
      Just b  -> merge a b

    ls' :: [(k, a)]
    ls' = P.fmap (\(c, i) -> (c, f i (lookup c (Map rs)))) ls

    rs' :: [(k, a)]
    rs' = List.filter (\(c, _) -> not (List.any (\(c', _) -> c' == c) ls)) rs
   in
    Map (ls' List.++ rs')


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
-}



emptyValue : Value
emptyValue = MkMap []

minValue : Value
minValue = MkMap ((ada , 2) ∷ [])

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

  iZero : Has0 Value
  iZero = record { emptyVal = emptyValue }

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


checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 2
--{-# COMPILE AGDA2HS checkMinValue #-}

uhh : ∀ (xs : List (Nat × Integer)) -> filter (λ (k , v) -> lookup {a = Nat} {b = Integer} k [] == Nothing) xs ≡ xs
uhh [] = refl
uhh (x ∷ xs) = cong (x ∷_) (uhh xs)

buh : ∀ (xs : List (Nat × Integer)) -> map (λ (k , v) -> (k , (plus v (lookup k [])))) xs ++ [] ≡ xs
buh [] = refl
buh (x ∷ xs) = cong (x ∷_) (buh xs)

addValIdL : ∀ (a : Value) -> addValue emptyValue a ≡ a
addValIdL (MkMap []) = refl
addValIdL (MkMap (x ∷ xs)) = cong (λ y → MkMap (x ∷ y)) (uhh xs)

addValIdR : ∀ (a : Value) -> addValue a emptyValue ≡ a
addValIdR (MkMap []) = refl
addValIdR (MkMap (x ∷ xs)) = cong (λ y → MkMap (x ∷ y)) (buh xs)

maybe⊥ : ∀ {x : Value} -> Nothing ≡ Just x -> ⊥
maybe⊥ ()

maybe≡ : ∀ {a b : Value} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl

v=v : ∀ (v : Value) -> eqValue v v ≡ True
v=v (MkMap []) = refl
v=v (MkMap (x ∷ xs)) rewrite n=n (x .fst) | i=i (x .snd) = v=v (MkMap {!xs!}) --v=v {!MkMap xs!}

why : ∀ {y} -> eqValue (addValue (MkMap []) (MkMap y))
      (addValue (MkMap y) (MkMap []))
      ≡ True
why {y} = subst (λ x →  eqValue x (addValue (MkMap y) (MkMap [])) ≡ True) (sym (addValIdL (MkMap y)))
          (subst (λ x → eqValue (MkMap y) x ≡ True) (sym (addValIdR (MkMap y))) {!refl!})

commVal : ∀ (a b : Value) -> eqValue (addValue a b) (addValue b a) ≡ True
commVal (MkMap []) b@(MkMap y) rewrite sym (addValIdL b) | sym (addValIdR b) = {!!}
commVal (MkMap (x ∷ xs)) (MkMap y) = {!!}
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
