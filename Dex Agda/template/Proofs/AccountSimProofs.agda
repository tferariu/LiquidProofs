open import Validators.AccountSim
open import Lib
open import Value

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer 
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

open import Haskell.Prim hiding (⊥) 
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Function.Base using (_∋_)

open import ProofLib

module Proofs.AccountSimProofs where

sumVal : AccMap -> Value
sumVal [] = 0
sumVal ((k , v) ∷ xs) = addValue v (sumVal xs)


record State : Set where
  field
    datum      : Label
    value      : Value  
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
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s tok}
    -> datum s ≡ ( tok , [] )
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> token s ≡ tok
    -> token s .snd ≡ tokName par
    -> hasToken s ≡ true
    -------------------
    -> par ⊢ s

--Transition Rules
data _~[_]~>_ : State -> Input -> State -> Set where
 
  TOpen : ∀ {pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> pkh ≡ tsig s'
    -> lookup pkh map ≡ Nothing
    -> datum s' ≡ (tok ,  insert pkh emptyValue map)
    -> value s' ≡ value s 
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> s ~[ (Open pkh) ]~> s'

  TClose : ∀ {pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> pkh ≡ tsig s'
    -> lookup pkh map ≡ Just emptyValue
    -> datum s' ≡ (tok , delete pkh map)
    -> value s' ≡ value s
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> s ~[ (Close pkh) ]~> s'

  TWithdraw : ∀ {pkh val s s' v tok map}
    -> datum s ≡ (tok , map)
    -> pkh ≡ tsig s'
    -> lookup pkh map ≡ Just v
    -> geq val emptyValue ≡ true
    -> geq v val ≡ true
    -> datum s' ≡ (tok , (insert pkh (subValue v val) map))
    -> addValue (value s') val ≡ value s
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> s ~[ (Withdraw pkh val) ]~> s'
    
  TDeposit : ∀ {pkh val s s' v tok map}
    -> datum s ≡ (tok , map)
    -> pkh ≡ tsig s'
    -> lookup pkh map ≡ Just v
    -> geq val emptyValue ≡ true
    -> datum s' ≡ (tok , (insert pkh (addValue v val) map))
    -> value s' ≡ addValue (value s) val
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> s ~[ (Deposit pkh val) ]~> s'

    
  TTransfer : ∀ {from to val s s' vF vT tok map}
    -> datum s ≡ (tok , map)
    -> from ≡ tsig s'
    -> lookup from map ≡ Just vF
    -> lookup to map ≡ Just vT
    -> geq val emptyValue ≡ true
    -> geq vF val ≡ true
    -> from ≢ to
    -> datum s' ≡ (tok , (insert from (subValue vF val) (insert to (addValue vT val) map)))
    -> value s' ≡ value s
    -> continues s ≡ true
    -> continues s' ≡ true
    -> hasToken s ≡ true
    -> hasToken s' ≡ true
    -------------------
    -> s ~[ (Transfer from to val) ]~> s'


data _~[_]~|_ : State -> Input -> State -> Set where

  TCleanup : ∀ {s s'}
    -> snd (datum s) ≡ []
    -> mint s' ≡ -1
    -> continues s ≡ true
    -> continues s' ≡ false
    -> hasToken s ≡ true
    -> hasToken s' ≡ false
    -------------------
    -> s ~[ Cleanup ]~| s'


--Multi-Step Transition
data _~[_]~*_ : State -> List Input -> State -> Set where

  root : ∀ { s }
    ------------------
    -> s ~[ [] ]~* s

  cons : ∀ { s s' s'' i is }
    -> s ~[ i ]~> s'
    -> s' ~[ is ]~* s''
    -------------------------
    -> s ~[ (i ∷ is) ]~* s''

  fin : ∀ { s s' is }
    -> s ~[ Cleanup ]~| s'
    -------------------------
    -> s ~[ ((Cleanup) ∷ is) ]~* s'


_∈_ : ∀ (x : PubKeyHash) (xs : AccMap) → Set
x ∈ xs = Any (\y -> x ≡ fst y) xs

_∉_ : ∀ (x : PubKeyHash) (xs : AccMap) → Set
x ∉ xs = ¬ (x ∈ xs)


data Unique : AccMap → Set where
  root : Unique []
  _::_ : {x : PubKeyHash} {v : Value} {map : AccMap} -> x ∉ map -> Unique map -> Unique ((x , v) ∷ map)



Valid : State -> Set 
Valid s = All (\y -> geq (snd y) emptyValue ≡ true) (snd (datum s)) × continues s ≡ true × hasToken s ≡ true

Fides : State -> Set
Fides s = value s ≡ sumVal (snd (datum s))

Invariant : State -> Set
Invariant s = (Valid s × Fides s)


maybe⊥ : ∀ {x : Value} -> Nothing ≡ Just x -> ⊥
maybe⊥ ()

maybe≡ : ∀ {a b : Value} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl

svLemma1 : ∀ {pkh} (map : AccMap) -> lookup pkh map ≡ Nothing -> sumVal map ≡ sumVal (insert pkh emptyValue map)
svLemma1 {pkh} [] p = refl
svLemma1 {pkh} (x ∷ map) p with pkh == (fst x) in eq
...| false = cong (λ a → addValue (x .snd) a) (svLemma1 map p)
...| true = ⊥-elim (maybe⊥ (sym p))



svLemma2 : ∀ {pkh} (map : AccMap) -> lookup pkh map ≡ Just emptyValue -> sumVal map ≡ sumVal (delete pkh map)
svLemma2 [] p = refl
svLemma2 {pkh} (x ∷ map) p with pkh == (fst x) in eq
...| false = cong (λ a → addValue (x .snd) a) (svLemma2 map p)
...| true rewrite maybe≡ p = addValIdL (sumVal map)


svLemma3 : ∀ {pkh v val} (map : AccMap) -> lookup pkh map ≡ Just v
           -> addValue (sumVal map) val ≡ sumVal (insert pkh (addValue v val) map)
svLemma3 [] p = ⊥-elim (maybe⊥ p) 
svLemma3 {pkh} {v} {val} (x ∷ l) p with pkh == (fst x) in eq
...| false rewrite (assocVal (snd x) (sumVal l) val)
     = cong (λ a → addValue (snd x) a) (svLemma3 l p)
...| true rewrite maybe≡ p | assocVal v (sumVal l) val
                | commVal (sumVal l) val
                | assocVal v val (sumVal l) = refl
                

--State.value s' ≡ sumVal (insert (State.tsig s') (addValue v (negValue x)) map)
      
svLemma4 : ∀ {x v1 v2 pkh map}
           -> lookup pkh map ≡ Just v1
           -> addValue x v2 ≡ sumVal map
           -> x ≡ sumVal (insert pkh (addValue v1 (negValue v2)) map)
svLemma4 {x} {v1} {v2} {map = map} p1 p2 rewrite switchSides x v2 (sumVal map) p2 = svLemma3 map p1


svLemma5 : ∀ {from to vF vT val} (map : AccMap) -> lookup from map ≡ Just vF
           -> lookup to map ≡ Just vT -> from ≢ to
           -> sumVal map ≡ sumVal (insert from (subValue vF val) (insert to (addValue vT val) map))
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 with to == (fst x) in eq1
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | true with from == to in eq2
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | true | true = ⊥-elim (p3 (==to≡ from to eq2))
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | true | false with from == (fst x) in eq3
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | true | false | true 
         rewrite ==to≡ to (fst x) eq1 | ==to≡ from (fst x) eq3 = ⊥-elim (p3 refl)
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | true | false | false
         rewrite (maybe≡ p2) | assocVal vT val (sumVal (insert from (subValue vF val) map))
         = cong (λ a → addValue vT a) (switchSides' (sumVal map) val
           (sumVal (insert from (addValue vF (negValue val)) map)) (svLemma3 map p1)) 
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | false with from == (fst x) in eq2
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ map) p1 p2 p3 | false | true
         rewrite (maybe≡ p1) | assocVal vF (negValue val) (sumVal (insert to (addValue vT val) map))
         | commVal (negValue val) (sumVal (insert to (addValue vT val) map))
         = cong (λ a → addValue vF a) (switchSides (sumVal map) val
           (sumVal (insert to (addValue vT val) map)) (svLemma3 map p2))
svLemma5 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false | false
         = cong (λ a → addValue (snd x) a) (svLemma5 l p1 p2 p3)





fidelity : ∀ {s s' : State} {i : Input}
         -> Fides s
         -> s ~[ i ]~> s'
         -> Fides s' --value s' ≡ sumVal (snd (datum s'))
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Open _} pf (TOpen refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma1 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Close _} pf (TClose refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma2 map p3 
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Withdraw _ _} pf (TWithdraw refl refl p3 p4 p5 p6 p7 p8 p9 p10 p11) rewrite pf | p6 = svLemma4 {pkh = State.tsig s'} {map = map} p3 p7
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Deposit _ _} pf (TDeposit refl p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 | p6 | pf = svLemma3 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Transfer _ _ _} pf (TTransfer refl p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13) rewrite p8 | p9 | pf = svLemma5 map p3 p4 p7

fidelityMulti : ∀ {s s' : State} {is : List Input}
  -> value s ≡ sumVal (snd (datum s))
  -> s ~[ is ]~* s'
  -> (value s' ≡ sumVal (snd (datum s')) ⊎ continues s' ≡ false)
fidelityMulti {s} {s} {[]} p1 root = inj₁ p1 
fidelityMulti {s} {s'} {(i ∷ is)} p1 (cons {s' = s''} x p2) = fidelityMulti (fidelity p1 x) p2
fidelityMulti {s} {s'} {i ∷ is} p1 (fin {s' = s''} (TCleanup x x₂ x₃ x₄ x₅ x₆)) = inj₂ x₄

{-
diffSubLemma : ∀ (v1 v2 : Value) -> geq 0 N.≤ m -> m N.≤ n ->
               geq (+ n - + m) emptyValue ≡ true
diffSubLemma zero .zero N.z≤n N.z≤n = refl
diffSubLemma (N.suc n) .zero N.z≤n N.z≤n = refl
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) with ltNat n m in eq
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | true = ⊥-elim (nope n m eq (≤NtoleqN p2))
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | false = geqNatLemma (monusNat n m) 


diffLemma : ∀ (v1 v2 : Value) -> geq v1 v2 ≡ true -> geq v2 emptyValue ≡ true -> geq (subValue v1 v2) emptyValue ≡ true
diffLemma v1 v2 p1 p2 = {!!}
v v' (-≤- n≤m) ()
diffLemma v v' -≤+ ()
diffLemma v v' (+≤+ {m} {n} 0≤m) (+≤+ m≤n) = diffSubLemma n m m≤n 0≤m -}
{-
geqPosLemma : ∀ (n : Nat) -> geq (+ n) emptyValue ≡ true
geqPosLemma zero = refl
geqPosLemma (N.suc n) = refl
-}



--geqPosLemma (addNat n m)


lem : ∀ {pkh} (map : AccMap) (v' : Value)
      -> geq v' emptyValue ≡ true 
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (insert pkh v' map)

lem {pkh} [] v' p1 p2 = allCons {{p1}} 
lem {pkh} ((pkh' , v) ∷ label) v' p1 (allCons {{i}} {{is}}) with pkh == pkh' in eq
...| true = allCons {{p1}} 
...| false = allCons {{i}} {{lem label v' p1 is}}

geqLem : ∀ {pkh} (map : AccMap) (v : Value)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> lookup pkh map ≡ Just v
      -> geq v emptyValue ≡ true
geqLem {pkh} ((pkh' , v') ∷ label) v allCons p2 with pkh == pkh' in eq
geqLem {pkh} ((pkh' , v') ∷ label) .v' (allCons {{i}} {{is}}) refl | true = i
geqLem {pkh} ((pkh' , v') ∷ label) v (allCons {{i}} {{is}}) p2 | false = geqLem label v is p2


delem : ∀ {pkh} (map : AccMap)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (delete pkh map)
delem {pkh} [] p1 = p1
delem {pkh} ((pkh' , v') ∷ label) (allCons {{i}} {{is}}) with pkh == pkh' in eq
...| true = is 
...| false = allCons {{i}} {{delem label is}}

validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> Valid s
validStateInitial {record { datum = .(_ , []) ; value = emptyValue ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl p3 p4 p5 p6 p7 p8) = allNil , p4 , p8

validStateTransition : ∀ {s s' : State} {i}
  -> Valid s
  -> s ~[ i ]~> s'
  -> Valid s'
  {-
validStateTransition {record { datum = .(_ , _) ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ emptyValue _) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TOpen refl p2 p3 refl p5 p6 p7 p8 p9) = {!!}
validStateTransition (fst , snd , thd) (TClose x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = {!!}
validStateTransition (fst , snd , thd) (TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = {!!}
validStateTransition (fst , snd , thd) (TDeposit x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = {!!}
validStateTransition (fst , snd , thd) (TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) = {!!}
-}
validStateTransition {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ emptyValue map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TOpen refl p2 p3 refl p5 p6 p7 p8 p9) = (lem map emptyValue refl fst) , p7 , p9
validStateTransition {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , delete _ map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TClose refl p2 p3 refl p5 p6 p7 p8 p9) = (delem map fst) , p7 , p9
validStateTransition {record { datum = tok , map ; value = .(addValue value₁ val) ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ (subValue v val) map) ; value = value₁ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl p8 p9 p10 p11) = (lem map (subValue v val) (diffLemma v val p5 p4) fst) , p9 , p11
validStateTransition {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ (addValue v val) map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6 p7 p8 p9 p10) = lem map (addValue v val) (sumLemma v val (geqLem map v fst p3) p4) fst , p8 , p10
validStateTransition {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert from (subValue vF val) (insert to (addValue vT val) map)) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TTransfer {from} {to} {val} {vF = vF} {vT = vT} refl p2 p3 p4 p5 p6 p7 refl p9 p10 p11 p12 p13) = lem (insert to (addValue vT val) map) (subValue vF val) (diffLemma vF val p6 p5) (lem map (addValue vT val) (sumLemma vT val (geqLem map vT fst p4) p5) fst) , p11 , p13



{- deprecated
validStateTerminal : ∀ {s s' : State} {i}
  -> Valid s
  -> s ~[ i ]~| s'
  -> Valid s'
validStateTerminal iv (TCleanup x x₂ x₃ x₄ x₅ x₆) = Stp x₄

validStateMulti : ∀ {s s' : State} {is}
  -> Valid s
  -> s ~[ is ]~* s'
  -> Valid s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x
validStateMulti iv (fin (TCleanup x x₂ x₃ x₄ x₅ x₆)) = Stp x₄
-}

{-
geqto≤ : ∀ {a b} -> geq a b ≡ true -> a ≥ b
geqto≤ {pos n} {pos m} pf = +≤+ (leqNto≤N' pf)
geqto≤ {pos n} {negsuc m} pf = -≤+
geqto≤ {negsuc n} {negsuc m} pf = -≤- (leqNto≤N pf)
-}

makeIs : AccMap -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = (Withdraw a b) ∷ (Close a) ∷ (makeIs l)

makeL : AccMap -> AccMap
makeL [] = []
makeL ((a , b) ∷ l) = (a , emptyValue) ∷ (makeL l)


lastSig : State -> PubKeyHash
lastSig record { datum = (tok , []) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = tsig
lastSig record { datum = (tok , x ∷ []) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = fst x
lastSig record { datum = (tok , x ∷ y ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = lastSig record { datum = (tok , y ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }


lookupProp1 : ∀ {b : Bool} {a : Set} { x y z : Maybe a }
            -> b ≡ true
            -> x ≡ z
            -> (if b then x else y) ≡ z
lookupProp1 refl refl = refl


deleteProp1 : ∀ {a : AssetClass} {b : Bool} { x y z : AccMap }
            -> b ≡ true
            -> x ≡ z
            -> (a , z) ≡ (a , (if b then x else y))
deleteProp1 refl refl = refl


getGeq : ∀ {s x tok map v sig spn mnt tok'}
         -> s ≡ record
                 { datum = tok , x ∷ map
                 ; value = v
                 ; tsig = sig
                 ; continues = true
                 ; spends = spn
                 ; hasToken = true
                 ; mint = mnt
                 ; token = tok'
                 }
         -> Valid s
         -> geq (snd x) emptyValue ≡ true
getGeq refl (allCons {{i}} {{is}} , x , y) = i --geqto≤ i


{-
i-i (pos zero) = refl
i-i +[1+ n ] = i-i (negsuc n)
i-i (negsuc n) rewrite (ltLem n) | (monusLem n) = refl
-}

rewriteLabel : ∀ (pkh : PubKeyHash) (val : Value) (map : AccMap)
               -> (pkh , subValue val val) ∷ map ≡ (pkh , emptyValue) ∷ map
rewriteLabel pkh val label rewrite (v-v val) = refl


sameLastSig' : ∀ {tok x v tsig spends mint token v' spends' mint' token' tsig'} (map : AccMap)
  -> lastSig
      (record
       { datum = tok , x ∷ map
       ; value = v
       ; tsig = tsig
       ; continues = true
       ; spends = spends
       ; hasToken = true
       ; mint = mint
       ; token = token
       })
      ≡
      lastSig
      (record
       { datum = tok , x ∷ map
       ; value = v'
       ; tsig = tsig'
       ; continues = true
       ; spends = spends'
       ; hasToken = true
       ; mint = mint'
       ; token = token'
       })
sameLastSig' [] = refl
sameLastSig' (y ∷ map) = sameLastSig' map

sameLastSig : ∀ {tok x v tsig spends mint token v' spends' mint' token'} (map : AccMap)
  -> lastSig
      (record
       { datum = tok , x ∷ map
       ; value = v
       ; tsig = tsig
       ; continues = true
       ; spends = spends
       ; hasToken = true
       ; mint = mint
       ; token = token
       })
      ≡
      lastSig
      (record
       { datum = tok , map
       ; value = v'
       ; tsig = fst x
       ; continues = true
       ; spends = spends'
       ; hasToken = true
       ; mint = mint'
       ; token = token'
       })
sameLastSig [] = refl 
sameLastSig (x ∷ []) = refl
sameLastSig (x ∷ y ∷ map) = sameLastSig' map


subValid : ∀ {s x tok map v sig spn mnt tok' }
  -> s ≡ (record
             { datum = tok , x ∷ map
             ; value = v
             ; tsig = sig
             ; continues = true
             ; spends = spn
             ; hasToken = true
             ; mint = mnt
             ; token = tok'
             })
  -> Valid s
  -> All (λ y → geq (snd y) emptyValue ≡ true) map
subValid refl (allCons {{i}} {{is}} , x , y) = is


prop1 : ∀ {tok} {map : AccMap} (s s' : State)
        -> datum s ≡ (tok , map)
        -> datum s' ≡ (tok , [])
        -> value s' ≡ 0
        -> tsig s' ≡ lastSig s
        -> value s ≡ sumVal map
        -> continues s ≡ true
        -> continues s' ≡ true
        -> hasToken s ≡ true
        -> hasToken s' ≡ true
        -> spends s ≡ spends s'
        -> mint s ≡ mint s'
        -> token s ≡ token s'
        -> Valid s
        -> s ~[ (makeIs map) ]~* s'
        
prop1 record { datum = (tok , []) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } record { datum = (tok' , map') ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' } refl refl refl refl refl refl refl refl refl refl refl refl p = root
prop1 s@record { datum = (tok , x ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } s'@record { datum = (tok' , map') ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' } refl refl refl refl refl refl refl refl refl refl refl refl p
  = cons {s' = st} (TWithdraw refl refl (lookupProp1 (n=n (fst x)) refl) (getGeq {s} refl p) (geq-refl (snd x)) (deleteProp1 (n=n (fst x))  (rewriteLabel (fst x) (snd x) map)) (commVal (sumVal map) (x .snd)) refl refl refl refl) 
  (cons {s' = st'} (TClose refl refl (lookupProp1 (n=n (fst x)) refl) (deleteProp1 (n=n (fst x)) refl) refl refl refl refl refl)
  (prop1 {tok} {map} st' s' refl refl refl (sameLastSig map) refl refl refl refl refl refl refl refl
  (((subValid {s} refl p)) , refl , refl)))
      where
      st = record
            { datum = tok , ((fst x , emptyValue) ∷ map)
            ; value = sumVal map
            ; tsig = fst x
            ; continues = true
            ; spends = spends
            ; hasToken = true
            ; mint = mint
            ; token = token
            }
      st' = record
             { datum = tok , map
             ; value = sumVal map
             ; tsig = fst x
             ; continues = true
             ; spends = spends
             ; hasToken = true
             ; mint = mint
             ; token = token
             }



liquidity : ∀ (s : State)
          -> Invariant s
          -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (value s' ≡ 0) )

liquidity s@record { datum = (tok , map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } (p@(p1 , p2 , p3) , p4) 
  = ⟨ s' , ⟨ (makeIs map) , ((prop1 s s' refl refl refl refl p4 p2 p2 p3 p3 refl refl refl p) , refl) ⟩ ⟩
  where
  s' = record
       { datum = tok , []
       ; value = 0
       ; tsig = lastSig s
       ; continues = continues
       ; spends = spends
       ; hasToken = hasToken
       ; mint = mint
       ; token = token
       }


{-

-}


{-

rewriteSubL : ∀ {l1 : AccMap} (l2 : AccMap) (pkh : PubKeyHash) (v1 v2 : Value) ->
             l1 ≡ insert pkh (subInteger v1 v2) l2 -> l1 ≡ insert pkh (v1 - v2) l2
rewriteSubL l2 pkh v1 v2 p rewrite sub≡ v1 v2 = p

rewriteAddL : ∀ {l1 : AccMap} (l2 : AccMap) (pkh : PubKeyHash) (v1 v2 : Value) ->
             l1 ≡ insert pkh (addInteger v1 v2) l2 -> l1 ≡ insert pkh (v1 + v2) l2
rewriteAddL l2 pkh v1 v2 p rewrite add≡ v1 v2 = p

doubleRewrite : ∀ {l1 : AccMap} (l2 : AccMap) (from to : PubKeyHash) (vF vT val : Value) ->
             l1 ≡ insert from (subInteger vF val) (insert to (addInteger vT val) l2) ->
             l1 ≡ insert from (vF - val) (insert to (vT + val) l2)
doubleRewrite l2 from to vF vT val p rewrite add≡ vT val | sub≡ vF val = p

rewriteSub : ∀ {a} (b c : Value) -> a ≡ subInteger b c -> a ≡ b - c
rewriteSub b c p rewrite sub≡ b c = p

rewriteAdd : ∀ {a} (b c : Value) -> a ≡ addInteger b c -> a ≡ b + c
rewriteAdd b c p rewrite add≡ b c = p
-}

getS : Label -> ScriptContext -> State
getS (tok , map) ctx = record
                               { datum = (tok , map)
                               ; value = oldValue ctx
                               ; tsig = 0 
                               ; continues = true
                               ; spends = 0
                               ; hasToken = checkTokenIn tok ctx --hasTokenIn ctx
                               ; mint = 0
                               ; token = 0 , 0
                               }


getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
                { datum = newDatum ctx
                ; value = newValue ctx
                ; tsig = sig ctx
                ; continues = continuing ctx
                ; spends = iRef ctx
                ; hasToken = checkTokenOut (ownAssetClass tn ctx) ctx
                ; mint = getMintedAmount ctx
                ; token = ownAssetClass tn ctx
                }

getS' : ScriptContext -> State
getS' ctx = record
                               { datum = newDatum ctx
                               ; value = newValue ctx
                               ; tsig = sig ctx
                               ; continues = continuing ctx
                               ; spends = iRef ctx
                               ; hasToken = checkTokenOut (newDatum ctx .fst) ctx --hasTokenOut ctx
                               ; mint = getMintedAmount ctx
                               ; token = (0 , 0)
                               }


checkWithdraw' : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> Label -> Bool
checkWithdraw' tok Nothing _ _ _ _ = false
checkWithdraw' tok (Just v) pkh val lab (tok' , map) = geq val emptyValue && geq v val && ((tok' , map) == (tok , insert pkh (subValue v val) lab)) --(addInteger v (negateInteger val))

checkDeposit' : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> Label -> Bool
checkDeposit' tok Nothing _ _ _ _ = false
checkDeposit' tok (Just v) pkh val lab (tok' , map) = geq val emptyValue && ((tok' , map) == (tok , insert pkh (addValue v val) lab))

checkTransfer' : AssetClass -> Maybe Value -> Maybe Value -> PubKeyHash -> PubKeyHash -> Value -> AccMap -> Label -> Bool
checkTransfer' tok Nothing _ _ _ _ _ _ = false
checkTransfer' tok (Just vF) Nothing _ _ _ _ _ = false
checkTransfer' tok (Just vF) (Just vT) from to val lab (tok' , map) = geq val emptyValue && geq vF val && from /= to &&
                         (tok' , map) == (tok , insert from (subValue vF val) (insert to (addValue vT val) lab))


==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==to≡ fst1 fst2 (get pf))
        | (==vto≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl
        
==Lto≡ : ∀ (a b : AccMap) -> (a == b) ≡ true -> a ≡ b
==Lto≡ [] [] pf = refl
==Lto≡ (x ∷ a) (y ∷ b) pf
  rewrite (==pto≡ x y (get pf)) = cong (λ x → y ∷ x) ((==Lto≡ a b (go (x == y) pf)))

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ (l : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Cleanup
                           -> (pf : agdaValidator l i ctx ≡ true)
                           -> getS l ctx ~[ i ]~> getS' ctx
                              

validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Just _ = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (pkh == (sig ctx)) pf)
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Nothing with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Nothing | tok' , map'
     rewrite sym (==tto≡ tok' tok (get (get (go (pkh == (sig ctx)) ((go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==Lto≡ map' (insert pkh emptyValue map) (go (tok' == tok) (get (go (pkh == sig ctx) 
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) 
             = TOpen refl (==to≡ pkh (sig ctx) (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
               eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ((tok' , map') == (tok , insert pkh emptyValue map)) (go (pkh == sig ctx) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
               refl (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) (get pf) (get (go (checkTokenIn tok ctx) pf))

validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (pkh == (sig ctx)) pf) 
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Just v | tok' , map' rewrite
            ==vto≡ v emptyValue (get (go (pkh == (sig ctx))
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            | ==tto≡ tok' tok (get (get (go (v == emptyValue) (go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
            | ==Lto≡ map' (delete pkh map) (go (tok' == tok) (get (go (v == emptyValue) (go (pkh == (sig ctx)) 
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) 
            = TClose refl (==to≡ pkh (sig ctx) (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
              eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ( (tok' , map') == (tok , delete pkh map)) (go (v == emptyValue)
              (go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) 
              refl (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) (get pf) (get (go (checkTokenIn tok ctx) pf))

validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (pkh == (sig ctx)) pf)
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Just v | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (geq v val) (go (geq val emptyValue) (get (go (pkh == (sig ctx))
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
             | (==Lto≡ map' (insert pkh (subValue v val) map)
             (go (tok' == tok) (go (geq v val) (go (geq val emptyValue) (get (go (pkh == (sig ctx))
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
            = TWithdraw refl (==to≡ pkh (sig ctx) (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            eq (get (get (go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
            (get (go (geq val emptyValue) (get (go (pkh == (sig ctx)) (go (continuing ctx)
            (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) eq2 
            (==vto≡ (addValue (newValue ctx) val) (oldValue ctx) (go (checkWithdraw' tok (Just v) pkh val map (tok' , map'))
            ((go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))          
            refl (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) (get pf) (get (go (checkTokenIn tok ctx) pf))

validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (pkh == (sig ctx)) pf)
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Just v | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (geq val emptyValue) (get (go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==Lto≡ map' (insert pkh (addValue v val) map)
             (go (tok' == tok) (go (geq val emptyValue)  (get (go (pkh == (sig ctx))
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
             = TDeposit refl (==to≡ pkh (sig ctx) (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
             eq (get (get (go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
             eq2 (==vto≡ (newValue ctx) (addValue (oldValue ctx) val) (go (checkDeposit' tok (Just v) pkh val map (tok' , map'))
             ((go (pkh == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
             refl (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) (get pf) (get (go (checkTokenIn tok ctx) pf))

validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf with lookup from map in eq1
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (from == (sig ctx)) pf)
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF with lookup to map in eq2
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (from == (sig ctx)) pf)
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT with newDatum ctx in eq3
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (from == (sig ctx))
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))))
  | ==Lto≡ map' (insert from (subValue vF val) (insert to (addValue vT val) map))
  (go (tok' == tok) (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (from == (sig ctx))
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
    = TTransfer refl ((==to≡ from (sig ctx) (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) eq1 eq2
    (get (get (go (from == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
    (get (go (geq val emptyValue) (get (go (from == (sig ctx)) 
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
    (/=to≢ from to (get (go (geq vF val) (go (geq val emptyValue) (get (go (from == (sig ctx))
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))) eq3  
    (==vto≡ (newValue ctx) (oldValue ctx) (go (checkTransfer' tok (Just vF) (Just vT) from to val map (tok' , map')) (go (from == (sig ctx)) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
    refl (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) (get pf) (get (go (checkTokenIn tok ctx) pf))
validatorImpliesTransition (tok , map) Cleanup ctx iv pf = ⊥-elim (iv refl)

mintingImpliesStart : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≡ 1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> record {address = adr ; outputRef = oref ; tokName = tn} ⊢ getMintS tn ctx
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut =  hasTokenOut ; mint = + 1 ; tokCurrSymbol = cs } refl pf
  rewrite  ==Lto≡ l [] (go ((cs , tn) == tok) (get (go (oref == inputRef) (go continues pf))))
  = TStart refl 
    refl (get pf) (==to≡ oref inputRef (get (go continues pf)))
    (==tto≡ (cs , tn) tok (get (get (go (oref == inputRef) (go continues pf))))) refl
    (go (checkDatum adr tn ctx) (go (oref == inputRef) (go continues pf)))


l=l : ∀ (l : AccMap) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite n=n (fst x) | v=v (snd x) = l=l l

bothImplyCleanup : ∀ {tn} (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
                   -> getMintedAmount ctx ≡ -1
                   -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tn tt ctx) ≡ true
                   -> getS l ctx ~[ Cleanup ]~| getS' ctx
bothImplyCleanup d adr oref ctx refl pf = TCleanup (==Lto≡ (snd d) [] (go (not (continuing ctx)) (go (not (checkTokenOut (d . fst) ctx)) (go (checkTokenIn (d . fst) ctx) (get pf))))) refl refl (unNot (get (go (not (checkTokenOut (d . fst) ctx)) (go (checkTokenIn (d . fst) ctx) (get pf))))) (get (get pf)) (unNot (get (go (checkTokenIn (d . fst) ctx) (get pf))))


transitionImpliesValidator : ∀ (l : Label) (i : Input) (ctx : ScriptContext)
                           -> getS l ctx ~[ i ]~> getS' ctx
                           -> agdaValidator l i ctx ≡ true
transitionImpliesValidator (tok , map) (Open pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TOpen refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n pkh | l=l (insert pkh emptyValue map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Close pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TClose refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n pkh | l=l (delete pkh map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Withdraw pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TWithdraw {v = v} refl refl p3 p4 p5 refl refl p8 refl refl refl) rewrite p3 | n=n pkh | v=v (addValue outputVal val) | l=l (insert pkh (subValue v val) map) | p4 | p5 | t=t tok = refl
transitionImpliesValidator (tok , map) (Deposit pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TDeposit {v = v} refl refl p3 p4 refl refl p7 refl refl refl) rewrite p3 | n=n pkh | v=v (addValue inputVal val) | l=l (insert pkh (addValue v val) map) | p4 | t=t tok = refl
transitionImpliesValidator (tok , map) (Transfer from to val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl p10 refl refl refl) rewrite p3 | p4 | ≢to/= from to p7 | n=n from | v=v inputVal | l=l (insert from (subValue vF val) (insert to (addValue vT val) map)) | p5 | p6 | t=t tok = refl


startImpliesMinting : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> record {address = adr ; outputRef = oref ; tokName = tn } ⊢ getMintS tn ctx
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TStart refl refl refl refl refl refl refl) rewrite n=n oref | t=t tok = refl


cleanupImpliesBoth : ∀ {tn} (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
  -> getS l ctx ~[ Cleanup ]~| getS' ctx
  -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tn tt ctx) ≡ true
cleanupImpliesBoth d adr oref ctx (TCleanup refl refl refl refl refl refl) = refl


data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase

record Argument : Set where
  field
    adr  : Address
    oref : TxOutRef
    tn   : TokenName
    dat  : Label
    inp  : Input
    ctx  : ScriptContext 
open Argument


Classifier : Argument -> Phase
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } = Initial
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Open x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero)  } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Close x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer x x₁ x₂) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Terminal

totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running = agdaValidator (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .dat) (arg .inp) (arg .ctx) &&
              agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)

totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial = record { address = arg .adr ; outputRef = arg .oref ; tokName = arg .tn}
                       ⊢ getMintS (arg .tn) (arg .ctx)
... | Running = getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx) 
... | Terminal =  getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .ctx) 

record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


removeCleanup : ∀ (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx)
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Open x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Open x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Close x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Close x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Withdraw x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Withdraw x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Deposit x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Deposit x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Transfer x x₁ x₂) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Transfer x x₁ x₂) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = Cleanup ; ctx = ctx₁ } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx₁) (negsuc 0) (get (go (checkTokenIn (dat₁ .fst) ctx₁) p2))))



totalEquiv' : totalF ≈ totalR
totalEquiv' = record { to = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } } x → removeCleanup arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } } x → mintingImpliesStart adr oref tn tt ctx refl x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } } x → removeCleanup arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Open pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Close pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Deposit pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Withdraw pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Transfer from to v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → bothImplyCleanup {0} dat adr oref ctx refl x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } } x → removeCleanup arg (λ ()) x }
                     ; from = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } } x → transitionImpliesValidator dat inp ctx x ;
                                { record { adr = adr ; oref = oref ; tn = tn ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } } x → startImpliesMinting adr oref tn tt ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } } x → transitionImpliesValidator dat inp ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Open pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Close pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Deposit pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Withdraw pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Transfer from to v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → cleanupImpliesBoth {0} dat adr oref ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } } x → transitionImpliesValidator dat inp ctx x } } 

















