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

-- Model and proofs for the Account Simulation contract

-- Extra definitions necessary for the model
sumVal : AccMap -> Value
sumVal [] = minValue
sumVal ((k , v) ∷ xs) = addValue v (sumVal xs)

_∈_ : ∀ (x : PubKeyHash) (xs : AccMap) → Set
x ∈ xs = Any (\y -> x ≡ fst y) xs

_∉_ : ∀ (x : PubKeyHash) (xs : AccMap) → Set
x ∉ xs = ¬ (x ∈ xs)

data Unique : AccMap → Set where
  root : Unique []
  _::_ : {x : PubKeyHash} {v : Value} {map : AccMap} -> x ∉ map -> Unique map -> Unique ((x , v) ∷ map)
  
-- The States of the State Transition System
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

-- Model paramets consisting of the combined parameters of the validator and minting policy
record MParams : Set where
    field
        address   : Address
        outputRef : TxOutRef
        tokName   : TokenName
open MParams public

--Transition Rules

--The Initial Transition
data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s tok}
    -> datum s ≡ ( tok , [] )
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> token s ≡ tok
    -> token s .snd ≡ tokName par
    -> value s ≡ minValue
    -> hasToken s ≡ true
    -------------------
    -> par ⊢ s

-- The Running Transitions
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

-- The Terminal Transition
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


-- Validity predicate
Valid : State -> Set 
Valid s = All (\y -> geq (snd y) emptyValue ≡ true) (snd (datum s)) × continues s ≡ true × hasToken s ≡ true

-- Fidelity predicate
Fides : State -> Set
Fides s = value s ≡ sumVal (snd (datum s))

-- Combined state invariant predicate
Invariant : State -> Set
Invariant s = (Valid s × Fides s)

-- Lemmas for Fidelity
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

-- Fidelity Proof
initialFidelity : ∀ {s par}
  -> par ⊢ s
  -> Fides s
initialFidelity {record { datum = .(_ , []) ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl x₁ x₂ x₃ x₄ x₅ x₆ x₇) = x₆

fidelity : ∀ {s s' : State} {i : Input}
         -> Fides s
         -> s ~[ i ]~> s'
         -> Fides s'
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Open _} pf (TOpen refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma1 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Close _} pf (TClose refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma2 map p3 
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Withdraw _ _} pf (TWithdraw refl refl p3 p4 p5 p6 p7 p8 p9 p10 p11) rewrite pf | p6 = svLemma4 {pkh = State.tsig s'} {map = map} p3 p7
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Deposit _ _} pf (TDeposit refl p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 | p6 | pf = svLemma3 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Transfer _ _ _} pf (TTransfer refl p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13) rewrite p8 | p9 | pf = svLemma5 map p3 p4 p7


-- Lemmas for Validity
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

-- Validity Proof
initialValidity : ∀ {s par}
  -> par ⊢ s
  -> Valid s
initialValidity {record { datum = .(_ , []) ; value = emptyValue ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl p3 p4 p5 p6 p7 p8 p9) = allNil , p4 , p9

validity : ∀ {s s' : State} {i}
  -> Valid s
  -> s ~[ i ]~> s'
  -> Valid s'
validity {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ emptyValue map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TOpen refl p2 p3 refl p5 p6 p7 p8 p9) = (lem map emptyValue refl fst) , p7 , p9
validity {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , delete _ map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TClose refl p2 p3 refl p5 p6 p7 p8 p9) = (delem map fst) , p7 , p9
validity {record { datum = tok , map ; value = .(addValue value₁ val) ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ (subValue v val) map) ; value = value₁ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl p8 p9 p10 p11) = (lem map (subValue v val) (diffLemma v val p5 p4) fst) , p9 , p11
validity {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert _ (addValue v val) map) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6 p7 p8 p9 p10) = lem map (addValue v val) (sumLemma v val (geqLem map v fst p3) p4) fst , p8 , p10
validity {record { datum = tok , map ; value = value₁ ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} {record { datum = .(_ , insert from (subValue vF val) (insert to (addValue vT val) map)) ; value = value₂ ; tsig = tsig₂ ; continues = continues₂ ; spends = spends₂ ; hasToken = hasToken₂ ; mint = mint₂ ; token = token₂ }} (fst , snd , thd) (TTransfer {from} {to} {val} {vF = vF} {vT = vT} refl p2 p3 p4 p5 p6 p7 refl p9 p10 p11 p12 p13) = lem (insert to (addValue vT val) map) (subValue vF val) (diffLemma vF val p6 p5) (lem map (addValue vT val) (sumLemma vT val (geqLem map vT fst p4) p5) fst) , p11 , p13

-- Invariant proofs
initialInvariant : ∀ {s par}
  -> par ⊢ s
  -> Invariant s
initialInvariant p = (initialValidity p) , (initialFidelity p)

stateInvariant : ∀ {s s' : State} {i}
  -> Invariant s
  -> s ~[ i ]~> s'
  -> Invariant s'
stateInvariant (valid , fides) p = validity valid p , fidelity fides p


-- Lemmas for Liquidity
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

lookupProp : ∀ {b : Bool} {a : Set} { x y z : Maybe a }
            -> b ≡ true
            -> x ≡ z
            -> (if b then x else y) ≡ z
lookupProp refl refl = refl

deleteProp : ∀ {a : AssetClass} {b : Bool} { x y z : AccMap }
            -> b ≡ true
            -> x ≡ z
            -> (a , z) ≡ (a , (if b then x else y))
deleteProp refl refl = refl

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

-- You can withdraw all money from each account and then close it, one by one
prop1 : ∀ {tok} {map : AccMap} (s s' : State)
        -> datum s ≡ (tok , map)
        -> datum s' ≡ (tok , [])
        -> value s' ≡ minValue
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
  = cons {s' = st} (TWithdraw refl refl (lookupProp (n=n (fst x)) refl) (getGeq {s} refl p) (geq-refl (snd x)) (deleteProp (n=n (fst x))  (rewriteLabel (fst x) (snd x) map)) (commVal (sumVal map) (x .snd)) refl refl refl refl) 
  (cons {s' = st'} (TClose refl refl (lookupProp (n=n (fst x)) refl) (deleteProp (n=n (fst x)) refl) refl refl refl refl refl)
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

-- Multi-Step transition lemma
lemmaMultiStep : ∀ (s s' s'' : State) (is is' : List Input)
                   -> s  ~[ is  ]~* s'
                   -> s' ~[ is' ]~* s''
                   -> s  ~[ is ++ is' ]~* s''
lemmaMultiStep s .s s'' [] is' root p2 = p2
lemmaMultiStep s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep s''' s' s'' is is' p2 p3)
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''} p1) root = fin p1
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (cons (TOpen x₇ x₈ x₉ x₁₀ x₁₁ refl x₁₃ x₁₄ x₁₅) p3)
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (cons (TClose x₇ x₈ x₉ x₁₀ x₁₁ refl x₁₃ x₁₄ x₁₅) p3) 
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (cons (TWithdraw x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ refl x₁₅ x₁₆ x₁₇) p3)
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (cons (TDeposit x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ refl x₁₄ x₁₅ x₁₆) p3)
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (cons (TTransfer x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ refl x₁₇ x₁₈ x₁₉) p3)
lemmaMultiStep s s' s'' (x ∷ is) is' (fin {s' = s'''}
  (TCleanup x₁ x₂ x₃ () x₅ x₆)) (fin (TCleanup x₇ x₈ refl x₁₀ x₁₁ x₁₂))


--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
liquidity : ∀ (s : State)
          -> Invariant s
          -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (value s' ≡ emptyValue) )

liquidity s@record { datum = (tok , map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } (p@(p1 , p2 , p3) , p4) 
  = ⟨ s'' , ⟨ (makeIs map) ++ [ Cleanup ] , (lemmaMultiStep s s' s'' (makeIs map) [ Cleanup ]
    (prop1 s s' refl refl refl refl p4 p2 p2 p3 p3 refl refl refl p) (fin (TCleanup refl refl p2 refl p3 refl)) , refl) ⟩ ⟩
  where
  s'' = record
       { datum = tok , []
       ; value = emptyValue
       ; tsig = lastSig s
       ; continues = false
       ; spends = spends
       ; hasToken = false
       ; mint = negsuc 0
       ; token = token
       }
  s' = record
       { datum = tok , []
       ; value = minValue
       ; tsig = lastSig s
       ; continues = continues
       ; spends = spends
       ; hasToken = hasToken
       ; mint = mint
       ; token = token
       }



-- Extracting the State from ScriptContext

-- Starting State for normal transitions
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


-- Initial State when we mint the token and put the smart contract on the blockchain
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

-- Resulting State for normal transitions
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


-- Lemmas and helper functions for validator returning true implies transition
checkWithdraw' : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> Label -> Bool
checkWithdraw' tok Nothing _ _ _ _ = false
checkWithdraw' tok (Just v) pkh val lab (tok' , map) = geq val emptyValue && geq v val && ((tok' , map) == (tok , insert pkh (subValue v val) lab))

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

map=map : ∀ (l : AccMap) -> (l == l) ≡ true
map=map [] = refl
map=map (x ∷ l) rewrite n=n (fst x) | v=v (snd x) = map=map l


--Validator returning true implies we can perform a transition
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


-- Minting the token implies we are in the initial state of our model
mintingImpliesStart : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≡ 1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> record {address = adr ; outputRef = oref ; tokName = tn} ⊢ getMintS tn ctx
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut =  hasTokenOut ; mint = + 1 ; tokCurrSymbol = cs } refl pf
  rewrite  ==Lto≡ l [] (go ((cs , tn) == tok) (get (go (oref == inputRef) (go continues pf))))
  = TStart refl 
    refl (get pf) (==to≡ oref inputRef (get (go continues pf)))
    (==tto≡ (cs , tn) tok (get (get (go (oref == inputRef) (go continues pf))))) refl
    (==vto≡ outputVal minValue (go hasTokenOut (go (checkDatum adr tn ctx) (go (oref == inputRef) (go continues pf)))))
    (get (go (checkDatum adr tn ctx) (go (oref == inputRef) (go continues pf))))


-- Validator returning true and burning a token implies we are in the terminal state 
bothImplyCleanup : ∀ {tn} (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
                   -> getMintedAmount ctx ≡ -1
                   -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tn tt ctx) ≡ true
                   -> getS l ctx ~[ Cleanup ]~| getS' ctx
bothImplyCleanup d adr oref ctx refl pf = TCleanup (==Lto≡ (snd d) [] (go (not (continuing ctx)) (go (not (checkTokenOut (d . fst) ctx)) (go (checkTokenIn (d . fst) ctx) (get pf))))) refl refl (unNot (get (go (not (checkTokenOut (d . fst) ctx)) (go (checkTokenIn (d . fst) ctx) (get pf))))) (get (get pf)) (unNot (get (go (checkTokenIn (d . fst) ctx) (get pf))))



-- Performing a transition implies that the validator returns true
transitionImpliesValidator : ∀ (l : Label) (i : Input) (ctx : ScriptContext)
                           -> getS l ctx ~[ i ]~> getS' ctx
                           -> agdaValidator l i ctx ≡ true
transitionImpliesValidator (tok , map) (Open pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TOpen refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n pkh | map=map (insert pkh emptyValue map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Close pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TClose refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n pkh | map=map (delete pkh map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Withdraw pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TWithdraw {v = v} refl refl p3 p4 p5 refl refl p8 refl refl refl) rewrite p3 | n=n pkh | v=v (addValue outputVal val) | map=map (insert pkh (subValue v val) map) | p4 | p5 | t=t tok = refl
transitionImpliesValidator (tok , map) (Deposit pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TDeposit {v = v} refl refl p3 p4 refl refl p7 refl refl refl) rewrite p3 | n=n pkh | v=v (addValue inputVal val) | map=map (insert pkh (addValue v val) map) | p4 | t=t tok = refl
transitionImpliesValidator (tok , map) (Transfer from to val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl p10 refl refl refl) rewrite p3 | p4 | ≢to/= from to p7 | n=n from | v=v inputVal | map=map (insert from (subValue vF val) (insert to (addValue vT val) map)) | p5 | p6 | t=t tok = refl


-- Being in the initial model state implies we can mint a token
startImpliesMinting : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> record {address = adr ; outputRef = oref ; tokName = tn } ⊢ getMintS tn ctx
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } (TStart refl refl refl refl refl refl refl refl) rewrite n=n oref | t=t tok = refl 


-- Getting to the terminal state implies that the validator returns true and a token can be burned
cleanupImpliesBoth : ∀ {tn} (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
  -> getS l ctx ~[ Cleanup ]~| getS' ctx
  -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tn tt ctx) ≡ true
cleanupImpliesBoth d adr oref ctx (TCleanup refl refl refl refl refl refl) = refl


-- Defining the components for the equivalence relation between the model and the validator.

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

-- The Equivalence Relation
record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

-- If we mint exactly 1 token we are in the Initial Phase
-- If we burn a token and the input is Close, we are in the Terminal Phase
-- Otherwise we are in the Running Phase
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

-- The Validator as a function returning a boolean
totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running = agdaValidator (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .dat) (arg .inp) (arg .ctx) &&
              agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)


-- The State Transition System as a relation
totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial = record { address = arg .adr ; outputRef = arg .oref ; tokName = arg .tn}
                       ⊢ getMintS (arg .tn) (arg .ctx)
... | Running = getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx) 
... | Terminal =  getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .ctx) 

-- Lemma for when the input is Close
removeCleanup : ∀ (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx)
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Open x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Open x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Close x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Close x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Withdraw x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Withdraw x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Deposit x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Deposit x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Transfer x x₁ x₂) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Transfer x x₁ x₂) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = Cleanup ; ctx = ctx₁ } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx₁) (negsuc 0) (get (go (checkTokenIn (dat₁ .fst) ctx₁) p2))))


-- The proof of equivalence
totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } } x → removeCleanup arg (λ ()) x ;
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

















