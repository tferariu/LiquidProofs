open import Validators.AccountSim
open import Lib
open import SimpleValue
open import ScriptContext Label Value

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
open import Haskell.Prelude using (lookup)


open import Function.Base using (_∋_)

open import ProofLib

module Proofs.AccountSimProofs where

sumVal : AccMap -> Integer
sumVal [] = 0
sumVal ((k , v) ∷ xs) = v + sumVal xs


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
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s tok}
    -> datum s ≡ ( tok , [] )
    -> value s ≡ 0
    -> mint s ≡ 1
    -> continues s ≡ true
    -> outputRef par ≡ spends s
    -> token s ≡ tok
    -> hasToken s ≡ true
    -------------------
    -> par ⊢ s

--Transition Rules
data _~[_]~>_ : State -> Input -> State -> Set where
 
  TOpen : ∀ {pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> pkh ≡ tsig s'
    -> lookup pkh map ≡ Nothing
    -> datum s' ≡ (tok ,  insert pkh 0 map)
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
    -> lookup pkh map ≡ Just 0
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
    -> val ≥ emptyValue
    -> v ≥ val
    -> datum s' ≡ (tok , (insert pkh (v - val) map))
    -> value s' + val ≡ value s
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
    -> val ≥ emptyValue
    -> datum s' ≡ (tok , (insert pkh (v + val) map))
    -> value s' ≡ value s + val
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
    -> val ≥ emptyValue
    -> vF ≥ val
    -> from ≢ to
    -> datum s' ≡ (tok , (insert from (vF - val) (insert to (vT + val) map)))
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



data Valid : State -> Set where

  Stp : ∀ {s}
    -> continues s ≡ false
    ----------------
    -> Valid s

  Oth : ∀ {s}
    -> value s ≡ sumVal (snd (datum s))
    -> All (\y -> geq (snd y) emptyValue ≡ true) (snd (datum s))
    ----------------
    -> Valid s


svLemma1 : ∀ {pkh} (map : AccMap) -> lookup pkh map ≡ Nothing -> sumVal map ≡ sumVal (insert pkh +0 map)
svLemma1 [] p = refl
svLemma1 {pkh} (x ∷ l) p with pkh == (fst x) in eq
...| false = cong (λ a → snd x + a) (svLemma1 l p)
...| true = ⊥-elim (maybe⊥ (sym p))

svLemma2 : ∀ {pkh} (map : AccMap) -> lookup pkh map ≡ Just +0 -> sumVal map ≡ sumVal (delete pkh map)
svLemma2 [] p = refl
svLemma2 {pkh} (x ∷ l) p with pkh == (fst x) in eq
...| false = cong (λ a → snd x + a) (svLemma2 l p)
...| true rewrite (maybe≡ p) | +-identityˡ (sumVal l) = refl

svLemma3 : ∀ {pkh v val} (map : AccMap) -> lookup pkh map ≡ Just v
           -> sumVal map + val ≡ sumVal (insert pkh (v + val) map)
svLemma3 [] p = ⊥-elim (maybe⊥ p) --refl
svLemma3 {pkh} {v} {val} (x ∷ l) p with pkh == (fst x) in eq
...| false rewrite (+-assoc (snd x) (sumVal l) val)
     = cong (λ a → snd x + a) (svLemma3 l p)
...| true rewrite (maybe≡ p) | (+-assoc v (sumVal l) val)
                  | +-comm (sumVal l) val
                  | (+-assoc v val (sumVal l)) = refl 


svLemma4 : ∀ {from to vF vT val} (map : AccMap) -> lookup from map ≡ Just vF
           -> lookup to map ≡ Just vT -> from ≢ to
           -> sumVal map ≡ sumVal (insert from (vF + - val) (insert to (vT + val) map))
svLemma4 [] p1 p2 p3 = ⊥-elim (maybe⊥ p1)
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 with to == (fst x) in eq1
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true with from == to in eq2
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | true = ⊥-elim (p3 (==to≡ from to eq2))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false with from == (fst x) in eq3
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false | true
         rewrite ==to≡ to (fst x) eq1 | ==to≡ from (fst x) eq3 = ⊥-elim (p3 refl)
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false | false
         rewrite (maybe≡ p2) | +-assoc vT val (sumVal (insert from (vF + - val) l))
         = cong (λ a → vT + a) (switchSides {b = val} (svLemma3 l p1))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false with from == (fst x) in eq2
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false | true
         rewrite (maybe≡ p1) | +-assoc vF (- val) (sumVal (insert to (vT + val) l))
         = cong (λ a → vF + a) (switchSides' {b = (val)} (svLemma3 l p2))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false | false
         = cong (λ a → snd x + a) (svLemma4 l p1 p2 p3)

svLemma5 : ∀ {x v v1 pkh l} -> lookup pkh l ≡ Just v -> x + v1 ≡ sumVal l -> x ≡ sumVal (insert pkh (v + - v1) l)
svLemma5 {x} {v} {v1} {pkh} {l} p1 p2 rewrite switchSides' {x} {v1} p2 | +-comm (- v1) (sumVal l) = svLemma3 l p1

fidelity : ∀ {s s' : State} {i : Input}
         -> value s ≡ sumVal (snd (datum s))
         -> s ~[ i ]~> s'
         -> value s' ≡ sumVal (snd (datum s'))
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Open _} pf (TOpen refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma1 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Close _} pf (TClose refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma2 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Withdraw _ _} pf (TWithdraw refl refl p3 p4 p5 p6 p7 p8 p9 p10 p11) rewrite pf | p6 = svLemma5 {pkh = State.tsig s'} {l = map} p3 p7
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Deposit _ _} pf (TDeposit refl p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 | p6 | pf = svLemma3 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Transfer _ _ _} pf (TTransfer refl p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13) rewrite p8 | p9 | pf = svLemma4 map p3 p4 p7

fidelityMulti : ∀ {s s' : State} {is : List Input}
  -> value s ≡ sumVal (snd (datum s))
  -> s ~[ is ]~* s'
  -> (value s' ≡ sumVal (snd (datum s')) ⊎ continues s' ≡ false)
fidelityMulti {s} {s} {[]} p1 root = inj₁ p1 
fidelityMulti {s} {s'} {(i ∷ is)} p1 (cons {s' = s''} x p2) = fidelityMulti (fidelity p1 x) p2
fidelityMulti {s} {s'} {i ∷ is} p1 (fin {s' = s''} (TCleanup x x₂ x₃ x₄ x₅ x₆)) = inj₂ x₄

diffSubLemma : ∀ (n m : Nat) -> 0 N.≤ m -> m N.≤ n ->
               geq (+ n - + m) emptyValue ≡ true
diffSubLemma zero .zero N.z≤n N.z≤n = refl
diffSubLemma (N.suc n) .zero N.z≤n N.z≤n = refl
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) with ltNat n m in eq
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | true = ⊥-elim (nope n m eq (≤NtoleqN p2))
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | false = geqNatLemma (monusNat n m) 

diffLemma : ∀ (v v' : Value) -> v' ≤ v -> emptyValue ≤ v' -> geq (v - v') emptyValue ≡ true
diffLemma v v' (-≤- n≤m) ()
diffLemma v v' -≤+ ()
diffLemma v v' (+≤+ {m} {n} 0≤m) (+≤+ m≤n) = diffSubLemma n m m≤n 0≤m

geqPosLemma : ∀ (n : Nat) -> geq (+ n) emptyValue ≡ true
geqPosLemma zero = refl
geqPosLemma (N.suc n) = refl

sumLemma : ∀ (v v' : Value) -> emptyValue ≤ v' -> geq v emptyValue ≡ true -> geq (v + v') emptyValue ≡ true
sumLemma (pos n) (pos m) p1 p2 = geqPosLemma (addNat n m)

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
validStateInitial {record { datum = .(_ , []) ; value = .0 ; tsig = tsig₁ ; continues = continues₁ ; spends = spends₁ ; hasToken = hasToken₁ ; mint = mint₁ ; token = token₁ }} (TStart refl refl p3 p4 p5 p6 p7) = Oth refl allNil

validStateTransition : ∀ {s s' : State} {i}
  -> Valid s
  -> s ~[ i ]~> s'
  -> Valid s'
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ 0 map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Oth a1 a2) t@(TOpen refl p2 p3 refl p5 p6 p7 p8 p9) = Oth (fidelity a1 t) (lem map 0 refl a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(delete _ map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Oth a1 a2) t@(TClose refl p2 p3 refl p5 p6 p7 p8 p9) = Oth (fidelity a1 t) (delem map a2)
validStateTransition {record { datum = tok , map ; value = v1 ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (v - val) map) ; value = v2 ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Oth a1 a2) t@(TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl p8 p9 p10 p11) = Oth (fidelity a1 t) (lem map (v - val) (diffLemma v val p5 p4) a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (v + val) map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Oth a1 a2) t@(TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6 p7 p8 p9 p10) = Oth (fidelity a1 t) (lem map (v + val) (sumLemma v val p4 (geqLem map v a2 p3)) a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (vF - val) (insert _ (vT + val) map)) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Oth a1 a2) t@(TTransfer {from} {to} {val} {vF = vF} {vT = vT} refl p2 p3 p4 p5 p6 p7 refl p9 p10 p11 p12 p13) = Oth (fidelity a1 t) (lem (insert to (vT + val) map) (vF - val) (diffLemma vF val p6 p5) (lem map (vT + val) (sumLemma vT val p5 (geqLem map vT a2 p4)) a2))
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = tok' , map' ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Stp refl) (TOpen x x₁ x₂ x₃ x₄ () x₆ x₇ x₈)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = tok' , map' ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Stp refl) (TClose x x₁ x₂ x₃ x₄ () x₆ x₇ x₈)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = tok' , map' ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Stp refl) (TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆ () x₈ x₉ x₁₀) 
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = tok' , map' ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Stp refl) (TDeposit x x₁ x₂ x₃ x₄ x₅ () x₇ x₈ x₉)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = tok' , map' ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Stp refl) (TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ () x₁₀ x₁₁ x₁₂)

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


geqto≤ : ∀ {a b} -> geq a b ≡ true -> a ≥ b
geqto≤ {pos n} {pos m} pf = +≤+ (leqNto≤N' pf)
geqto≤ {pos n} {negsuc m} pf = -≤+
geqto≤ {negsuc n} {negsuc m} pf = -≤- (leqNto≤N pf)


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
         -> snd x ≥ emptyValue
getGeq refl (Oth x (allCons {{i}} {{is}})) = geqto≤ i

i-i : ∀ (i : Integer) -> i - i ≡ emptyValue
i-i (pos zero) = refl
i-i +[1+ n ] = i-i (negsuc n)
i-i (negsuc n) rewrite (ltLem n) | (monusLem n) = refl

rewriteLabel : ∀ (pkh : PubKeyHash) (val : Value) (map : AccMap)
               -> (pkh , val - val) ∷ map ≡ (pkh , emptyValue) ∷ map
rewriteLabel pkh val label rewrite (i-i val) = refl


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


subValid : ∀ {x tok map v sig spn mnt tok' }
  -> Valid (record
             { datum = tok , x ∷ map
             ; value = v
             ; tsig = sig
             ; continues = true
             ; spends = spn
             ; hasToken = true
             ; mint = mnt
             ; token = tok'
             })
  -> All (λ y → geq (snd y) emptyValue ≡ true) map
subValid (Oth x (allCons {{i}} {{is}})) = is


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
prop1 record { datum = (tok , x ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } s'@record { datum = (tok' , map') ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' } refl refl refl refl refl refl refl refl refl refl refl refl p
  = cons {s' = st} (TWithdraw refl refl (lookupProp1 (n=n (fst x)) refl) (getGeq refl p) ≤-refl (deleteProp1 (n=n (fst x))  (rewriteLabel (fst x) (snd x) map)) (+-comm (sumVal map) (x .snd)) refl refl refl refl) 
  (cons {s' = st'} (TClose refl refl (lookupProp1 (n=n (fst x)) refl) (deleteProp1 (n=n (fst x)) refl) refl refl refl refl refl)
  (prop1 {tok} {map} st' s' refl refl refl (sameLastSig map) refl refl refl refl refl refl refl refl (Oth refl (subValid p))))
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
          -> value s ≡ sumVal (snd (datum s))
          -> Valid s
          -> continues s ≡ true
          -> hasToken s ≡ true
          -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (value s' ≡ 0) )

liquidity s@record { datum = (tok , map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } p1 p2 p3 p4
  = ⟨ s' , ⟨ (makeIs map) , ((prop1 s s' refl refl refl refl p1 p3 p3 p4 p4 refl refl refl p2) , refl) ⟩ ⟩
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


==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==to≡ fst1 fst2 (get pf))
        | (==ito≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl

==Lto≡ : ∀ (a b : AccMap) -> (a == b) ≡ true -> a ≡ b
==Lto≡ [] [] pf = refl
==Lto≡ (x ∷ a) (y ∷ b) pf
  rewrite (==pto≡ x y (get pf)) = cong (λ x → y ∷ x) ((==Lto≡ a b (go (x == y) pf)))




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

getS : Label -> ScriptContext -> State
getS d ctx = record
                               { datum = d
                               ; value = inputVal ctx
                               ; tsig = 0 
                               ; continues = true
                               ; spends = 0
                               ; hasToken = hasTokenIn ctx
                               ; mint = 0
                               ; token = 0
                               }

getS' : ScriptContext -> State
getS' ctx = record
                               { datum = outputDatum ctx
                               ; value = outputVal ctx
                               ; tsig = signature ctx
                               ; continues = continuing ctx
                               ; spends = inputRef ctx
                               ; hasToken = hasTokenOut ctx
                               ; mint = mint ctx
                               ; token = tokAssetClass ctx
                               }

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ (l : Label) (i : Input) (ctx : ScriptContext)
                           -> i ≢ Cleanup
                           -> (pf : agdaValidator l i ctx ≡ true)
                           -> getS l ctx ~[ i ]~> getS' ctx
                              

validatorImpliesTransition (tok , map) (Open pkh) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf with lookup pkh map in eq
...| Nothing rewrite ==to≡ tok' tok (get (get (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf))))))
             | ==Lto≡ map' (insert pkh 0 map) (go (tok' == tok) (get (go (pkh == signature) 
             (go continues (go hasTokenOut (go hasTokenIn pf))))))
             = TOpen refl (==to≡ pkh signature (get (go continues (go hasTokenOut (go hasTokenIn pf)))))
               eq refl (==ito≡ outputVal inputVal (go (newDatum ctx == (tok , insert pkh 0 map)) (go (pkh == signature)
               (go continues (go hasTokenOut (go hasTokenIn pf))))))
               refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
...| Just _ = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (pkh == signature) pf)

validatorImpliesTransition (tok , map) (Close pkh) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (pkh == signature) pf) 
...| Just v rewrite ==ito≡ v 0 (get (go (pkh == signature)
            (go continues (go hasTokenOut (go hasTokenIn pf)))))
            | ==to≡ tok' tok (get (get (go (v == 0) (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
            | ==Lto≡ map' (delete pkh map) (go (tok' == tok) (get (go (v == 0) (go (pkh == signature) 
            (go continues (go hasTokenOut (go hasTokenIn pf)))))))
            = TClose refl (==to≡ pkh signature (get (go continues (go hasTokenOut (go hasTokenIn pf)))))
            (rewriteJust eq refl) refl (==ito≡ outputVal inputVal (go (newDatum ctx == (tok , delete pkh map)) (go (v == 0)
            (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
     refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (pkh == signature) pf) 
...| Just v rewrite ==to≡ tok' tok (get (go (geq v val) (go (geq val emptyValue) (get (go (pkh == signature)
             (go continues (go hasTokenOut (go hasTokenIn pf))))))))
             | rewriteSubL map pkh v val (==Lto≡ map' (insert pkh (subInteger v val) map)
             (go (tok' == tok) (go (geq v val) (go (geq val 0) (get (go (pkh == signature)
             (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
            = TWithdraw refl (==to≡ pkh signature (get (go continues (go hasTokenOut (go hasTokenIn pf)))))
            eq (geqto≤ (get (get (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
            (geqto≤ (get (go (geq val emptyValue) (get (go (pkh == signature)
            (go continues (go hasTokenOut (go hasTokenIn pf)))))))) refl
            (sym (rewriteAdd outputVal val (sym ((==ito≡ (addInteger outputVal val) inputVal (go (checkWithdraw tok (Just v) pkh val map ctx)
            ((go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf))))))))))) 
            refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (pkh == signature) pf) 
...| Just v rewrite ==to≡ tok' tok (get (go (geq val emptyValue) (get (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
             | rewriteAddL map pkh v val (==Lto≡ map' (insert pkh (addInteger v val) map)
             (go (tok' == tok) (go (geq val 0)  (get (go (pkh == signature)
             (go continues (go hasTokenOut (go hasTokenIn pf))))))))
             = TDeposit refl (==to≡ pkh signature (get (go continues (go hasTokenOut (go hasTokenIn pf)))))
             eq (geqto≤ (get (get (go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
             refl
             (rewriteAdd inputVal val (==ito≡ outputVal (addInteger inputVal val) (go (checkDeposit tok (Just v) pkh val map ctx)
             ((go (pkh == signature) (go continues (go hasTokenOut (go hasTokenIn pf))))))))
             refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf with lookup from map in eq1
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf | Nothing = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (from == signature) pf) 
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf | Just vF with lookup to map in eq2
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf | Just vF | Nothing = ⊥-elim (&&4false hasTokenIn hasTokenOut continues (from == signature) pf) 
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf | Just vF | Just vT rewrite
  ==to≡ tok' tok (get (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (from == signature)
  (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
  | doubleRewrite map from to vF vT val (==Lto≡ map' (insert from (subInteger vF val) (insert to (addInteger vT val) map))
  (go (tok' == tok) (go (from /= to) (go (geq vF val) (go (geq val 0) (get (go (from == signature)
  (go continues (go hasTokenOut (go hasTokenIn pf))))))))))
  = TTransfer refl
  ((==to≡ from signature (get (go continues (go hasTokenOut (go hasTokenIn pf)))))) eq1 eq2
  (geqto≤ (get (get (go (from == signature) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
  (geqto≤ (get (go (geq val emptyValue) (get (go (from == signature) 
  (go continues (go hasTokenOut (go hasTokenIn pf))))))))
  (/=to≢ from to (get (go (geq vF val) (go (geq val 0) (get (go (from == signature)
  (go continues (go hasTokenOut (go hasTokenIn pf))))))))) refl
  (==ito≡ outputVal inputVal (go (checkTransfer tok (Just vF) (Just vT) from to val map ctx) (go (from == signature)
  (go continues (go hasTokenOut (go hasTokenIn pf))))))
  refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) Cleanup ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } iv pf = ⊥-elim (iv refl)

mintingImpliesStart : ∀ (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> mint ctx ≡ 1
                           -> (pf : agdaPolicy adr oref top ctx ≡ true)
                           -> record {address = adr ; outputRef = oref } ⊢ getS' ctx
mintingImpliesStart adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = + 1 ; tokAssetClass = tokAssetClass } refl pf
  rewrite ==to≡ tokAssetClass tok (get (get (go (oref == inputRef) (go continues pf)))) |
  ==Lto≡ l [] (go (tokAssetClass == tok) (get (go (oref == inputRef) (go continues pf))))
  = TStart refl
    (==ito≡ outputVal 0 (get (go (tokAssetClass == tok && l == []) (go (oref == inputRef) (go continues pf)))))
    refl (get pf) (==to≡ oref inputRef (get (go continues pf))) refl
    (go (outputVal == 0) (go (tokAssetClass == tok && l == []) (go (oref == inputRef) (go continues pf))))

l=l : ∀ (l : AccMap) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite n=n (fst x) | i=i (snd x) = l=l l

bothImplyCleanup : ∀ (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
                   -> mint ctx ≡ -1
                   -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tt ctx) ≡ true
                   -> getS l ctx ~[ Cleanup ]~| getS' ctx
bothImplyCleanup d adr oref record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = .(negsuc 0) ; tokAssetClass = tokAssetClass } refl pf = TCleanup (==Lto≡ (snd d) [] (go (not continues) (go (not hasTokenOut) (go hasTokenIn (get pf))))) refl refl (unNot continues (get (go (not hasTokenOut) (go hasTokenIn (get pf))))) (get (get pf)) (unNot hasTokenOut (get (go hasTokenIn (get pf))))


≤toGeq : ∀ {a b} -> a ≤ b -> geq b a ≡ true
≤toGeq (-≤- n≤m) = ≤NtoLeqN n≤m
≤toGeq -≤+ = refl
≤toGeq (+≤+ m≤n) = ≤NtoLeqN' m≤n

transitionImpliesValidator : ∀ (l : Label) (i : Input) (ctx : ScriptContext)
                           -> getS l ctx ~[ i ]~> getS' ctx
                           -> agdaValidator l i ctx ≡ true
transitionImpliesValidator (tok , map) (Open pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TOpen refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n tok | n=n pkh | l=l (insert pkh 0 map) | i=i inputVal = refl
transitionImpliesValidator (tok , map) (Close pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TClose refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n tok | n=n pkh | l=l (delete pkh map) | i=i inputVal = refl
transitionImpliesValidator (tok , map) (Withdraw pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TWithdraw {v = v} refl refl p3 p4 p5 refl refl p8 refl refl refl) rewrite p3 | ≤toGeq p4 | ≤toGeq p5 | n=n tok | n=n pkh | add≡ outputVal val | i=i (outputVal + val) | sub≡ v val | l=l (insert pkh (v - val) map) = refl
transitionImpliesValidator (tok , map) (Deposit pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TDeposit {v = v} refl refl p3 p4 refl refl p7 refl refl refl) rewrite p3 | ≤toGeq p4 | n=n tok | n=n pkh | add≡ inputVal val | i=i (inputVal + val) | add≡ v val | l=l (insert pkh (v + val) map) = refl
transitionImpliesValidator (tok , map) (Transfer from to val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl p10 refl refl refl) rewrite p3 | p4 | ≤toGeq p5 | ≤toGeq p6 | ≢to/= from to p7 | n=n tok | n=n from | i=i inputVal | add≡ vT val | sub≡ vF val | l=l (insert from (vF + - val) (insert to (vT + val) map)) = refl


startImpliesMinting : ∀ (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> record {address = adr ; outputRef = oref } ⊢ getS' ctx
                           -> agdaPolicy adr oref top ctx ≡ true
startImpliesMinting adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TStart refl refl refl refl refl refl refl) rewrite n=n oref | n=n tok = refl


cleanupImpliesBoth : ∀ (l : Label) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
  -> getS l ctx ~[ Cleanup ]~| getS' ctx
  -> (agdaValidator l Cleanup ctx && agdaPolicy adr oref tt ctx) ≡ true
cleanupImpliesBoth d adr oref ctx (TCleanup refl refl refl refl refl refl) = refl


data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase

record Argument : Set where
  field
    adr  : Address
    oref : TxOutRef
    dat  : Label
    inp  : Input
    ctx  : ScriptContext 
open Argument


Classifier : Argument -> Phase
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } } = Initial
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Open x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Close x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer x x₁ x₂) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } = Terminal

totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) tt (arg .ctx)
... | Running = agdaValidator (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .dat) (arg .inp) (arg .ctx) &&
              agdaPolicy (arg .adr) (arg .oref) tt (arg .ctx)

totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial = record { address = arg .adr ; outputRef = arg .oref } ⊢ getS' (arg .ctx)
... | Running = getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx) 
... | Terminal =  getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .ctx) 

record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


removeCleanup : ∀ (arg : Argument) -> (mint (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .dat) (arg .inp) (arg .ctx) ≡ true)
               -> getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .ctx)
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Open x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Open x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Close x) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Close x) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Withdraw x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Withdraw x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Deposit x x₁) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Deposit x x₁) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = (Transfer x x₁ x₂) ; ctx = ctx₁ } p1 p2 = validatorImpliesTransition dat₁ (Transfer x x₁ x₂) ctx₁ (λ ()) p2
removeCleanup record { adr = adr₁ ; oref = oref₁ ; dat = dat₁ ; inp = Cleanup ; ctx = ctx₁ } p1 p2 = ⊥-elim (p1 (==ito≡ (mint ctx₁) (negsuc 0) (get (go (hasTokenIn ctx₁) p2))))



totalEquiv' : totalF ≈ totalR
totalEquiv' = record { to = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } } } x → removeCleanup arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } } } x → mintingImpliesStart adr oref tt ctx refl x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } } } x → removeCleanup arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → validatorImpliesTransition dat (Open pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → validatorImpliesTransition dat (Close pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → validatorImpliesTransition dat (Deposit pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → validatorImpliesTransition dat (Withdraw pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → validatorImpliesTransition dat (Transfer from to v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → bothImplyCleanup dat adr oref ctx refl x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } } } x → removeCleanup arg (λ ()) x }
                     ; from = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (+_ zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat inp ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ zero ] ; tokAssetClass = tokAssetClass } } } x → startImpliesMinting adr oref tt ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = +[1+ N.suc n ] ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat inp ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat (Open pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat (Close pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat (Deposit pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat (Withdraw pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat (Transfer from to v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; inp = Cleanup ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc zero) ; tokAssetClass = tokAssetClass } } } x → cleanupImpliesBoth dat adr oref ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; inp = inp ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) ; tokAssetClass = tokAssetClass } } } x → transitionImpliesValidator dat inp ctx x } } 



















