--{-# OPTIONS --inversion-max-depth=500 #-}
--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import AccountSim

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


module AccountSimProofs where



sumVal : Label -> Integer
sumVal [] = 0
sumVal ((k , v) ∷ xs) =  v + sumVal xs


record State : Set where
  field
    datum      : Datum
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
    -> value s' ≡ value s - val
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


_∈_ : ∀ (x : PubKeyHash) (xs : Label ) → Set
x ∈ xs = Any (\y -> x ≡ fst y) xs

_∉_ : ∀ (x : PubKeyHash) (xs : Label) → Set
x ∉ xs = ¬ (x ∈ xs)


data Unique : Label → Set where
  root : Unique []
  _::_ : {x : PubKeyHash} {v : Value} {l : Label} -> x ∉ l -> Unique l -> Unique ((x , v) ∷ l)





data Valid : State -> Set where

  Always : ∀ {s}
    -> value s ≡ sumVal (snd (datum s))
    -> All (\y -> geq (snd y) emptyValue ≡ true) (snd (datum s))
    ----------------
    -> Valid s


sub : ∀ {a b c : ℤ} -> a ≡ b -> a ≡ c -> b ≡ c
sub refl refl = refl

maybe⊥ : ∀ {x : Value} -> Nothing ≡ Just x -> ⊥
maybe⊥ ()

0+a : ∀ (a : Integer) -> +0 + a ≡ a
0+a (pos n) = refl
0+a (negsuc n) = refl

svLemma1 : ∀ {pkh} (l : Label) -> lookup pkh l ≡ Nothing -> sumVal l ≡ sumVal (insert pkh +0 l)
svLemma1 [] p = refl
svLemma1 {pkh} (x ∷ l) p with pkh == (fst x) in eq
...| false = cong (λ a → snd x + a) (svLemma1 l p)
...| true = ⊥-elim (maybe⊥ (sym p))

maybe≡ : ∀ {a b : Integer} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl

svLemma2 : ∀ {pkh} (l : Label) -> lookup pkh l ≡ Just +0 -> sumVal l ≡ sumVal (delete pkh l)
svLemma2 [] p = refl
svLemma2 {pkh} (x ∷ l) p with pkh == (fst x) in eq
...| false = cong (λ a → snd x + a) (svLemma2 l p)
...| true rewrite (maybe≡ p) | 0+a (sumVal l) = refl

monusLT : ∀ (a b : Nat) -> ltNat a b ≡ true -> Internal.subNat a b ≡ - (+ monusNat b a)
monusLT zero (N.suc b) pf = refl
monusLT (N.suc a) (N.suc b) pf = monusLT a b pf

monusGT : ∀ (a b : Nat) -> ltNat a b ≡ false -> Internal.subNat a b ≡ + monusNat a b
monusGT zero zero pf = refl
monusGT (N.suc a) zero pf = refl
monusGT (N.suc a) (N.suc b) pf = monusGT a b pf

subN≡ : ∀ (a b : Nat) -> Internal.subNat a b ≡ a ⊖ b
subN≡ a b with ltNat a b in eq
...| true = monusLT a b eq
...| false = monusGT a b eq

--?
ni≡ : ∀ (a : Integer) -> negateInteger a ≡ - a
ni≡ (pos zero) = refl
ni≡ +[1+ n ] = refl
ni≡ (negsuc zero) = refl
ni≡ (negsuc (N.suc n)) = refl

add≡ : ∀ (a b : Integer) -> addInteger a b ≡ a + b
add≡ (+_ n) (+_ m) = refl
add≡ (+_ n) (negsuc m) = subN≡ n (N.suc m)
add≡ (negsuc n) (+_ m) = subN≡ m (N.suc n)
add≡ (negsuc n) (negsuc m) = refl

sub≡ : ∀ (a b : Integer) -> subInteger a b ≡ a - b
sub≡ (+_ n) (+_ m) rewrite ni≡ (+ m) = add≡ (+ n) (- (+ m))
sub≡ (+_ n) (negsuc m) = refl
sub≡ (negsuc n) (+_ m) rewrite ni≡ (+ m) = add≡ (negsuc n) (- (+ m))
sub≡ (negsuc n) (negsuc m) = subN≡ (N.suc m) (N.suc n)

svLemma3 : ∀ {pkh v val} (l : Label) -> lookup pkh l ≡ Just v
           -> sumVal l + val ≡ sumVal (insert pkh (v + val) l)
svLemma3 [] p = ⊥-elim (maybe⊥ p) --refl
svLemma3 {pkh} {v} {val} (x ∷ l) p with pkh == (fst x) in eq
...| false rewrite (+-assoc (snd x) (sumVal l) val)
     = cong (λ a → snd x + a) (svLemma3 l p)
...| true rewrite (maybe≡ p) | (+-assoc v (sumVal l) val)
                  | +-comm (sumVal l) val
                  | (+-assoc v val (sumVal l)) = refl 


==to≡ : ∀ (a b : Nat) -> (a == b) ≡ true -> a ≡ b
==to≡ zero zero p = refl
==to≡ (Nat.suc a) (Nat.suc b) p = cong Nat.suc (==to≡ a b p)

==ito≡ : ∀ (a b : Integer) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong (+_) (==to≡ n m pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (==to≡ n m pf) 

switchSides : ∀ {a b c : Integer} -> a - b ≡ c -> a ≡ b + c
switchSides {a} {b} refl rewrite +-comm a (- b) | sym (+-assoc b (- b) a)
                         | +-inverseʳ b | +-identityˡ a = refl

switchSides' : ∀ {a b c : Integer} -> a + b ≡ c -> a ≡ - b + c
switchSides' {a} {b} refl rewrite +-comm a b | sym (+-assoc (- b) b a)
                         | +-inverseˡ b | +-identityˡ a = refl

doubleMinus : ∀ (a b : Integer) -> a - - b ≡ a + b
doubleMinus a b rewrite neg-involutive b = refl

svLemma4 : ∀ {from to vF vT val} (l : Label) -> lookup from l ≡ Just vF
           -> lookup to l ≡ Just vT -> from ≢ to
           -> sumVal l ≡ sumVal (insert from (vF + - val) (insert to (vT + val) l))
svLemma4 [] p1 p2 p3 = ⊥-elim (maybe⊥ p1)
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 with to == (fst x) in eq1
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true with from == to in eq2
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | true = ⊥-elim (p3 (==ito≡ from to eq2))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false with from == (fst x) in eq3
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false | true
         rewrite ==ito≡ to (fst x) eq1 | ==ito≡ from (fst x) eq3 = ⊥-elim (p3 refl)
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | true | false | false
         rewrite (maybe≡ p2) | +-assoc vT val (sumVal (insert from (vF + - val) l))
         = cong (λ a → vT + a) (switchSides {b = val} (svLemma3 l p1))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false with from == (fst x) in eq2
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false | true
         rewrite (maybe≡ p1) | +-assoc vF (- val) (sumVal (insert to (vT + val) l))
         = cong (λ a → vF + a) (switchSides' {b = (val)} (svLemma3 l p2))
svLemma4 {from} {to} {vF} {vT} {val} (x ∷ l) p1 p2 p3 | false | false
         = cong (λ a → snd x + a) (svLemma4 l p1 p2 p3)


fidelity : ∀ {s s' : State} {i : Input}
         -> value s ≡ sumVal (snd (datum s))
         -> s ~[ i ]~> s'
         -> value s' ≡ sumVal (snd (datum s'))
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Open _} pf (TOpen refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma1 map p3
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Close _} pf (TClose refl p2 p3 p4 p5 p6 p7 p8 p9) rewrite pf | p5 | p4 = svLemma2 map p3
         --rewrite pf | p4 | p3 = {!!} --svLemma2 (snd (datum s)) p2
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Withdraw _ _} pf (TWithdraw refl p2 p3 p4 p5 p6 p7 p8 p9 p10 p11) rewrite pf | p6 | p7 = svLemma3 map p3
         --rewrite p5 | p6 | pf = ? --svLemma3 (snd (datum s)) p2
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Deposit _ _} pf (TDeposit refl p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite p5 | p6 | pf = svLemma3 map p3
         --rewrite p5 | pf | p4 = svLemma3 (snd (datum s)) p2
fidelity {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {s'} {Transfer _ _ _} pf (TTransfer refl p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13) rewrite p8 | p9 | pf = svLemma4 map p3 p4 p7
--         rewrite p8 | pf | p7 = svLemma4 (snd (datum s)) p2 p3 p6

fidelityMulti : ∀ {s s' : State} {is : List Input}
  -> value s ≡ sumVal (snd (datum s))
  -> s ~[ is ]~* s'
  -> value s' ≡ sumVal (snd (datum s'))
fidelityMulti {s} {s} {[]} p1 root = p1
fidelityMulti {s} {s'} {(i ∷ is)} p1 (cons {s' = s''} x p2) = fidelityMulti (fidelity p1 x) p2

n=n : ∀ (n : Nat) -> eqNat n n ≡ true
n=n zero = refl
n=n (N.suc n) = n=n n

i=i : ∀ (i : Value) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = n=n n 
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = n=n n


≤NtoleqN : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true 
≤NtoleqN {zero} {zero} pf = refl
≤NtoleqN {zero} {N.suc b} pf = refl
≤NtoleqN {N.suc a} {N.suc b} (N.s≤s pf) = ≤NtoleqN pf

nope : ∀ (n m : Nat) -> ltNat n m ≡ true -> (ltNat m n || eqNat m n) ≡ true -> ⊥
nope (N.suc n) (N.suc m) p1 p2 = ⊥-elim (nope n m p1 p2)

monusLemma : ∀ (n m : Nat) -> (0 <= (monusNat n m)) ≡ true
monusLemma zero zero = refl
monusLemma zero (N.suc m) = refl
monusLemma (N.suc n) zero = refl
monusLemma (N.suc n) (N.suc m) = monusLemma n m

geqNatLemma : ∀ (n : Nat) -> (n >= 0) ≡ true
geqNatLemma zero = refl
geqNatLemma (N.suc n) = refl

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

lem : ∀ {pkh} (label : Label) (v' : Value)
      -> geq v' emptyValue ≡ true 
      -> All (λ y → geq (snd y) emptyValue ≡ true) label
      -> All (λ y → geq (snd y) emptyValue ≡ true) (insert pkh v' label)

lem {pkh} [] v' p1 p2 = allCons {{p1}} 
lem {pkh} ((pkh' , v) ∷ label) v' p1 (allCons {{i}} {{is}}) with pkh == pkh' in eq
...| true = allCons {{p1}} 
...| false = allCons {{i}} {{lem label v' p1 is}}

geqLem : ∀ {pkh} (label : Label) (v : Value)
      -> All (λ y → geq (snd y) emptyValue ≡ true) label
      -> lookup pkh label ≡ Just v
      -> geq v emptyValue ≡ true
geqLem {pkh} ((pkh' , v') ∷ label) v allCons p2 with pkh == pkh' in eq
geqLem {pkh} ((pkh' , v') ∷ label) .v' (allCons {{i}} {{is}}) refl | true = i
geqLem {pkh} ((pkh' , v') ∷ label) v (allCons {{i}} {{is}}) p2 | false = geqLem label v is p2


delem : ∀ {pkh} (label : Label)
      -> All (λ y → geq (snd y) emptyValue ≡ true) label
      -> All (λ y → geq (snd y) emptyValue ≡ true) (delete pkh label)
delem {pkh} [] p1 = p1
delem {pkh} ((pkh' , v') ∷ label) (allCons {{i}} {{is}}) with pkh == pkh' in eq
...| true = is 
...| false = allCons {{i}} {{delem label is}}

validStateTransition : ∀ {s s' : State} {i}
  -> Valid s
  -> s ~[ i ]~> s'
  -> Valid s'
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ 0 map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Always a1 a2) t@(TOpen refl p2 p3 refl p5 p6 p7 p8 p9) = Always (fidelity a1 t) (lem map 0 refl a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(delete _ map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Always a1 a2) t@(TClose refl p2 p3 refl p5 p6 p7 p8 p9) = Always (fidelity a1 t) (delem map a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (v - val) map) ; value = .(value - _) ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Always a1 a2) t@(TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl p8 p9 p10 p11) = Always (fidelity a1 t) (lem map (v - val) (diffLemma v val p5 p4) a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (v + val) map) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Always a1 a2) t@(TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6 p7 p8 p9 p10) = Always (fidelity a1 t) (lem map (v + val) (sumLemma v val p4 (geqLem map v a2 p3)) a2)
validStateTransition {record { datum = tok , map ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }} {record { datum = .tok , .(insert _ (vF - val) (insert _ (vT + val) map)) ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' }} (Always a1 a2) t@(TTransfer {from} {to} {val} {vF = vF} {vT = vT} refl p2 p3 p4 p5 p6 p7 refl p9 p10 p11 p12 p13) = Always (fidelity a1 t) (lem (insert to (vT + val) map) (vF - val) (diffLemma vF val p6 p5) (lem map (vT + val) (sumLemma vT val p5 (geqLem map vT a2 p4)) a2))
{-
validStateTransition {s}
  {record { label = .(insert pkh 0 (label s)) ; context = context₁ }}
  (Always a1 a2) t@(TOpen {pkh} p1 p2 refl p4)
  = Always (fidelity a1 t) (lem (label s) 0 refl a2)
validStateTransition {s} {record { label = .(delete pkh (label s)) ; context = context₁ }} (Always a1 a2) t@(TClose {pkh} p1 p2 refl p4) = Always (fidelity a1 t) (delem (label s) a2)
validStateTransition {s} {record { label = .(insert pkh (v - val) (label s)) ; context = context₁ }} (Always a1 a2) t@(TWithdraw {pkh} {val} {v = v} p1 p2 p3 p4 refl p6) = Always (fidelity a1 t) (lem (label s) (v - val) (diffLemma v val p4 p3) a2)
validStateTransition {s} {record { label = .(insert pkh (v + val) (label s)) ; context = context₁ }} (Always a1 a2) t@(TDeposit {pkh} {val = val} {v = v} p1 p2 p3 refl p5) = Always (fidelity a1 t) (lem (label s) (v + val) (sumLemma v val p3 (geqLem (label s) v a2 p2)) a2)
validStateTransition {s} {record { label = .(insert from (vF - val) (insert to (vT + val) (label s))) ; context = context₁ }} (Always a1 a2) t@(TTransfer {from} {to} {val} {vF = vF} {vT} p1 p2 p3 p4 p5 p6 refl p8) = Always (fidelity a1 t) (lem (insert to (vT + val) (label s)) (vF - val) (diffLemma vF val p4 p5) (lem (label s) (vT + val) (sumLemma vT val p5 (geqLem (label s) vT a2 p3)) a2)) -}


go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl

leqNto≤N : ∀ {a b} -> (ltNat a b || eqNat a b) ≡ true -> a N.≤ b
leqNto≤N {zero} {zero} pf = N.z≤n
leqNto≤N {zero} {suc b} pf = N.z≤n
leqNto≤N {suc a} {suc b} pf = N.s≤s (leqNto≤N pf)

leqNto≤N' : ∀ {a b} -> (ltNat a b || eqNat b a) ≡ true -> a N.≤ b
leqNto≤N' {zero} {zero} pf = N.z≤n
leqNto≤N' {zero} {suc b} pf = N.z≤n
leqNto≤N' {suc a} {suc b} pf = N.s≤s (leqNto≤N' pf)

geqto≤ : ∀ {a b} -> geq a b ≡ true -> a ≥ b
geqto≤ {pos n} {pos m} pf = +≤+ (leqNto≤N' pf)
geqto≤ {pos n} {negsuc m} pf = -≤+
geqto≤ {negsuc n} {negsuc m} pf = -≤- (leqNto≤N pf)

==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==ito≡ fst1 fst2 (get pf))
        | (==ito≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl

==lto≡ : ∀ (a b : Label) -> (a == b) ≡ true -> a ≡ b
==lto≡ [] [] pf = refl
==lto≡ (x ∷ a) (y ∷ b) pf
  rewrite (==pto≡ x y (get pf)) = cong (λ x → y ∷ x) ((==lto≡ a b (go (x == y) pf)))

get⊥ : ∀ (n : Nat) -> not (eqNat n n) ≡ true -> ⊥
get⊥ (N.suc n) p = get⊥ n p

/=to≢ : ∀ (a b : PubKeyHash) -> (a /= b) ≡ true -> a ≢ b
/=to≢ (pos n) (pos m) pf = λ {refl → get⊥ n pf}
/=to≢ (pos n) (negsuc m) pf = λ ()
/=to≢ (negsuc n) (pos m) pf = λ ()
/=to≢ (negsuc n) (negsuc m) pf = λ {refl → get⊥ n pf}


&&false : ∀ (a : Bool) -> (a && false) ≡ true -> ⊥
&&false true ()

&&5false : ∀ (a b c d e : Bool) -> (a && b && c && d && e && false) ≡ true -> ⊥
&&5false true true true true true ()

--why?
rewriteJust : ∀ {a : Maybe ℤ} {v v'} -> a ≡ Just v -> v ≡ v' -> a ≡ Just v'
rewriteJust refl refl = refl

rewriteSubL : ∀ {l1 : Label} (l2 : Label) (pkh : PubKeyHash) (v1 v2 : Value) ->
             l1 ≡ insert pkh (subInteger v1 v2) l2 -> l1 ≡ insert pkh (v1 - v2) l2
rewriteSubL l2 pkh v1 v2 p rewrite sub≡ v1 v2 = p

rewriteAddL : ∀ {l1 : Label} (l2 : Label) (pkh : PubKeyHash) (v1 v2 : Value) ->
             l1 ≡ insert pkh (addInteger v1 v2) l2 -> l1 ≡ insert pkh (v1 + v2) l2
rewriteAddL l2 pkh v1 v2 p rewrite add≡ v1 v2 = p

doubleRewrite : ∀ {l1 : Label} (l2 : Label) (from to : PubKeyHash) (vF vT val : Value) ->
             l1 ≡ insert from (subInteger vF val) (insert to (addInteger vT val) l2) ->
             l1 ≡ insert from (vF - val) (insert to (vT + val) l2)
doubleRewrite l2 from to vF vT val p rewrite add≡ vT val | sub≡ vF val = p

rewriteSub : ∀ {a} (b c : Value) -> a ≡ subInteger b c -> a ≡ b - c
rewriteSub b c p rewrite sub≡ b c = p

rewriteAdd : ∀ {a} (b c : Value) -> a ≡ addInteger b c -> a ≡ b + c
rewriteAdd b c p rewrite add≡ b c = p

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {sig spn mnt tok} (d : Datum) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator d i ctx ≡ true)
                           -> record
                               { datum = d
                               ; value = inputVal ctx
                               ; tsig = sig
                               ; continues = true
                               ; spends = spn
                               ; hasToken = hasTokenIn ctx
                               ; mint = mnt
                               ; token = tok
                               }
                              ~[ i ]~>
                              record
                               { datum = outputDatum ctx
                               ; value = outputVal ctx
                               ; tsig = signature ctx
                               ; continues = continuing ctx
                               ; spends = inputRef ctx
                               ; hasToken = hasTokenOut ctx
                               ; mint = mint ctx
                               ; token = tokAssetClass ctx
                               }

validatorImpliesTransition (tok , map) (Open pkh) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf with lookup pkh map in eq
...| Nothing rewrite ==to≡ tok' tok (get (go continues (go hasTokenOut (go hasTokenIn pf))))
             | ==lto≡ map' (insert pkh 0 map) (get (go (pkh == signature) (go (tok' == tok)
             (go continues (go hasTokenOut (go hasTokenIn pf))))))
             = TOpen refl (==ito≡ pkh signature (get (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))
               eq refl (==ito≡ outputVal inputVal (go (map' == (insert pkh 0 map)) (go (pkh == signature)
               (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf)))))))
               refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
...| Just _ = ⊥-elim (&&5false hasTokenIn hasTokenOut continues (tok' == tok) (pkh == signature) pf)

validatorImpliesTransition (tok , map) (Close pkh) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&5false hasTokenIn hasTokenOut continues (tok' == tok) (pkh == signature) pf)
...| Just v rewrite ==ito≡ v 0 (get (go (pkh == signature) (go (tok' == tok)
            (go continues (go hasTokenOut (go hasTokenIn pf))))))
            | ==to≡ tok' tok (get (go continues (go hasTokenOut (go hasTokenIn pf))))
            | ==lto≡ map' (delete pkh map) (get (go (v == 0) (go (pkh == signature) (go (tok' == tok)
            (go continues (go hasTokenOut (go hasTokenIn pf)))))))
            = TClose refl (==ito≡ pkh signature (get (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))
            (rewriteJust eq refl) refl (==ito≡ outputVal inputVal (go (map' == (delete pkh map)) (go (v == 0)
            (go (pkh == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))))
     refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&5false hasTokenIn hasTokenOut continues (tok' == tok) (pkh == signature) pf)
...| Just v rewrite ==to≡ tok' tok (get (go continues (go hasTokenOut (go hasTokenIn pf))))
             | rewriteSubL map pkh v val (==lto≡ map' (insert pkh (subInteger v val) map)
             (go (geq v val) (go (geq val 0) (get (go (pkh == signature) (go (tok' == tok)
             (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
            = TWithdraw refl (==ito≡ pkh signature (get (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))
            eq (geqto≤ (get (get (go (pkh == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))))
            (geqto≤ (get (go (geq val emptyValue) (get (go (pkh == signature) (go (tok' == tok)
            (go continues (go hasTokenOut (go hasTokenIn pf))))))))) refl
            (rewriteSub inputVal val (==ito≡ outputVal (subInteger inputVal val) (go (checkWithdraw (Just v) pkh val map ctx)
            ((go (pkh == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
            refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf with lookup pkh map in eq
...| Nothing = ⊥-elim (&&5false hasTokenIn hasTokenOut continues (tok' == tok) (pkh == signature) pf)
...| Just v rewrite ==to≡ tok' tok (get (go continues (go hasTokenOut (go hasTokenIn pf))))
             | rewriteAddL map pkh v val (==lto≡ map' (insert pkh (addInteger v val) map)
             (go (geq val 0)  (get (go (pkh == signature) (go (tok' == tok)
             (go continues (go hasTokenOut (go hasTokenIn pf))))))))
             = TDeposit refl (==ito≡ pkh signature (get (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))
             eq (geqto≤ (get (get (go (pkh == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))))
             refl
             (rewriteAdd inputVal val (==ito≡ outputVal (addInteger inputVal val) (go (checkDeposit (Just v) pkh val map ctx)
             ((go (pkh == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
             refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf with lookup from map in eq1
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf | Nothing = ⊥-elim ((&&5false hasTokenIn hasTokenOut continues (tok' == tok) (from == signature) pf))
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf | Just vF with lookup to map in eq2
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf | Just vF | Nothing = ⊥-elim (&&5false hasTokenIn hasTokenOut continues (tok' == tok) (from == signature) pf)
validatorImpliesTransition (tok , map) (Transfer from to val) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } pf | Just vF | Just vT rewrite
  ==to≡ tok' tok (get (go continues (go hasTokenOut (go hasTokenIn pf))))
  | doubleRewrite map from to vF vT val (==lto≡ map' (insert from (subInteger vF val) (insert to (addInteger vT val) map))
  (go (from /= to) (go (geq vF val) (go (geq val 0) (get (go (from == signature) (go (tok' == tok)
  (go continues (go hasTokenOut (go hasTokenIn pf))))))))))
  = TTransfer refl
  ((==ito≡ from signature (get (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))) eq1 eq2
  (geqto≤ (get (get (go (from == signature) (go (tok' == tok) (go continues (go hasTokenOut (go hasTokenIn pf))))))))
  (geqto≤ (get (go (geq val emptyValue) (get (go (from == signature) (go (tok' == tok)
  (go continues (go hasTokenOut (go hasTokenIn pf)))))))))
  (/=to≢ from to (get (go (geq vF val) (go (geq val 0) (get (go (from == signature) (go (tok' == tok)
  (go continues (go hasTokenOut (go hasTokenIn pf)))))))))) refl
  (==ito≡ outputVal inputVal (go (checkTransfer (Just vF) (Just vT) from to val map ctx) (go (from == signature) (go (tok' == tok)
  (go continues (go hasTokenOut (go hasTokenIn pf)))))))
  refl (get (go hasTokenOut (go hasTokenIn pf))) (get pf) (get (go hasTokenIn pf))



mintingImpliesStart : ∀ {s} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> mint ctx ≡ 1
                           -> (pf : agdaPolicy adr oref top ctx ≡ true)
                           -> record {address = adr ; outputRef = oref } ⊢
                           record { datum = outputDatum ctx ; value = outputVal ctx ;
                           tsig = s ; continues = continues ctx ;
                           spends = inputRef ctx ; hasToken = hasTokenOut ctx ; mint = mint ctx ; token = tokAssetClass ctx}
mintingImpliesStart adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = + 1 ; tokAssetClass = tokAssetClass } refl pf
  rewrite ==to≡ tokAssetClass tok (get (get (go (oref == inputRef) (go continues pf)))) |
  ==lto≡ l [] (go (tokAssetClass == tok) (get (go (oref == inputRef) (go continues pf))))
  = TStart refl refl (get pf) (==to≡ oref inputRef (get (go continues pf))) refl
  (go (tokAssetClass == tok && l == []) (go (oref == inputRef) (go continues pf)))

l=l : ∀ (l : Label) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite i=i (fst x) | i=i (snd x) = l=l l



≤NtoLeqN : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤NtoLeqN {b = zero} N.z≤n = refl
≤NtoLeqN {b = N.suc b} N.z≤n = refl
≤NtoLeqN (N.s≤s p) = ≤NtoLeqN p

≤NtoLeqN' : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat b a) ≡ true
≤NtoLeqN' {b = zero} N.z≤n = refl
≤NtoLeqN' {b = N.suc b} N.z≤n = refl
≤NtoLeqN' (N.s≤s p) = ≤NtoLeqN' p

≤toGeq : ∀ {a b} -> a ≤ b -> geq b a ≡ true
≤toGeq (-≤- n≤m) = ≤NtoLeqN n≤m
≤toGeq -≤+ = refl
≤toGeq (+≤+ m≤n) = ≤NtoLeqN' m≤n

≢to/= : ∀ (a b : PubKeyHash) -> a ≢ b -> (a /= b) ≡ true
≢to/= (pos n) (pos m) p with eqNat n m in eq
...| False = refl
...| True rewrite ==to≡ n m eq = ⊥-elim (p refl)
≢to/= (pos n) (negsuc m) p = refl
≢to/= (negsuc n) (pos m) p = refl
≢to/= (negsuc n) (negsuc m) p with eqNat n m in eq
...| False = refl 
...| True rewrite ==to≡ n m eq = ⊥-elim (p refl)



transitionImpliesValidator : ∀ {sig spn mnt tok}  (d : Datum) (i : Input) (ctx : ScriptContext)
                           -> record
                               { datum = d
                               ; value = inputVal ctx
                               ; tsig = sig
                               ; continues = true
                               ; spends = spn
                               ; hasToken = hasTokenIn ctx
                               ; mint = mnt
                               ; token = tok
                               }
                              ~[ i ]~>
                              record
                               { datum = outputDatum ctx
                               ; value = outputVal ctx
                               ; tsig = signature ctx
                               ; continues = continuing ctx
                               ; spends = inputRef ctx
                               ; hasToken = hasTokenOut ctx
                               ; mint = mint ctx
                               ; token = tokAssetClass ctx
                               }
                           -> agdaValidator d i ctx ≡ true
transitionImpliesValidator (tok , map) (Open pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TOpen refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n tok | i=i pkh | l=l (insert pkh 0 map) | i=i inputVal = refl
transitionImpliesValidator (tok , map) (Close pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TClose refl refl p3 refl refl p6 refl refl refl) rewrite p3 | n=n tok | i=i pkh | l=l (delete pkh map) | i=i inputVal = refl
transitionImpliesValidator (tok , map) (Withdraw pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TWithdraw {v = v} refl refl p3 p4 p5 refl refl p8 refl refl refl) rewrite p3 | ≤toGeq p4 | ≤toGeq p5 | n=n tok | i=i pkh | sub≡ inputVal val | i=i (inputVal - val) | sub≡ v val | l=l (insert pkh (v - val) map) = refl
transitionImpliesValidator (tok , map) (Deposit pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TDeposit {v = v} refl refl p3 p4 refl refl p7 refl refl refl) rewrite p3 | ≤toGeq p4 | n=n tok | i=i pkh | add≡ inputVal val | i=i (inputVal + val) | add≡ v val | l=l (insert pkh (v + val) map) = refl
transitionImpliesValidator (tok , map) (Transfer from to val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl p10 refl refl refl) rewrite p3 | p4 | ≤toGeq p5 | ≤toGeq p6 | ≢to/= from to p7 | n=n tok | i=i from | i=i inputVal | add≡ vT val | sub≡ vF val | l=l (insert from (vF + - val) (insert to (vT + val) map)) = refl


startImpliesMinting : ∀ {s} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> record {address = adr ; outputRef = oref } ⊢
                           record { datum = outputDatum ctx ; value = outputVal ctx ;
                           tsig = s ; continues = continues ctx ;
                           spends = inputRef ctx ; hasToken = hasTokenOut ctx ; mint = mint ctx ; token = tokAssetClass ctx}
                           -> agdaPolicy adr oref top ctx ≡ true
startImpliesMinting adr oref top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; hasTokenIn = hasTokenIn ; hasTokenOut = hasTokenOut ; mint = mint ; tokAssetClass = tokAssetClass } (TStart refl refl refl refl refl refl) rewrite n=n oref | n=n tok = refl

lemmaMultiStep : ∀ {s s' s'' : State} {is is' : List Input}
                   -> s  ~[ is  ]~* s'
                   -> s' ~[ is' ]~* s''
                   -> s  ~[ is ++ is' ]~* s''
lemmaMultiStep {s} {.s} {s''} {[]} {is'} root p2 = p2
lemmaMultiStep {s} {s'} {s''} {i ∷ is} {is'} (cons {s' = s'''} x p1) p2 = cons x (lemmaMultiStep p1 p2)



makeIs : Label -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = (Withdraw a b) ∷ (Close a) ∷ (makeIs l)

makeL : Label -> Label
makeL [] = []
makeL ((a , b) ∷ l) = (a , emptyValue) ∷ (makeL l)


lastSig : State -> PubKeyHash
lastSig record { datum = (tok , []) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = tsig
lastSig record { datum = (tok , x ∷ []) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = fst x
lastSig record { datum = (tok , x ∷ y ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } = lastSig record { datum = (tok , y ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token }
{-
lastSig record { label = [] ; context = record { value = value ; tsig = tsig } } = tsig
lastSig record { label = (x ∷ []) ; context = record { value = value ; tsig = tsig } } = fst x
lastSig record { label = (x ∷ y ∷ label) ; context = ctx }
  = lastSig (record { label = y ∷ label ; context = ctx })-}


lookupProp1 : ∀ {b : Bool} {a : Set} { x y z : Maybe a }
            -> b ≡ true
            -> x ≡ z
            -> (if b then x else y) ≡ z
lookupProp1 refl refl = refl


deleteProp1 : ∀ {a : AssetClass} {b : Bool} { x y z : Label }
            -> b ≡ true
            -> x ≡ z
            -> (a , z) ≡ (a , (if b then x else y))
deleteProp1 refl refl = refl



n≤n : ∀ (n : Nat) -> n N.≤ n
n≤n zero = N.z≤n
n≤n (N.suc n) = N.s≤s (n≤n n)

v≤v : ∀ (v : Value) -> v ≤ v
v≤v (pos n) = +≤+ (n≤n n)
v≤v (negsuc n) = -≤- (n≤n n)

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
getGeq refl (Always x (allCons {{i}} {{is}})) = geqto≤ i

ltLem : ∀ (n : Nat) -> ltNat n n ≡ false
ltLem zero = refl
ltLem (N.suc n) = ltLem n

monusLem : ∀ (n : Nat) -> monusNat n n ≡ 0
monusLem zero = refl
monusLem (N.suc n) = monusLem n

i-i : ∀ (i : Value) -> i - i ≡ emptyValue
i-i (pos zero) = refl
i-i +[1+ n ] = i-i (negsuc n)
i-i (negsuc n) rewrite (ltLem n) | (monusLem n) = refl

rewriteLabel : ∀ (pkh : PubKeyHash) (val : Value) (label : Label)
               -> (pkh , val - val) ∷ label ≡ (pkh , emptyValue) ∷ label
rewriteLabel pkh val label rewrite (i-i val) = refl



minusLemma : ∀ (a b c : Value) -> a ≡ b + c -> a - c ≡ b
minusLemma .(b + + n) b (pos n) refl rewrite +-assoc b (+ n) (- (+ n))
           | [+m]-[+n]≡m⊖n n n | n⊖n≡0 n | +-identityʳ b = refl
minusLemma .(b + negsuc n) b (negsuc n) refl rewrite +-assoc b (negsuc n) (- (negsuc n))
           | n⊖n≡0 (N.suc n) | +-identityʳ b = refl


{-
sameLastSig' : ∀ {x context context'} (label : Label)
  -> lastSig (record { label = x ∷ label ; context = context }) ≡
     lastSig (record { label = x ∷ label ; context = context' })
sameLastSig' [] = refl --refl
sameLastSig' (y ∷ label) = sameLastSig' label
-}

sameLastSig' : ∀ {tok x v tsig spends mint token v' spends' mint' token' tsig'} (map : Label)
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

sameLastSig : ∀ {tok x v tsig spends mint token v' spends' mint' token'} (map : Label)
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

refactor : ∀ (a b c : Value) -> a ≡ b + c -> c ≡ a - b
refactor a b c p rewrite +-comm b c = sym (minusLemma a c b p)

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
subValid (Always x (allCons {{i}} {{is}})) = is


prop1 : ∀ {tok} {map : Label} (s s' : State)
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
prop1 record { datum = (tok , x ∷ map) ; value = value ; tsig = tsig ; continues = continues ; spends = spends ; hasToken = hasToken ; mint = mint ; token = token } s'@record { datum = (tok' , map') ; value = value' ; tsig = tsig' ; continues = continues' ; spends = spends' ; hasToken = hasToken' ; mint = mint' ; token = token' } refl refl refl refl refl refl refl refl refl refl refl refl p rewrite i=i (x .fst)
  = cons {s' = st} (TWithdraw refl refl (lookupProp1 (i=i (fst x)) refl) (getGeq refl p) (v≤v (snd x)) (deleteProp1 (i=i (fst x))  (rewriteLabel (fst x) (snd x) map) ) (refactor value (snd x) (sumVal map) refl) refl refl refl refl)
  (cons {s' = st'} (TClose refl refl (lookupProp1 (i=i (fst x)) refl) (deleteProp1 (i=i (fst x)) refl) refl refl refl refl refl)
  (prop1 {tok} {map} st' s' refl refl refl (sameLastSig map) refl refl refl refl refl refl refl refl (Always refl (subValid p))))
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

















