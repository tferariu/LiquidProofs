--{-# OPTIONS --inversion-max-depth=500 #-}
--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import AccountSim

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
--open import Data.Nat.Properties
open import Data.Integer --hiding (_+_; _-_)
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
--open import Data.List.Relation.Unary.Any hiding (lookup)
--open import Data.List.Relation.Unary.All as All hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
--open import Data.Product

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

{- -}
open import Haskell.Prim hiding (⊥) -- ; All)
open import Haskell.Prim.Integer
--open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup)

--open import Haskell.Prelude
--open import Haskell.Prim renaming (magic to ⊥-elim)
--using (lookup)

open import Function.Base using (_∋_)


module AccountSimProofs where

--open import ListInsertLib (PubKeyHash) (==ito≡) (=/=ito≢)

sumVal : Label -> Integer
sumVal [] = 0
sumVal ((k , v) ∷ xs) =  v + sumVal xs


record Context : Set where
  field
    value         : Value  {-
    outVal        : Value
    outAdr        : PubKeyHash -}
    tsig          : PubKeyHash
open Context

record State : Set where
  field
    label         : Label
    context       : Context
open State

--Transition Rules
data _~[_]~>_ : State -> Input -> State -> Set where
 
  TOpen : ∀ {pkh s s'}
    -> pkh ≡ tsig (context s')
    -> lookup pkh (label s) ≡ Nothing
    -> label s' ≡ insert pkh 0 (label s)
    -> value (context s') ≡ value (context s) 
    -------------------
    -> s ~[ (Open pkh) ]~> s'

  TClose : ∀ {pkh s s'}
    -> pkh ≡ tsig (context s')
    -> lookup pkh (label s) ≡ Just 0
    -> label s' ≡ delete pkh (label s)
    -> value (context s') ≡ value (context s) 
    -------------------
    -> s ~[ (Close pkh) ]~> s'

  TWithdraw : ∀ {pkh val s s' v}
    -> pkh ≡ tsig (context s')
    -> lookup pkh (label s) ≡ Just v
    -> val ≥ emptyValue
    -> v ≥ val
    -> label s' ≡ (insert pkh (v - val) (label s))
    -> value (context s') ≡ value (context s) - val
  --  -> pkh ≡ outAdr (context s') 
  --  -> val ≡ outVal (context s') 
    -------------------
    -> s ~[ (Withdraw pkh val) ]~> s'
    
  TDeposit : ∀ {pkh val s s' v}
    -> pkh ≡ tsig (context s')
    -> lookup pkh (label s) ≡ Just v
    -> val ≥ emptyValue
    -> label s' ≡ (insert pkh (v + val) (label s))
    -> value (context s') ≡ value (context s) + val
    -------------------
    -> s ~[ (Deposit pkh val) ]~> s'

    
  TTransfer : ∀ {from to val s s' vF vT}
    -> from ≡ tsig (context s')
    -> lookup from (label s) ≡ Just vF
    -> lookup to (label s) ≡ Just vT
    -> vF ≥ val
    -> val ≥ emptyValue
    -> from ≢ to
    -> label s' ≡ (insert from (vF - val) (insert to (vT + val) (label s)))
    -> value (context s') ≡ value (context s)
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

{--}

data Valid : State -> Set where

  Always : ∀ {s}
    -> value (context s) ≡ sumVal (label s)
    -> All (\y -> geq (snd y) emptyValue ≡ true) (label s)
    -- -> (∀ {pkh v} -> lookup pkh (label s) ≡ Just v -> (geq v emptyValue ≡ true)) --use ALl
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


--subN≡ : ∀ (a b : Integer) -> subNat a b ≡ a ⊖ b
--subN≡ a b = ?

ni≡ : ∀ (a : Integer) -> negateInteger a ≡ - a
ni≡ (pos zero) = refl
ni≡ +[1+ n ] = refl
ni≡ (negsuc zero) = refl
ni≡ (negsuc (N.suc n)) = refl

add≡ : ∀ (a b : Integer) -> addInteger a b ≡ a + b
add≡ (pos zero) (pos zero) = refl
add≡ (pos zero) +[1+ m ] = refl
add≡ +[1+ n ] (pos zero) = refl
add≡ +[1+ n ] +[1+ m ] = refl
add≡ (pos zero) (negsuc zero) = refl
add≡ (pos zero) (negsuc (N.suc m)) = refl
add≡ +[1+ n ] (negsuc zero) = refl
add≡ +[1+ n ] (negsuc (N.suc m)) with ltNat n (N.suc m)
...| True = ni≡ (pos (monusNat (N.suc m) n))
...| False = refl 
add≡ (negsuc zero) (pos zero) = refl
add≡ (negsuc zero) +[1+ m ] = refl
add≡ (negsuc (N.suc n)) (pos zero) = refl
add≡ (negsuc (N.suc n)) +[1+ m ] with ltNat m (N.suc n)
...| True = ni≡ (pos (monusNat (N.suc n) m))
...| False = refl
add≡ (negsuc zero) (negsuc zero) = refl
add≡ (negsuc zero) (negsuc (N.suc m)) = refl
add≡ (negsuc (N.suc n)) (negsuc zero) = refl
add≡ (negsuc (N.suc n)) (negsuc (N.suc m)) = refl

sub≡ : ∀ (a b : Integer) -> subInteger a b ≡ a - b
sub≡ (pos zero) (pos zero) = refl
sub≡ (pos zero) +[1+ m ] = refl
sub≡ +[1+ n ] (pos zero) = refl
sub≡ +[1+ n ] +[1+ m ] = sub≡ (negsuc m) (negsuc n)
sub≡ (pos zero) (negsuc zero) = refl
sub≡ (pos zero) (negsuc (N.suc m)) = refl
sub≡ +[1+ n ] (negsuc zero) = refl
sub≡ +[1+ n ] (negsuc (N.suc m)) = refl
sub≡ (negsuc zero) (pos zero) = refl
sub≡ (negsuc zero) +[1+ m ] = refl
sub≡ (negsuc (N.suc n)) (pos zero) = refl
sub≡ (negsuc (N.suc n)) +[1+ m ] = refl
sub≡ (negsuc zero) (negsuc zero) = refl
sub≡ (negsuc zero) (negsuc (N.suc m)) = refl
sub≡ (negsuc (N.suc n)) (negsuc zero) = refl
sub≡ (negsuc (N.suc n)) (negsuc (N.suc m)) with ltNat m n
...| True = ni≡ (pos (monusNat n m))
...| False = refl

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
==ito≡ (pos n) (pos m) pf = cong pos (==to≡ n m pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (sym (==to≡ m n pf)) 

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
         -> value (context s) ≡ sumVal (label s)
         -> s ~[ i ]~> s'
         -> value (context s') ≡ sumVal (label s')
fidelity {s} {s'} {Open _} pf (TOpen p1 p2 p3 p4)
         rewrite pf | p4 | p3 = svLemma1 (label s) p2
fidelity {s} {s'} {Close _} pf (TClose p1 p2 p3 p4)
         rewrite pf | p4 | p3 = svLemma2 (label s) p2
fidelity {s} {s'} {Withdraw _ _} pf (TWithdraw p1 p2 p3 p4 p5 p6)
         rewrite p5 | p6 | pf = svLemma3 (label s) p2
fidelity {s} {s'} {Deposit _ _} pf (TDeposit p1 p2 p3 p4 p5)
         rewrite p5 | pf | p4 = svLemma3 (label s) p2
fidelity {s} {s'} {Transfer _ _ _} pf (TTransfer p1 p2 p3 p4 p5 p6 p7 p8)
         rewrite p8 | pf | p7 = svLemma4 (label s) p2 p3 p6

fidelityMulti : ∀ {s s' : State} {is : List Input}
  -> value (context s) ≡ sumVal (label s)
  -> s ~[ is ]~* s'
  -> value (context s') ≡ sumVal (label s')
fidelityMulti {s} {s} {[]} p1 root = p1
fidelityMulti {s} {s'} {(i ∷ is)} p1 (cons {s' = s''} x p2) = fidelityMulti (fidelity p1 x) p2


i=i : ∀ (i : Value) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = i=i (pos n)
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = i=i (pos n)


≤NtoleqN : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true 
≤NtoleqN {zero} {zero} pf = refl
≤NtoleqN {zero} {N.suc b} pf = refl
≤NtoleqN {N.suc a} {N.suc b} (N.s≤s pf) = ≤NtoleqN pf

aaa : ∀ (n m : Nat) -> ltNat n m ≡ true -> (ltNat m n || eqNat m n) ≡ true -> ⊥
aaa (N.suc n) (N.suc m) p1 p2 = ⊥-elim (aaa n m p1 p2)

monusLemma : ∀ (n m : Nat) -> (0 <= (monusNat n m)) ≡ true
monusLemma zero zero = refl
monusLemma zero (N.suc m) = refl
monusLemma (N.suc n) zero = refl
monusLemma (N.suc n) (N.suc m) = monusLemma n m

diffSubLemma : ∀ (n m : Nat) -> 0 N.≤ m -> m N.≤ n ->
             (ltInteger +0 (pos n + - pos m) || eqInteger +0 (pos n + - pos m)) ≡ true
diffSubLemma zero .zero N.z≤n N.z≤n = refl
diffSubLemma (N.suc n) .zero N.z≤n N.z≤n = refl
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) with ltNat n m in eq
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | true = ⊥-elim (aaa n m eq (≤NtoleqN p2))
diffSubLemma .(N.suc n) .(N.suc m) N.z≤n (N.s≤s {m} {n} p2) | false = monusLemma n m

diffLemma : ∀ (v v' : Value) -> v' ≤ v -> emptyValue ≤ v' -> geq (v - v') emptyValue ≡ true
diffLemma .(negsuc _) .(negsuc _) (-≤- n≤m) ()
diffLemma .(pos _) .(negsuc _) -≤+ ()
diffLemma .(pos n) .(pos m) (+≤+ {m} {n} m≤n) (+≤+ m≤n₁) = diffSubLemma n m m≤n₁ m≤n

addNatLemma : ∀ (n m : Nat) -> (0 <= (addNat n m)) ≡ true
addNatLemma zero zero = refl
addNatLemma zero (N.suc m) = refl
addNatLemma (N.suc n) zero = refl
addNatLemma (N.suc n) (N.suc m) = refl 

sumLemma : ∀ (v v' : Value) -> emptyValue ≤ v' -> geq v emptyValue ≡ true -> geq (v + v') emptyValue ≡ true
sumLemma (pos n) (pos m) p1 p2 = addNatLemma n m

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
validStateTransition {s}
  {record { label = .(insert pkh 0 (label s)) ; context = context₁ }}
  (Always a1 a2) t@(TOpen {pkh} p1 p2 refl p4)
  = Always (fidelity a1 t) (lem (label s) 0 refl a2)
validStateTransition {s} {record { label = .(delete pkh (label s)) ; context = context₁ }} (Always a1 a2) t@(TClose {pkh} p1 p2 refl p4) = Always (fidelity a1 t) (delem (label s) a2)
validStateTransition {s} {record { label = .(insert pkh (v - val) (label s)) ; context = context₁ }} (Always a1 a2) t@(TWithdraw {pkh} {val} {v = v} p1 p2 p3 p4 refl p6) = Always (fidelity a1 t) (lem (label s) (v - val) (diffLemma v val p4 p3) a2)
validStateTransition {s} {record { label = .(insert pkh (v + val) (label s)) ; context = context₁ }} (Always a1 a2) t@(TDeposit {pkh} {val = val} {v = v} p1 p2 p3 refl p5) = Always (fidelity a1 t) (lem (label s) (v + val) (sumLemma v val p3 (geqLem (label s) v a2 p2)) a2)
validStateTransition {s} {record { label = .(insert from (vF - val) (insert to (vT + val) (label s))) ; context = context₁ }} (Always a1 a2) t@(TTransfer {from} {to} {val} {vF = vF} {vT} p1 p2 p3 p4 p5 p6 refl p8) = Always (fidelity a1 t) (lem (insert to (vT + val) (label s)) (vF - val) (diffLemma vF val p4 p5) (lem (label s) (vT + val) (sumLemma vT val p5 (geqLem (label s) vT a2 p3)) a2)) 


get : ∀ (a : Bool) {b} -> (a && b) ≡ true -> a ≡ true
get true pf = refl

go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

skip : ∀ {a b : Bool} -> (a && b) ≡ true -> b ≡ true
skip {true} {true} pf = pf

here : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
here {true} {true} pf = refl

leqNto≤N : ∀ {a b} -> (ltNat a b || eqNat a b) ≡ true -> a N.≤ b
leqNto≤N {zero} {zero} pf = N.z≤n
leqNto≤N {zero} {suc b} pf = N.z≤n
leqNto≤N {suc a} {suc b} pf = N.s≤s (leqNto≤N pf)

geqto≤ : ∀ {a b} -> geq a b ≡ true -> a ≥ b
geqto≤ {pos n} {pos m} pf = +≤+ (leqNto≤N pf)
geqto≤ {pos n} {negsuc m} pf = -≤+
geqto≤ {negsuc n} {negsuc m} pf = -≤- (leqNto≤N pf)


==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==ito≡ fst1 fst2 (get (fst1 == fst2) pf))
        | (==ito≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl

==lto≡ : ∀ (a b : Label) -> (a == b) ≡ true -> a ≡ b
==lto≡ [] [] pf = refl
==lto≡ (x ∷ a) (y ∷ b) pf
  rewrite (==pto≡ x y (get (x == y) pf)) = cong (λ x → y ∷ x) ((==lto≡ a b (go (x == y) pf)))

get⊥ : ∀ (n : Nat) -> not (eqNat n n) ≡ true -> ⊥
get⊥ (N.suc n) p = get⊥ n p

/=to≢ : ∀ (a b : PubKeyHash) -> (a /= b) ≡ true -> a ≢ b
/=to≢ (pos n) (pos m) pf = λ {refl → get⊥ n pf}
/=to≢ (pos n) (negsuc m) pf = λ ()
/=to≢ (negsuc n) (pos m) pf = λ ()
/=to≢ (negsuc n) (negsuc m) pf = λ {refl → get⊥ n pf}


&&false : ∀ (a : Bool) -> (a && false) ≡ true -> ⊥
&&false true ()


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
validatorImpliesTransition : ∀ {sig} (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator l i ctx ≡ true)
                           -> record { label = l ; context = record { value = (inputVal ctx) ; tsig = sig } }
                              ~[ i ]~>
                              record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx)
                              ; tsig = signature ctx } }

validatorImpliesTransition l (Open pkh) ctx pf with lookup pkh l in eq
...| Nothing = TOpen (==ito≡ pkh (signature ctx) (get (pkh == (signature ctx)) pf)) eq
               (==lto≡ (outputLabel ctx) (insert pkh 0 l) (get ((outputLabel ctx) == (insert pkh 0 l))
               (go (pkh == (signature ctx)) pf))) (==ito≡ (outputVal ctx) (inputVal ctx)
               (go ((outputLabel ctx) == (insert pkh +0 l)) (go (pkh == (signature ctx)) pf)))
...| Just _ = ⊥-elim (&&false (pkh == signature ctx) pf)

validatorImpliesTransition l (Close pkh) ctx pf with lookup pkh l in eq
...| Nothing = ⊥-elim (&&false (pkh == signature ctx) pf)
...| Just v = TClose (==ito≡ pkh (signature ctx) (get (pkh == (signature ctx)) pf))
              (rewriteJust eq (==ito≡ v +0 (get (v == +0) (go (pkh == signature ctx) pf))))
              ((==lto≡ (outputLabel ctx) (delete pkh l) (here --get ((outputLabel ctx) == (delete pkh l))
               (go (v == +0) (go (pkh == (signature ctx)) pf))))) (==ito≡ (outputVal ctx) (inputVal ctx)
               (go ((outputLabel ctx) == (delete pkh l)) (go (v == +0) (go (pkh == (signature ctx)) pf))))
               
validatorImpliesTransition l (Withdraw pkh val) ctx pf with lookup pkh l in eq
...| Nothing = ⊥-elim (&&false (pkh == signature ctx) pf)
...| Just v = TWithdraw (==ito≡ pkh (signature ctx) (get (pkh == (signature ctx)) pf)) eq
              (geqto≤ (get (geq val +0) (get (checkWithdraw (Just v) pkh val l ctx) (go (pkh == (signature ctx)) pf)) )) 
              (geqto≤ (get (geq v val) (go (geq val +0) (get (checkWithdraw (Just v) pkh val l ctx) (go (pkh == (signature ctx)) pf)) ))) -- ()
              (rewriteSubL l pkh v val (==lto≡ (newLabel ctx) (insert pkh (subInteger v val) l)
              (go (geq v val) (go (geq val +0) (get (checkWithdraw (Just v) pkh val l ctx) (go (pkh == signature ctx) pf)))))) 
              (rewriteSub (inputVal ctx) val (==ito≡ (outputVal ctx) (subInteger (inputVal ctx) val)
              ( (go (checkWithdraw (Just v) pkh val l ctx) (go (pkh == signature ctx) pf)))))
              
              

validatorImpliesTransition l (Deposit pkh val) ctx pf with lookup pkh l in eq
...| Nothing = ⊥-elim (&&false (pkh == signature ctx) pf)
...| Just v = TDeposit (==ito≡ pkh (signature ctx) (here pf)) eq
              (geqto≤ (here (here (go (pkh == signature ctx) pf))))
              (rewriteAddL l pkh v val (==lto≡ (outputLabel ctx) (insert pkh (addInteger v val) l)
              (go (geq val +0) (here (go (pkh == signature ctx) pf)))))
              (rewriteAdd (inputVal ctx) val (==ito≡ (outputVal ctx) (addInteger (inputVal ctx) val)
              (go (checkDeposit (Just v) pkh val l ctx) (go (pkh == signature ctx) pf))))
              
validatorImpliesTransition l (Transfer from to val) ctx pf with lookup from l in eq1
validatorImpliesTransition l (Transfer from to val) ctx pf | Nothing = ⊥-elim (&&false (from == signature ctx) pf)
validatorImpliesTransition l (Transfer from to val) ctx pf | Just vF with lookup to l in eq2
validatorImpliesTransition l (Transfer from to val) ctx pf | Just vF | Nothing = ⊥-elim (&&false (from == signature ctx) pf)
validatorImpliesTransition l (Transfer from to val) ctx pf | Just vF | Just vT = TTransfer
  (==ito≡ from (signature ctx) (here pf)) eq1 eq2
  (geqto≤ (here (here (go (from == signature ctx) pf))))
  (geqto≤ (here (go (geq vF val) (here (go (from == signature ctx) pf)))))
  (/=to≢ from to (here (go (geq val +0) (go (geq vF val) (here (go (from == signature ctx) pf))))))
  (doubleRewrite l from to vF vT val (==lto≡ (outputLabel ctx)  (insert from (subInteger vF val) (insert to (addInteger vT val) l))
  (go (from /= to) (go (geq val +0) (go (geq vF val) (here (go (from == signature ctx) pf)))))))
  (==ito≡ (outputVal ctx) (inputVal ctx) (go (checkTransfer (Just vF) (Just vT) from to val l ctx)
  (go (from == signature ctx) pf)))





l=l : ∀ (l : Label) -> (l == l) ≡ true
l=l [] = refl
l=l (x ∷ l) rewrite i=i (fst x) | i=i (snd x) = l=l l

--sub≡ : ∀ (a b : Integer) -> subInteger a b ≡ a - b
--add≡ : ∀ (a b : Integer) -> addInteger a b ≡ a + b
{-
≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a ≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl



<to<ᵇ : ∀ {a b} -> a < b -> (a <ᵇ b) ≡ true
<to<ᵇ {zero} (s≤s pf) = refl
<to<ᵇ {suc a} (s≤s pf) = <to<ᵇ pf-}


≤NtoLeqN : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤NtoLeqN {b = zero} N.z≤n = refl
≤NtoLeqN {b = N.suc b} N.z≤n = refl
≤NtoLeqN (N.s≤s p) = ≤NtoLeqN p

≤toGeq : ∀ {a b} -> a ≤ b -> geq b a ≡ true
≤toGeq (-≤- n≤m) = ≤NtoLeqN n≤m
≤toGeq -≤+ = refl
≤toGeq (+≤+ m≤n) = ≤NtoLeqN m≤n

≢to/= : ∀ (a b : PubKeyHash) -> a ≢ b -> (a /= b) ≡ true
≢to/= (pos n) (pos m) p with eqNat n m in eq
...| False = refl
...| True rewrite ==to≡ n m eq = ⊥-elim (p refl)
≢to/= (pos n) (negsuc m) p = refl
≢to/= (negsuc n) (pos m) p = refl
≢to/= (negsuc n) (negsuc m) p with eqNat m n in eq
...| False = refl
...| True rewrite ==to≡ m n eq = ⊥-elim (p refl)

transitionImpliesValidator : ∀ { s} (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : record { label = l ; context = record { value = (inputVal ctx) ; tsig = s } }
                              ~[ i ]~>
                              record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx)
                              ; tsig = signature ctx } })
                           -> agdaValidator l i ctx ≡ true
transitionImpliesValidator l (Open pkh) ctx (TOpen p1 p2 p3 p4)
  rewrite p1 | p2 | sym p3 | p4 | i=i (signature ctx) | l=l (outputLabel ctx) | i=i (inputVal ctx) = refl
transitionImpliesValidator l (Close pkh) ctx (TClose p1 p2 p3 p4)
  rewrite p1 | p2 | sym p3 | p4 | i=i (signature ctx) | l=l (outputLabel ctx) | i=i (inputVal ctx) = refl
transitionImpliesValidator l (Withdraw pkh val) ctx (TWithdraw {v = v} p1 p2 p3 p4 p5 p6)
  rewrite sym p1 | i=i pkh | p2 | ≤toGeq p3 | ≤toGeq p4 | sym (sub≡ v val) | sym p5
  | sym (sub≡ (inputVal ctx) val) | sym p6 | i=i (outputVal ctx) | l=l (outputLabel ctx) = refl 
transitionImpliesValidator l (Deposit pkh val) ctx (TDeposit {v = v} p1 p2 p3 p4 p5)
  rewrite p1 | p2 | i=i (signature ctx) | ≤toGeq p3 | sym (add≡ (inputVal ctx) val) | sym p5 |
  i=i (outputVal ctx) | sym (add≡ v val) | sym p4 | l=l (outputLabel ctx) = refl
transitionImpliesValidator l (Transfer from to val) ctx (TTransfer {vF = vF} {vT = vT} p1 p2 p3 p4 p5 p6 p7 p8)
  rewrite sym p1 | p2 | p3 | p8 | i=i from | i=i (inputVal ctx) | ≤toGeq p4 | ≤toGeq p5 |
  ≢to/= from to p6 | sym (add≡ vT val) | sym (sub≡ vF val) | sym p7 | l=l (outputLabel ctx) = refl


lemmaMultiStep : ∀ {s s' s'' : State} {is is' : List Input}
                   -> s  ~[ is  ]~* s'
                   -> s' ~[ is' ]~* s''
                   -> s  ~[ is ++ is' ]~* s''
lemmaMultiStep {s} {.s} {s''} {[]} {is'} root p2 = p2
lemmaMultiStep {s} {s'} {s''} {i ∷ is} {is'} (cons {s' = s'''} x p1) p2 = cons x (lemmaMultiStep p1 p2)

{-
makeIs : Label -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = if (b == emptyValue) then (makeIs l)
                                             else (Withdraw a b) ∷ (makeIs l)
-}

{-
makeIs : Label -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = (Withdraw a b) ∷ (makeIs l)
-}

makeIs : Label -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = (Withdraw a b) ∷ (Close a) ∷ (makeIs l)

makeL : Label -> Label
makeL [] = []
makeL ((a , b) ∷ l) = (a , emptyValue) ∷ (makeL l)

{-
lastOutVal : State -> Value
lastOutVal record { label = [] ; context = record { value = value ; outVal = outVal ; outAdr = outAdr ; tsig = tsig } } = outVal
lastOutVal record { label = ((a , b) ∷ []) ; context = context } = a
lastOutVal record { label = (x ∷ y ∷ label) ; context = context } = lastOutVal ( record { label = (y ∷ label) ; context = context })

lastOutAdr : State -> PubKeyHash
lastOutAdr record { label = [] ; context = record { value = value ; outVal = outVal ; outAdr = outAdr ; tsig = tsig } } = outAdr
lastOutAdr record { label = ((a , b) ∷ []) ; context = context } = b
lastOutAdr record { label = (x ∷ y ∷ label) ; context = context } = lastOutAdr ( record { label = (y ∷ label) ; context = context })
-}

{-
lastSig : State -> PubKeyHash
lastSig record { label = [] ; context = record { value = value ; tsig = tsig } } = tsig
lastSig record { label = ((a , b) ∷ []) ; context = context } = a
lastSig record { label = (x ∷ y ∷ label) ; context = record { value = value ; tsig = sig } }
  = lastSig ( record { label = (y ∷ label)
                     ; context = record { value = value
                                        ; tsig = fst x } })
-}
{-
lastSig : State -> PubKeyHash
lastSig record { label = [] ; context = record { value = value ; tsig = tsig } } = tsig
lastSig record { label = ((fst , snd) ∷ []) ; context = record { value = value ; tsig = tsig } } = fst
lastSig record { label = ((fst , snd) ∷ y ∷ label) ; context = record { value = value ; tsig = tsig } }
  = lastSig (record { label = y ∷ label ; context = record { value = value ; tsig = fst } })
-}

lastSig : State -> PubKeyHash
lastSig record { label = [] ; context = record { value = value ; tsig = tsig } } = tsig
lastSig record { label = (x ∷ []) ; context = record { value = value ; tsig = tsig } } = fst x
lastSig record { label = (x ∷ y ∷ label) ; context = ctx }
  = lastSig (record { label = y ∷ label ; context = ctx })

{-
record Context : Set where
  field
    value         : Value  
    outVal        : Value
    outAdr        : PubKeyHash
    tsig          : PubKeyHash
open Context-}



--prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7-}


lookupProp1 : ∀ {b : Bool} {a : Set} { x y z : Maybe a }
            -> b ≡ true
            -> x ≡ z
            -> (if b then x else y) ≡ z
lookupProp1 refl refl = refl


deleteProp1 : ∀ {b : Bool} { x y z : Label }
            -> b ≡ true
            -> x ≡ z
            -> z ≡ (if b then x else y)
deleteProp1 refl refl = refl

{-
        -> (makeIs (label s)) = (is ++ is')
        -> label s' ≡ is' --makeL (label s)
-}

--generalized

{-
prop : ∀ (s s' : State)
        -> label s' ≡ makeL (label s)
        -> value (context s') ≡ 0
        -> tsig (context s') ≡ lastSig s
        -> value (context s) ≡ sumVal (label s)
        -> Valid s
        -> s ~[ (makeIs (label s)) ]~* s'
prop record { label = [] ; context = record { value = .(sumVal []) ; tsig = tsig₁ } } record { label = .(makeL []) ; context = record { value = .0 ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; tsig = tsig₁ } })) } } refl refl refl refl (Always x x₁) = root
prop record { label = (x ∷ label) ; context = context } record { label = label' ; context = context' } p1 p2 p3 p4 p5 with (snd x) == emptyValue in eq
...| True = {!prop!}
...| False = cons {s' = record { label = (fst x , emptyValue) ∷ label
                         ; context = record { value = sumVal label
                                            ; tsig = fst x}}}
             (TWithdraw refl ((lookupProp1 (i=i (fst x)) refl)) {!!} {!!} {!!} {!!} ) ({!prop!})  -}

{-
prop record { label = [] ; context = record { value = .(sumVal []) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } } record { label = .(makeL []) ; context = record { value = .0 ; outVal = .(lastOutVal (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; outAdr = .(lastOutAdr (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) } } refl refl refl refl refl refl p7 = root
prop record { label = (x ∷ label)
            ; context = context }
     record { label = label'
            ; context = context' }
            p1 p2 p3 p4 p5 p6 p7
     with (snd x) == emptyValue in eq
...| True = {!prop!}
...| False = cons {s' = record { label = (fst x , emptyValue) ∷ label
                         ; context = record { value = sumVal label
                                            ; outVal = snd x
                                            ; outAdr = fst x
                                            ; tsig = fst x}}}
             (TWithdraw refl ((lookupProp1 (i=i (fst x)) refl)) {!!} {!!} {!!} {!!} refl refl) {!prop!}
-}
--no liveness

{-cons {s' = record { label = (fst x , emptyValue) ∷ label
                         ; context = record { value = sumVal label
                                            ; outVal = snd x
                                            ; outAdr = fst x
                                            ; tsig = fst x}}}
     (TWithdraw refl (lookupProp1 (i=i (fst x)) refl) {!!} {!!} {!!} {!!} refl refl) {!prop!}
-}
{-
prop1 : ∀ (s s' : State)
        -> label s' ≡ makeL (label s)
        -> value (context s') ≡ 0
        -> tsig (context s') ≡ lastSig s
        -> value (context s) ≡ sumVal (label s)
        -> Valid s
        -> s ~[ (makeIs (label s)) ]~* s'
prop1 record { label = [] ; context = record { value = .(sumVal []) ; tsig = tsig₁ } } record { label = .[] ; context = record { value = .0 ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; tsig = tsig₁ } })) } } refl refl refl refl (Always x x₁) = root
prop1 record { label = (x ∷ label) ; context = context } record { label = label' ; context = context' } p1 p2 p3 p4 p5 = cons {s' = record
            { label = (fst x , emptyValue) ∷ label
            ; context = record
              { value = sumVal label
              ; tsig = fst x
              }}} (TWithdraw refl (lookupProp1 (i=i (fst x)) refl) {!!} {!!} {!!} {!!}) {!prop1!}

-- get a counter for empty values on both labels
-}

n≤n : ∀ (n : Nat) -> n N.≤ n
n≤n zero = N.z≤n
n≤n (N.suc n) = N.s≤s (n≤n n)

v≤v : ∀ (v : Value) -> v ≤ v
v≤v (pos n) = +≤+ (n≤n n)
v≤v (negsuc n) = -≤- (n≤n n)

{-zero = ? --z≤n
v≤v (suc v) = ? --s≤s (v≤v v)-}

getGeq : ∀ {s x label context}
         -> s ≡ record { label = x ∷ label ; context = context }
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
minusLemma .(b + pos n) b (pos n) refl rewrite +-assoc b (pos n) (- (pos n))
           | [+m]-[+n]≡m⊖n n n | n⊖n≡0 n | +-identityʳ b = refl
minusLemma .(b + negsuc n) b (negsuc n) refl rewrite +-assoc b (negsuc n) (- (negsuc n))
           | n⊖n≡0 (N.suc n) | +-identityʳ b = refl


sameLastSig' : ∀ {x context context'} (label : Label)
  -> lastSig (record { label = x ∷ label ; context = context }) ≡
     lastSig (record { label = x ∷ label ; context = context' })
sameLastSig' [] = refl --refl
sameLastSig' (y ∷ label) = sameLastSig' label

sameLastSig : ∀ {x context} (label : Label)
  -> lastSig (record { label = label ; context = record { value = sumVal label ; tsig = fst x } }) ≡
     lastSig (record { label = x ∷ label ; context = context })
sameLastSig [] = refl --refl
sameLastSig (y ∷ label) = sameLastSig' label

--sameLastSig {!label!}
     

--rewrite m-n≡m⊖n c c = {!!} --rewrite -m+n≡n⊝m c c = {!!}

{-
minusLemma : ∀ (a b c : Value) -> a ≡ b + c -> a - c ≡ b
minusLemma a b (pos zero) p rewrite +-identityʳ a | +-identityʳ b = p
minusLemma a b +[1+ n ] p = {!!}
minusLemma a b (negsuc zero) p = {!!}
minusLemma a b (negsuc (N.suc n)) p = {!!}-}

refactor : ∀ (a b c : Value) -> a ≡ b + c -> c ≡ a - b
refactor a b c p rewrite +-comm b c = sym (minusLemma a c b p)

subValid : ∀ {x label context}
  -> Valid (record { label = x ∷ label ; context = context })
  -> All (λ y → geq (snd y) emptyValue ≡ true) label
subValid (Always x (allCons {{i}} {{is}})) = is

prop1 : ∀ (s s' : State) {l : Label}
        -> label s ≡ l
        -> label s' ≡ []
        -> value (context s') ≡ 0
        -> tsig (context s') ≡ lastSig s
        -> value (context s) ≡ sumVal (label s)
        -> Valid s
        -> s ~[ (makeIs (label s)) ]~* s'
prop1 record { label = [] ; context = record { value = .(sumVal []) ; tsig = tsig₁ } } record { label = .[] ; context = record { value = .0 ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; tsig = tsig₁ } })) } } {.[]} refl refl refl refl refl (Always x x₁) = root --root
prop1 s1@(record { label = (x ∷ label) ; context = context }) s2@(record { label = label' ; context = context' }) {.(x ∷ label)} refl p2 p3 p4 p5 p6 rewrite sym (sameLastSig {x} {context} label) --(Always a b) rewrite i-i
  = cons {s' = record
            { label = (fst x , emptyValue) ∷ label
            ; context = record
              { value = sumVal label
              ; tsig = fst x
              }}}
            (TWithdraw refl (lookupProp1 (i=i (fst x)) refl) (getGeq refl p6) (v≤v (snd x)) (deleteProp1 (i=i (fst x)) (rewriteLabel (fst x) (snd x) label)) (refactor (value context) (snd x) (sumVal label) p5))
            (cons {s' = record
                  { label = label
                  ; context = record
                    { value = sumVal label
                    ; tsig = fst x
                  }}}
            (TClose refl (lookupProp1 (i=i (fst x)) refl) (deleteProp1 (i=i (fst x)) refl) refl)
            (prop1 (record { label = label
                           ; context = record { value = sumVal label
                                              ; tsig = fst x}})
            s2 {label} refl p2 p3 p4 refl (Always refl (subValid p6))))


{-
prop1 record { label = [] ; context = record { value = .(sumVal []) ; tsig = tsig₁ } } record { label = .[] ; context = record { value = .0 ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; tsig = tsig₁ } })) } } refl refl refl refl (Always x x₁) = root
prop1 record { label = (x ∷ label) ; context = context } record { label = label' ; context = context' } p1 p2 p3 p4 p5 = cons {s' = record
            { label = (fst x , emptyValue) ∷ label
            ; context = record
              { value = sumVal label
              ; tsig = fst x
              }}}
            (TWithdraw refl (lookupProp1 (i=i (fst x)) refl) {!!} {!!} {!!} {!!})
            (cons {s' = record
                  { label = label
                  ; context = record
                    { value = sumVal label
                    ; tsig = fst x
                  }}}
            (TClose {!!} {!!} {!!} {!!}) (prop1 {!!} {!!} {!!} {!!} {!!} {!!} {!!}))-}



{-
prop1 record { label = [] ; context = record { value = .(sumVal []) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } } record { label = [] ; context = record { value = .0 ; outVal = .(lastOutVal (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; outAdr = .(lastOutAdr (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) } } refl refl refl refl refl refl p = root

prop1 record { label = (x ∷ label) ; context = context } record { label = [] ; context = context' } p1 p2 p3 p4 p5 p6 p7  = {!!} {-cons {s' = record
           { label = label
           ; context = record
             { value = sumVal label
             ; outVal = snd x
             ; outAdr = fst x
             ; tsig = fst x
             }}} (TWithdraw refl (lookupProp1 (i=i (fst x)) refl) {!!} {!!} {!!} {!!} refl refl) {!prop1!}-}
-}

{-
prop1 record { label = [] ; context = record { value = .(sumVal []) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } } record { label = .[] ; context = record { value = .0 ; outVal = .(lastOutVal (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; outAdr = .(lastOutAdr (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; tsig = .(lastSig (record { label = [] ; context = record { value = sumVal [] ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) } } refl refl refl refl refl refl = root
prop1 record { label = ((fst₁ , snd₁) ∷ label₁) ; context = record { value = .(sumVal ((fst₁ , snd₁) ∷ label₁)) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } } record { label = .[] ; context = record { value = .0 ; outVal = .(lastOutVal (record { label = (fst₁ , snd₁) ∷ label₁ ; context = record { value = sumVal ((fst₁ , snd₁) ∷ label₁) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; outAdr = .(lastOutAdr (record { label = (fst₁ , snd₁) ∷ label₁ ; context = record { value = sumVal ((fst₁ , snd₁) ∷ label₁) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) ; tsig = .(lastSig (record { label = (fst₁ , snd₁) ∷ label₁ ; context = record { value = sumVal ((fst₁ , snd₁) ∷ label₁) ; outVal = outVal₁ ; outAdr = outAdr₁ ; tsig = tsig₁ } })) } } refl refl refl refl refl refl
  = cons {s' = record
      { label = (insert fst₁ 0 label₁)
      ; context =
          record
          { value = sumVal label₁
          ; outVal = snd₁
          ; outAdr = fst₁
          ; tsig = fst₁
          }
      }} (TWithdraw refl {!refl!} {!!} {!!} {!!} {!!} refl refl) {!prop1!} --(prop1 {!!} {!!} refl refl {!!} {!!} {!!} refl)-}


liquidity : ∀ (s : State)
          -> value (context s) ≡ sumVal (label s)
          -> Valid s
          -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (value (context s') ≡ 0) )

liquidity s p1 p2 =
  ⟨ record { label = [] ; context = record { value = 0 ; tsig = lastSig s } } ,
  ⟨ makeIs (label s) , (prop1 s (record { label = [] ; context = record { value = 0 ; tsig = lastSig s } }) {label s}
  refl refl refl refl p1 p2 , refl) ⟩ ⟩

{-
liquidity record { label = [] ; context = record { value = .(sumVal []) ; tsig = tsig₁ } } refl
  = ⟨ (record
        { label = []
        ; context =
            record
            { value = pos zero
            ; tsig = tsig₁
            }
        }) , ⟨ [] , (root , refl) ⟩ ⟩
liquidity record { label = (x ∷ label) ; context = record { value = .(sumVal (x ∷ label)) ; tsig = tsig₁ } } refl
  = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩

-}

--  | sym (rewriteSub (inputVal ctx) (payAmt ctx) p6)

{-
foo : (x w : Maybe ℤ) →
    x ≡ w → {a b : ℤ}
    (pf : not (( (Maybe ℤ -> Bool) ∋ (λ { Nothing → false ; (Just v) → true })) w) ≡ true) →
    a ≡ b
foo x w p pf = {!!}



aux2 : (x w : Maybe ℤ) →
    x ≡ w → {a b : ℤ}
    (pf : not ((case w of λ { Nothing → false ; (Just v) → true })) ≡ true) →
    a ≡ b
aux2 x w p pf = {!!}
-}


--sub-lemmas and helper functions for validator returning true implies transition
{-
≤ᵇto≤ : ∀ {a b} -> (a <ᵇ b || b ≡ᵇ a) ≡ true -> a ≤ b
≤ᵇto≤ {zero} {zero} pf = z≤n
≤ᵇto≤ {zero} {suc b} pf = z≤n
≤ᵇto≤ {suc a} {suc b} pf = s≤s (≤ᵇto≤ pf)

<ᵇto< : ∀ {a b} -> (a <ᵇ b) ≡ true -> a < b
<ᵇto< {zero} {suc b} pf = s≤s z≤n
<ᵇto< {suc a} {suc b} pf = s≤s (<ᵇto< pf)

3&&false : ∀ (a b c : Bool) -> (a && b && c && false) ≡ true -> ⊥
3&&false true true true ()

p1 : ∀ (a b c d e f : Bool) (x y : Value) -> ((x ≡ᵇ y) && a && b && c && d && e && f) ≡ true -> x ≡ y
p1 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y)  pf)

p2 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && (x <ᵇ y || y ≡ᵇ x) && b && c && d && e && f) ≡ true -> x ≤ y
p2 a b c d e f x y pf = ≤ᵇto≤ ( get ((x <ᵇ y || y ≡ᵇ x)) (go a pf) )

p3 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && b && (x <ᵇ y) && c && d && e && f) ≡ true -> x < y
p3 a b c d e f x y pf = <ᵇto< ( get (x <ᵇ y) (go b (go a pf)) )

p4 : ∀ (a b c d e f : Bool) (x y : Value) -> (a && b && c && (x ≡ᵇ y) && d && e && f) ≡ true -> x ≡ y
p4 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) (go c (go b (go a pf))) )

p5 : ∀ (a b c d e f : Bool) (x y : PubKeyHash) -> (a && b && c && d && (x == y) && e && f) ≡ true -> x ≡ y
p5 a b c d e f x y pf = ==ito≡ x y (get (x == y) (go d (go c (go b (go a pf)))) )

p6 : ∀ (a b c d e f : Bool) (x y : Deadline) -> (a && b && c && d && e && (x ≡ᵇ y) && f) ≡ true -> x ≡ y
p6 a b c d e f x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) (go e (go d (go c (go b (go a pf))))))

p7 : ∀ (a b c d e f : Bool) (x y : List PubKeyHash) -> (a && b && c && d && e && f && (x == y)) ≡ true -> x ≡ y
p7 a b c d e f x y pf = ==lto≡ x y (go f (go e (go d (go c (go b (go a pf))))))

orToSum : ∀ (a b : Bool) -> (a || b) ≡ true -> a ≡ true ⊎ b ≡ true
orToSum false true pf = inj₂ refl
orToSum true b pf = inj₁ refl

queryTo∈ : ∀ {sig sigs} -> (query sig sigs) ≡ true -> sig ∈ sigs
queryTo∈ {sig} {x ∷ sigs} pf with orToSum (x == sig) (query sig sigs) pf
... | inj₁ a = here (sym (==ito≡ x sig a))
... | inj₂ b = there (queryTo∈ b)

a2 : ∀ (a b c d e f : Bool) (x y : PubKeyHash) -> (a && (x == y) && b && c && d && e && f) ≡ true -> x ≡ y
a2 a b c d e f x y pf = ==ito≡ x y ( get (x == y) (go a pf) )

a3 : ∀ (a b c d e f : Bool) (sig : PubKeyHash) (sigs : List PubKeyHash) -> (a && b && (query sig sigs) && c && d && e && f) ≡ true -> sig ∈ sigs
a3 a b c d e f sig sigs pf = queryTo∈ ( get (query sig sigs) (go b (go a pf)) )

lengthNatToLength : ∀ (n : ℕ) (l : List PubKeyHash) -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true -> n ≤ length l
lengthNatToLength zero [] pf = z≤n
lengthNatToLength zero (x ∷ l) pf = z≤n
lengthNatToLength (suc n) (x ∷ l) pf = s≤s (lengthNatToLength n l pf)

y1 : ∀ (a b c : Bool) (n : ℕ) (sigs : List PubKeyHash) -> ((n <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ n) && (a && b) && c) ≡ true -> n ≤ length sigs
y1 a b c n sigs pf = lengthNatToLength n sigs (get (n <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ n) pf)

y2 : ∀ (a b c : Bool) (x y : PubKeyHash) -> (a && ((x == y) && b) && c) ≡ true -> x ≡ y
y2 a b c x y pf = ==ito≡ x y (get (x == y) (get ((x == y) && b) (go a pf)))

y3 : ∀ (a b c : Bool) (x y : Value) -> (a && (b && (x ≡ᵇ y)) && c) ≡ true -> x ≡ y
y3 a b c x y pf = ≡ᵇto≡ (go b (get (b && (x ≡ᵇ y)) (go a pf)))

y4 : ∀ (a b c : Bool) (x y : Value) -> (a && (b && c) && x ≡ᵇ y) ≡ true -> x ≡ y
y4 a b c x y pf = ≡ᵇto≡ (go (b && c) (go a pf))

c1 : ∀ (a : Bool) (x y : Value) -> (x ≡ᵇ y && a) ≡ true -> x ≡ y
c1 a x y pf = ≡ᵇto≡ (get (x ≡ᵇ y) pf) 

c2 : ∀ (a : Bool) (x y : Deadline) -> (a && (x <ᵇ y)) ≡ true -> x < y
c2 a x y pf = <ᵇto< (go a pf)
-}

{-
 (rewriteSub l pkh v val (==lto≡ (newLabel ctx) (insert pkh (subInteger v val) l)
              (go (geq v val) (go (geq val +0) (get (checkWithdraw (Just v) pkh val l ctx)
              (go (pkh == signature ctx) pf))))))-}

--(==lto≡ ( (newLabel ctx)) {! (insert pkh (subInteger v val) l)!} {!!})
{-(==lto≡ (newLabel ctx) (insert pkh (subInteger v val) l)
              (get ((newLabel ctx) == (insert pkh (subInteger v val) l))
              (go (geq v val) (go (geq val +0) (get {!!} {!!})))))-}
{-((ltInteger +0 val || eqInteger +0 val) &&
        (ltInteger val v || eqInteger val v) &&
        (outputLabel ctx) == (insert pkh (addInteger v (negateInteger val)) l))-}
--  (geqto≤ (here (here (skip {!!}))))
-- (geqto≤ (get (geq val +0) (go (pkh == (signature ctx)) {!pf!})))


{-validatorImpliesTransition [] (Open pkh) ctx pf
  = TOpen (sym (==ito≡ pkh (signature ctx) (get (pkh == (signature ctx)) pf))) refl
    (==lto≡ (outputLabel ctx) ((pkh , +0) ∷ []) (get ((outputLabel ctx) == ((pkh , +0) ∷ []))
    (go (pkh == (signature ctx)) pf))) (sym (==ito≡ (outputVal ctx) (inputVal ctx)
    (go ((outputLabel ctx) == ((pkh , +0) ∷ [])) (go (pkh == (signature ctx)) pf))))
validatorImpliesTransition [] (Close pkh) ctx pf = ⊥-elim (&&false (pkh == (signature ctx)) pf)
validatorImpliesTransition [] (Withdraw pkh val) ctx pf = ⊥-elim (&&false (pkh == (signature ctx)) pf)
validatorImpliesTransition [] (Deposit pkh val) ctx pf = ⊥-elim (&&false (pkh == (signature ctx)) pf)
validatorImpliesTransition [] (Transfer from to val) ctx pf = ⊥-elim (&&false (from == (signature ctx)) pf)
validatorImpliesTransition ((fst , snd) ∷ l) (Open pkh) ctx pf = TOpen {!!} {!!} {!!} {!!}
{-with eqInteger pkh fst in eq
...| true = ?
...| false = ? -}
{-with pkh == (fst x)
...| false = ?
...| true = {!!}-}
validatorImpliesTransition (x ∷ l) (Close pkh) ctx pf = {!!}
validatorImpliesTransition (x ∷ l) (Withdraw pkh val) ctx pf = {!!}
validatorImpliesTransition (x ∷ l) (Deposit pkh val) ctx pf = {!!}
validatorImpliesTransition (x ∷ l) (Transfer from to pkh) ctx pf = {!!}-}

{-par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) ( (v <ᵇ inputVal || inputVal ≡ᵇ v)) (0 <ᵇ v) pf)
validatorImpliesTransition par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  rewrite p1 (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) outputVal inputVal pf
  | sym (p4 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (pkh == pkh') (d ≡ᵇ d') (sigs' == []) v v' pf)
  | p5 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (d ≡ᵇ d') (sigs' == []) pkh pkh' pf
  | p6 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (sigs' == []) d d' pf
  | p7 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs' [] pf
  = TPropose (p2 (outputVal ≡ᵇ inputVal) (0 <ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) v inputVal pf)
    (p3 (outputVal ≡ᵇ inputVal) (v <ᵇ inputVal || inputVal ≡ᵇ v) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == []) 0 v pf) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (3&&false (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) pf)
validatorImpliesTransition par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  rewrite p1 (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) outputVal inputVal pf
  | sym (p4 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) v v' pf)
  | p5 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (d ≡ᵇ d') (sigs' == (insert sig sigs)) pkh pkh' pf
  | p6 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (sigs' == (insert sig sigs)) d d' pf
  | p7 (outputVal ≡ᵇ inputVal) (sig == signature) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') sigs' (insert sig sigs) pf
  = TAdd (a3 (outputVal ≡ᵇ inputVal) (sig == signature) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig (authSigs par) pf)
  (sym (a2 (outputVal ≡ᵇ inputVal) (query sig (authSigs par)) (v ≡ᵇ v') (pkh == pkh') (d ≡ᵇ d') (sigs' == (insert sig sigs)) sig signature pf)) refl refl refl
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = TPay (y4 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (pkh == payTo) (v ≡ᵇ payAmt) inputVal (outputVal + v) pf)
    (y1 (eqInteger pkh payTo) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) (nr par) sigs pf) refl refl
    (sym (y3 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (pkh == payTo) (inputVal ≡ᵇ outputVal + v) v payAmt pf))
    (sym (y2 (nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par) (v ≡ᵇ payAmt) (inputVal ≡ᵇ outputVal + v) pkh payTo pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Pay
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (&&false ((nr par <ᵇ lengthNat sigs || lengthNat sigs ≡ᵇ nr par)) pf) 
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = TCancel (c2 (outputVal ≡ᵇ inputVal) d time pf) refl refl (sym (c1 (d <ᵇ time) outputVal inputVal pf))
validatorImpliesTransition par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting v' pkh' d' sigs') ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature } pf
  = ⊥-elim (&&false (outputVal ≡ᵇ inputVal) pf) -}


--sub-lemmas for transition implies validation returns true
{-


||true : ∀ {b} -> (b || true) ≡ true
||true {false} = refl
||true {true} = refl

∈toQuery : ∀ {sig sigs} -> sig ∈ sigs -> (query sig sigs) ≡ true
∈toQuery {sig} (here refl) rewrite i=i sig = refl
∈toQuery (there pf) rewrite ∈toQuery pf = ||true

lengthToLengthNat : ∀ (n : ℕ) (l : List PubKeyHash) -> n ≤ length l -> (n <ᵇ lengthNat l || lengthNat l ≡ᵇ n) ≡ true
lengthToLengthNat zero [] z≤n = refl
lengthToLengthNat zero (x ∷ l) z≤n = refl
lengthToLengthNat (suc n) (x ∷ l) (s≤s pf) = lengthToLengthNat n l pf

-}

{-par Holding (Propose v pkh d)
  record { inputVal = inputVal ;
           outputVal = outputVal ;
           outputLabel = (Collecting _ _ _ []) ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature }
  (TPropose p1 p2 refl refl p5)
  rewrite ≡to≡ᵇ (sym p5) | ≤to≤ᵇ p1 | <to<ᵇ p2 | v=v v | i=i pkh | v=v d = refl
transitionImpliesValidator par (Collecting v pkh d sigs) (Add sig)
  record { inputVal = inputVal ;
           outputVal = .(inputVal) ;
           outputLabel = (Collecting .v .pkh .d .(insert sig sigs)) ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = .sig }
  (TAdd p1 refl refl refl refl)
  rewrite v=v inputVal | i=i sig | ∈toQuery p1 | v=v v | i=i pkh | v=v d | l=l (insert sig sigs) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) Pay
  record { inputVal = .(addNat outputVal v) ;
           outputVal = outputVal ;
           outputLabel = Holding ;
           time = time ;
           payTo = .pkh ;
           payAmt = .v ;
           signature = signature }
  (TPay refl p2 refl refl refl refl)
  rewrite i=i pkh | v=v v | lengthToLengthNat (nr par) sigs p2 | v=v (outputVal + v) = refl
transitionImpliesValidator par (Collecting v pkh d sigs) Cancel
  record { inputVal = inputVal ;
           outputVal = .(inputVal) ;
           outputLabel = Holding ;
           time = time ;
           payTo = payTo ;
           payAmt = payAmt ;
           signature = signature }
  (TCancel p1 refl refl refl)
  rewrite v=v inputVal | <to<ᵇ p1 = refl -}


{-


--Prop1 sub-lemmas and helper functions
makeIs : List PubKeyHash -> List Input
makeIs [] = []
makeIs (x ∷ pkhs) = Add x ∷ makeIs pkhs

insertList : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
insertList [] sigs = sigs
insertList (x ∷ asigs) sigs = insertList asigs (insert x sigs)

appendLemma : ∀ (x : PubKeyHash) (a b : List PubKeyHash) -> a ++ x ∷ b ≡ (a ++ x ∷ []) ++ b
appendLemma x [] b = refl
appendLemma x (a ∷ as) b = cong (λ y → a ∷ y) (appendLemma x as b) 

∈lemma : ∀ (xs ys : List PubKeyHash) (z : PubKeyHash) -> z ∈ (xs ++ z ∷ ys)
∈lemma [] ys z = here refl
∈lemma (x ∷ xs) ys z = there (∈lemma xs ys z)

finalSig : ∀ (s : State) -> (ls : List Input) -> PubKeyHash
finalSig s [] = tsig (context s)
finalSig s (Propose x x₁ x₂ ∷ [])  = tsig (context s)
finalSig s (Add sig ∷ []) = sig
finalSig s (Pay ∷ []) = tsig (context s)
finalSig s (Cancel ∷ []) = tsig (context s)
finalSig s (i ∷ ls) = finalSig s ls

finalSigLemma : ∀ (s s' : State) (x : PubKeyHash) (xs : List PubKeyHash)
  -> tsig (context s') ≡ x -> finalSig s (makeIs (x ∷ xs)) ≡ finalSig s' (makeIs xs)
finalSigLemma s1 s2 x [] pf = sym pf
finalSigLemma s1 s2 x (y ∷ []) pf = refl
finalSigLemma s1 s2 x (y ∷ z ∷ xs) pf = finalSigLemma s1 s2 x (z ∷ xs) pf

--Generalized Prop1 (Can add signatures 1 by 1)
prop : ∀ {v pkh d sigs} (s s' : State) (par : Params) (asigs asigs' asigs'' : List PubKeyHash)
         -> asigs ≡ (authSigs par)
         -> asigs ≡ (asigs' ++ asigs'')
         -> label s ≡ Collecting v pkh d sigs
         -> label s' ≡ Collecting v pkh d (insertList asigs'' sigs)
         -> outVal (context s) ≡ outVal (context s')
         -> outAdr (context s) ≡ outAdr (context s')
         -> now (context s) ≡ now (context s')
         -> value (context s) ≡ value (context s')
         -> tsig (context s') ≡ finalSig s (makeIs asigs'')
         -> par ⊢ s ~[ makeIs asigs'' ]~* s'

prop {v} {pkh} {d} {sigs}
  record { label = .(Collecting v pkh d sigs) ;
           context = record { value = .value₁ ;
                              outVal = .outVal₁ ;
                              outAdr = .outAdr₁ ;
                              now = .now₁ ;
                              tsig = tsig₁ } }
  record { label = .(Collecting v pkh d (insertList [] sigs)) ;
           context = record { value = value₁ ;
                              outVal = outVal₁ ;
                              outAdr = outAdr₁ ;
                              now = now₁ ;
                              tsig = .(finalSig (record { label = Collecting v pkh d sigs ;
                                                          context = record { value = value₁ ;
                                                                             outVal = outVal₁ ;
                                                                             outAdr = outAdr₁ ;
                                                                             now = now₁ ;
                                                                             tsig = tsig₁ } }) (makeIs [])) } }
  record { authSigs = .(sigs2 ++ []) ;
           nr = nr₁ }
  .(sigs2 ++ []) sigs2 [] refl refl refl refl refl refl refl refl refl = root
  
prop {v} {pkh} {d} {sigs}
  s1@(record { label = .(Collecting v pkh d sigs) ;
               context = record { value = .value₁ ;
                                  outVal = .outVal₁ ;
                                  outAdr = .outAdr₁ ;
                                  now = .now₁ ;
                                  tsig = tsig₁ } })
  s2@(record { label = .(Collecting v pkh d (insertList (x ∷ sigs3) sigs)) ;
               context = record { value = value₁ ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = .(finalSig s1 (makeIs (x ∷ sigs3))) } })
  par@(record { authSigs = .(sigs2 ++ x ∷ sigs3) ; nr = nr₁ })
  .(sigs2 ++ x ∷ sigs3) sigs2 (x ∷ sigs3) refl refl refl refl refl refl refl refl refl
  
  = cons
    (TAdd (∈lemma sigs2 sigs3 x) refl refl refl refl)
    (prop s' s2 par (sigs2 ++ x ∷ sigs3) (sigs2 ++ [ x ]) sigs3 refl
          (appendLemma x sigs2 sigs3) refl refl refl refl refl refl
          (finalSigLemma s1 s' x sigs3 refl))
    where
      s' = record { label = Collecting v pkh d (insert x sigs) ;
                    context = record { value = value₁ ;
                                       outVal = outVal₁ ;
                                       outAdr = outAdr₁ ;
                                       now = now₁ ;
                                       tsig = x }}


--Actual Prop1 (Can add all signatures 1 by 1)
prop1 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
        -> label s ≡ Collecting v pkh d sigs
        -> label s' ≡ Collecting v pkh d (insertList (authSigs par) sigs)
        -> outVal (context s) ≡ outVal (context s')
        -> outAdr (context s) ≡ outAdr (context s')
        -> now (context s) ≡ now (context s')
        -> value (context s) ≡ value (context s')
        -> tsig (context s') ≡ finalSig s (makeIs (authSigs par))
        -> par ⊢ s ~[ (makeIs (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 = prop s s' par (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7



--UniqueInsertLemma sub-lemmas


_⊆_ : List a -> List a -> Set
l1 ⊆ l2 = All (_∈ l2) l1

⊆-cons : (x : a){l1 l2 : List a} -> l1 ⊆ l2 -> l1 ⊆ (x ∷ l2)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : (l : List a) -> l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷ ⊆-cons x (⊆-refl l)

⊆-trans : {l1 l2 l3 : List a} -> l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3
⊆-trans [] p2 = []
⊆-trans (px ∷ p1) p2 = All.lookup p2 px ∷ ⊆-trans  p1 p2





insert-lem1 : (x : PubKeyHash)(l : List PubKeyHash) -> x ∈ insert x l
insert-lem1 x [] = here refl
insert-lem1 x (y ∷ l) with x == y in eq
... | false = there (insert-lem1 x l) 
... | true rewrite ==ito≡ x y eq = here refl

insert-lem2 : (x y : PubKeyHash)(l : List PubKeyHash) -> x ∈ l -> x ∈ insert y l
insert-lem2 x y [] pf = there pf
insert-lem2 x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite ==ito≡ y z eq | px = here refl
insert-lem2 x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem2 x y l pf) 
...| true rewrite ==ito≡ y z eq = there pf

del : ∀{x} (l : List a) -> x ∈ l -> List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) -> suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong suc (length-del p) 

∈-del : ∀{x y}{l : List a} (p : x ∈ l) -> x ≢ y -> y ∈ l -> y ∈ del l p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l1 l2 : List a} (p : x ∈ l2) -> (x ∉ l1) -> l1 ⊆ l2 -> l1 ⊆ del l2 p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e -> n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {l1 l2 : List a} -> l1 ⊆ l2 -> Unique l1 -> length l2 ≥ length l1
unique-lem [] root = z≤n
unique-lem (px ∷ sub) (x :: un) rewrite sym (length-del px) = s≤s (unique-lem (subset-del px x sub) un)

insertList-sublem : (l1 l2 : List PubKeyHash) (x : PubKeyHash) -> x ∈ l2 -> x ∈ insertList l1 l2
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l1) l2 x pf = insertList-sublem l1 (insert y l2) x (insert-lem2 x y l2 pf)


insertList-lem : (l1 l2 : List PubKeyHash) -> l1 ⊆ insertList l1 l2
insertList-lem [] l = []
insertList-lem (x ∷ l1) l2 = insertList-sublem l1 (insert x l2) x (insert-lem1 x l2) ∷ insertList-lem l1 (insert x l2)

--Unique Insert Lemma
uil : ∀ (l1 l2 : List PubKeyHash) (pf : Unique l1) -> (length (insertList l1 l2) ≥ length l1)
uil l1 l2 pf = unique-lem (insertList-lem l1 l2) pf


--Valid Parameters
data ValidP : Params -> Set where

  Always : ∀ {par}
    -> Unique (authSigs par)
    -> length (authSigs par) ≥ nr par
    ------------------
    -> ValidP par


--Multi-Step lemma
lemmaMultiStep : ∀ (par : Params) (s s' s'' : State) (is is' : List Input)
                   -> par ⊢ s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep par s .s s'' [] is' root p2 = p2
lemmaMultiStep par s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)


--Prop2 (Can add signatures 1 by 1 and then pay)
prop2 : ∀ { v pkh d sigs } (s s' : State) (par : Params)
          -> ValidS s
          -> label s ≡ Collecting v pkh d sigs
          -> label s' ≡ Holding
          -> outVal (context s') ≡ v
          -> outAdr (context s') ≡ pkh
          -> value (context s) ≡ value (context s') + v
          -> ValidP par
          -> par ⊢ s ~[ ((makeIs (authSigs par)) ++ [ Pay ]) ]~* s'
prop2 {d = d} {sigs = sigs}
  s1@(record { label = .(Collecting (outVal context₁) (outAdr context₁) d sigs) ;
               context = record { value = .(addNat (value context₁) (outVal context₁)) ;
                                  outVal = outVal₁ ;
                                  outAdr = outAdr₁ ;
                                  now = now₁ ;
                                  tsig = tsig₁ } })
  s2@record { label = .Holding ; context = context₁ }
  par (Col p1 p2 p3 p6) refl refl refl refl refl (Always p4 p5)
  = lemmaMultiStep par s1 s' s2 (makeIs (authSigs par)) [ Pay ]   
    (prop1 s1 s' par refl refl refl refl refl refl refl)
    (cons (TPay refl (≤-trans p5 (uil (authSigs par) sigs p4)) refl refl refl refl) root)
      where
        s' = record { label = Collecting (outVal context₁) (outAdr context₁) d (insertList (authSigs par) sigs) ;
                       context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                          outVal = outVal₁ ;
                                          outAdr = outAdr₁ ;
                                          now = now₁ ;
                                          tsig = finalSig (record { label = (Collecting (outVal context₁) (outAdr context₁) d sigs) ;
                                                                    context = record { value = (addNat (value context₁) (outVal context₁)) ;
                                                                              outVal = outVal₁ ;
                                                                              outAdr = outAdr₁ ;
                                                                              now = now₁ ;
                                                                              tsig = tsig₁ } }) (makeIs (authSigs par)) } }



v≤v : ∀ (v : Value) -> v ≤ v
v≤v zero = z≤n
v≤v (suc v) = s≤s (v≤v v)

--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition there and have no value left int he contract)
liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> ValidS s -> ValidP par
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value (context s') ≡ 0) )
          
liquidity'
  record { authSigs = authSigs ; nr = nr }
  s@(record { label = label ;
              context = record { value = zero ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol p1) (Always p2 p3)
  = ⟨ s , ⟨ [] , ⟨ root , refl ⟩ ⟩ ⟩
liquidity' par
  s@(record { label = .Holding ;
              context = record { value = (suc value) ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig }})
  pkh d (Hol refl) (Always p2 p3)
  = ⟨ s'' , ⟨ (Propose (suc value) pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TPropose (s≤s (v≤v value)) (s≤s z≤n) refl refl refl)
    (prop2 s' s'' par (Col refl (s≤s (v≤v value)) (s≤s z≤n) root) refl refl refl refl refl (Always p2 p3)) , refl ⟩ ⟩ ⟩
      where
        s'' = record { label = Holding ;
                      context = record { value = zero ;
                                         outVal = suc value ;
                                         outAdr = pkh ;
                                         now = now ;
                                         tsig = tsig } }
        s' = record { label = Collecting (suc value) pkh d [] ;
                       context = record { value = (suc value) ;
                                          outVal = outVal ;
                                          outAdr = outAdr ;
                                          now = now ;
                                          tsig = tsig } }
liquidity'
  record { authSigs = authSigs ; nr = nr }
  s@(record { label = label ;
              context = record { value = zero ;
                                 outVal = outVal ;
                                 outAdr = outAdr ;
                                 now = now ;
                                 tsig = tsig } })
  pkh d (Col p1 p2 p3 p6) (Always p4 p5)
  = ⟨ s , ⟨ [] , ⟨ root , refl ⟩ ⟩ ⟩
liquidity' par
  record { label = (Collecting v' pkh' d' sigs') ; context = record { value = (suc value) ; outVal = outVal ; outAdr = outAdr ; now = now ; tsig = tsig } }
  pkh d (Col refl p2 p3 p6) (Always p4 p5)
  = ⟨ s''' , ⟨ Cancel ∷ (Propose (suc value) pkh d) ∷ ((makeIs (authSigs par)) ++ [ Pay ]) ,
    ⟨ cons (TCancel {s' = s'}
    (s≤s (v≤v d')) refl refl refl)
    (cons (TPropose (s≤s (v≤v value)) (s≤s z≤n) refl refl refl)
    (prop2 s'' s''' par (Col refl (s≤s (v≤v value)) (s≤s z≤n) root) refl refl refl refl refl (Always p4 p5))) , refl ⟩ ⟩ ⟩
      where
        s''' = record { label = Holding ;
                       context = record { value = zero ;
                                          outVal = suc value ;
                                          outAdr = pkh ;
                                          now = now ;
                                          tsig = tsig } }
        s' = record { label = Holding ;
                      context = record { value = (suc value) ;
                                         outVal = outVal ;
                                         outAdr = outAdr ;
                                         now = suc d' ;
                                         tsig = tsig } }
        s'' = record { label = Collecting (suc value) pkh d [] ;
                        context = record { value = (suc value) ;
                                           outVal = outVal ;
                                           outAdr = outAdr ;
                                           now = d + 1 ;
                                           tsig = tsig } }

      



-}
 {-
data Unique {a : Set} : List a → Set where
  root : Unique []
  _::_ : {x : a} {l : List a} -> x ∉ l -> Unique l -> Unique (x ∷ l)






--Valid State
data ValidS : State -> Set where

  Hol : ∀ {s}
    -> label s ≡ Holding
    ----------------
    -> ValidS s

  Col : ∀ {s v pkh d sigs}
    -> label s ≡ Collecting v pkh d sigs
    -> value (context s) ≥ v
    -> v > 0
    -> Unique sigs
    --------------------------------
    -> ValidS s


--State Validity sub-lemmas
diffLabels : ∀ {v pkh d sigs} (l : Label) -> l ≡ Holding
           -> l ≡ Collecting v pkh d sigs -> ⊥ 
diffLabels Holding p1 ()
diffLabels (Collecting v pkh d sigs) () p2

sameValue : ∀ {v v' pkh pkh' d d' sigs sigs'}
  -> Collecting v pkh d sigs ≡ Collecting v' pkh' d' sigs' -> v ≡ v'
sameValue refl = refl

sameSigs : ∀ {v v' pkh pkh' d d' sigs sigs'}
  -> Collecting v pkh d sigs ≡ Collecting v' pkh' d' sigs' -> sigs ≡ sigs'
sameSigs refl = refl




reduce∈ : ∀ {A : Set} {x y : A} {xs} -> y ∈ (x ∷ xs) -> y ≢ x -> y ∈ xs
reduce∈ (here px) p2 = ⊥-elim (p2 px)
reduce∈ (there p1) p2 = p1 


insertPreserves∈ : ∀ {x y zs}
  -> x ∈ insert y zs -> (y == x) ≡ false -> x ∈ zs
insertPreserves∈ {zs = []} (here px) p2 = ⊥-elim (=/=ito≢ p2 (sym px))
insertPreserves∈ {x} {y} {z ∷ zs} p1 p2 with y == x in eq1
...| true =  ⊥-elim (get⊥ p2)
...| false with y == z in eq2
...| true rewrite ==ito≡ y z eq2 = p1 
...| false with x == z in eq3
...| true rewrite ==ito≡ x z eq3 = here refl 
...| false = there (insertPreserves∈ (reduce∈ p1 (=/=ito≢ eq3)) eq1)


insertPreservesUniqueness : ∀ {sig sigs}
  -> Unique sigs -> Unique (insert sig sigs)
insertPreservesUniqueness root = (λ ()) :: root
insertPreservesUniqueness {sig} {(x ∷ xs)} (p :: ps) with sig == x in eq
...| false = (λ z → p (insertPreserves∈ z eq)) :: (insertPreservesUniqueness ps)
...| true rewrite ==ito≡ sig x eq = p :: ps

--State Validity Invariant
validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition iv (TPropose p1 p2 p3 p4 p5) rewrite p5 = Col p4 p1 p2 root
validStateTransition {s} (Hol pf) (TAdd p1 p2 p3 p4 p5) = ⊥-elim (diffLabels (label s) pf p3)
validStateTransition (Col pf1 pf2 pf3 pf4) (TAdd p1 p2 p3 p4 p5)
                     rewrite pf1 | sameValue p3 | p5 | sameSigs p3
                     = Col p4 pf2 pf3 (insertPreservesUniqueness pf4)
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6) = Hol p4
validStateTransition iv (TCancel p1 p2 p3 p4) = Hol p3

validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x 


 -}


{-
validatorImpliesTransition l (Transfer from to val) ctx pf with lookup from l in eq1
validatorImpliesTransition l (Transfer from to val) ctx pf | Nothing = ⊥-elim (&&false (from == signature ctx) pf)
validatorImpliesTransition l (Transfer from to val) ctx pf | Just vF with lookup to l in eq2
validatorImpliesTransition l (Transfer from to val) ctx pf | Just vF | Nothing = ⊥-elim (&&false (from
-}
{- 
make⊥ : true ≡ false -> ⊥
make⊥ ()

sublem : ∀ (pkh pkh' : PubKeyHash)  (label : Label) (v v' : Value)
        -> (pkh == pkh') ≡ false
        -> lookup pkh (insert pkh' v' label) ≡ Just v
        -> lookup pkh label ≡ Just v
sublem pkh pkh' [] v v' p1 p2 rewrite p1 = p2
sublem pkh pkh' (x ∷ label) v v' p1 p2 with pkh' == fst x in eq1
sublem pkh pkh' (x ∷ label) v v' p1 p2 | true with pkh == fst x in eq2
sublem pkh pkh' (x ∷ label) v v' p1 p2 | true | true
  rewrite ==ito≡ pkh' (fst x) eq1 | ==ito≡ pkh (fst x) eq2 | i=i (fst x) = ⊥-elim (make⊥ p1)
sublem pkh pkh' (x ∷ label) v v' p1 p2 | true | false rewrite p1 = p2
sublem pkh pkh' (x ∷ label) v v' p1 p2 | false with pkh == fst x in eq2
sublem pkh pkh' (x ∷ label) v v' p1 p2 | false | true = p2 
sublem pkh pkh' (x ∷ label) v v' p1 p2 | false | false = sublem pkh pkh' label v v' p1 p2 


unjust : ∀ {a b : PubKeyHash} -> Just a ≡ Just b -> a ≡ b
unjust refl = refl

sublem2 : ∀ (pkh : PubKeyHash)  (label : Label) (v v' : Value)
         -> lookup pkh (insert pkh v' label) ≡ Just v -> v' ≡ v
sublem2 pkh [] v v' p rewrite i=i pkh = unjust p 
sublem2 pkh (x ∷ label) v v' p with pkh == (fst x) in eq
...| true rewrite i=i pkh = unjust p
...| false rewrite eq = sublem2 pkh label v v' p


n≤n : ∀ (n : Nat) -> (n <= n) ≡ true
n≤n zero = refl
n≤n (N.suc n) = n≤n n

rwleq : ∀ (a b c : Value) -> a ≡ b -> (c <= a) ≡ true -> (c <= b) ≡ true
rwleq a (pos n) c p1 p2 rewrite p1 = p2 --n≤n n
rwleq a (negsuc n) c p1 p2 rewrite p1 = p2 --n≤n n

lem : ∀ {pkh v} (sig : PubKeyHash) (label : Label) (v' : Value)
      -> geq v' emptyValue ≡ true 
      -> (lookup pkh label ≡ Just v -> geq v emptyValue ≡ true)
      -> (lookup pkh (insert sig v' label) ≡ Just v -> geq v emptyValue ≡ true)
lem {pkh} {v} sig label v' p1 p2 with pkh == sig in eq
...| true rewrite ==ito≡ pkh sig eq = λ x → rwleq v' v 0 (sublem2 sig label v v' x) p1
...| false = λ x → p2 (sublem pkh sig label v v' eq x)

lookDel : ∀ (pkh : PubKeyHash) (label : Label) -> lookup pkh (delete pkh label) ≡ Nothing
lookDel pkh [] = refl
lookDel pkh (x ∷ l) with pkh == (fst x) in eq
...| true = {!!}
...| false = {!!}

delSub : ∀ (pkh sig : PubKeyHash) (label : Label) (v : Value) -> lookup pkh (delete sig label) ≡ Just v
       -> lookup pkh label ≡ Just v
delSub pkh sig label v p = {!!}

delem : ∀ (sig : PubKeyHash) (label : Label)
      -> (∀ {pkh v} -> (lookup pkh label ≡ Just v -> geq v emptyValue ≡ true))
      -> (∀ {pkh v} -> (lookup pkh (delete sig label) ≡ Just v -> geq v emptyValue ≡ true))
delem sig label p1 {pkh} {v} p2 = {!!}
{-with pkh == sig in eq
...| true rewrite ==ito≡ pkh sig eq = {!!}
...| false = {!!}-}

{-with pkh == sig in eq
...| true rewrite ==ito≡ pkh sig eq = ?
--λ x → rwleq v' v 0 (sublem2 sig label v v' x) p1
...| false = ?
--λ x → p2 (sublem pkh sig label v v' eq x)-}

 -}
 {-
delem : ∀ (sig : PubKeyHash) (label : Label)
      -> (∀ {pkh v} -> (lookup pkh label ≡ Just v -> geq v emptyValue ≡ true))
      -> (∀ {pkh v} -> (lookup pkh (delete sig label) ≡ Just v -> geq v emptyValue ≡ true))
delem sig label p1 {pkh} {v} p2 = {!!} -}
{-with pkh == sig in eq
...| true rewrite ==ito≡ pkh sig eq = λ x → rwleq v' v 0 (sublem2 sig label v v' x) p1
...| false  = {!!} -}
-- -> (lookup pkh label ≡ Just v -> geq v emptyValue ≡ true)
-- -> (lookup pkh (insert sig v' label) ≡ Just v -> geq v emptyValue ≡ true)
--(lem pkh (label s) (v + val) (sumLemma v val p3 {!!}) a2)
--(lem from (insert to (vT + val) (label s)) (vF - val) (diffLemma vF val p4 p5) (lem to (label s) (vT + val) (sumLemma vT val p5 (a2 p3)) a2))

{-iv (TPropose p1 p2 p3 p4 p5) rewrite p5 = Col p4 p1 p2 root
validStateTransition {s} (Hol pf) (TAdd p1 p2 p3 p4 p5) = ⊥-elim (diffLabels (label s) pf p3)
validStateTransition (Col pf1 pf2 pf3 pf4) (TAdd p1 p2 p3 p4 p5)
                     rewrite pf1 | sameValue p3 | p5 | sameSigs p3
                     = Col p4 pf2 pf3 (insertPreservesUniqueness pf4)
validStateTransition iv (TPay p1 p2 p3 p4 p5 p6) = Hol p4
validStateTransition iv (TCancel p1 p2 p3 p4) = Hol p3-}


--Multi-Step lemma


{-par s .s s'' [] is' root p2 = p2
lemmaMultiStep par s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)
-}
