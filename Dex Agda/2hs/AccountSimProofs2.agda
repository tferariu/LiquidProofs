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


module AccountSimProofs2 where

--open import ListInsertLib (PubKeyHash) (==ito≡) (=/=ito≢)

sumVal : Label -> Integer
sumVal [] = 0
sumVal ((k , v) ∷ xs) =  v + sumVal xs


record Context : Set where
  field
    valueIn       : Value
    valueOut      : Value
    tsig          : PubKeyHash
open Context

record State : Set where
  field
    label         : Label
open State

--Transition Rules
data _⊢_~[_]~>_ : Context -> State -> Input -> State -> Set where
 
  TOpen : ∀ {ctx pkh s s'}
    -> pkh ≡ tsig ctx
    -> lookup pkh (label s) ≡ Nothing
    -> label s' ≡ insert pkh 0 (label s)
    -> valueOut ctx ≡ valueIn ctx
    -------------------
    -> ctx ⊢ s ~[ (Open pkh) ]~> s'

  TClose : ∀ {ctx pkh s s'}
    -> pkh ≡ tsig ctx
    -> lookup pkh (label s) ≡ Just 0
    -> label s' ≡ delete pkh (label s)
    -> valueOut ctx ≡ valueIn ctx  
    -------------------
    -> ctx ⊢ s ~[ (Close pkh) ]~> s'

  TWithdraw : ∀ {ctx pkh val s s' v}
    -> pkh ≡ tsig ctx
    -> lookup pkh (label s) ≡ Just v
    -> val ≥ emptyValue
    -> v ≥ val
    -> label s' ≡ (insert pkh (v - val) (label s))
    -> valueOut ctx ≡ valueIn ctx - val
    -------------------
    -> ctx ⊢ s ~[ (Withdraw pkh val) ]~> s'
    
  TDeposit : ∀ {ctx pkh val s s' v}
    -> pkh ≡ tsig ctx
    -> lookup pkh (label s) ≡ Just v
    -> val ≥ emptyValue
    -> label s' ≡ (insert pkh (v + val) (label s))
    -> valueOut ctx ≡ valueIn ctx + val
    -------------------
    -> ctx ⊢ s ~[ (Deposit pkh val) ]~> s'

    
  TTransfer : ∀ {ctx from to val s s' vF vT}
    -> from ≡ tsig ctx
    -> lookup from (label s) ≡ Just vF
    -> lookup to (label s) ≡ Just vT
    -> vF ≥ val
    -> val ≥ emptyValue
    -> from ≢ to
    -> label s' ≡ (insert from (vF - val) (insert to (vT + val) (label s)))
    -> valueOut ctx ≡ valueIn ctx
    -------------------
    -> ctx ⊢ s ~[ (Transfer from to val) ]~> s'

--Multi-Step Transition
data _⊢_~[_]~*_ : List Context -> State -> List Input -> State -> Set where

  root : ∀ { s }
    -- -> valueOut ctx ≡ valueIn ctx
    ------------------
    -> [] ⊢ s ~[ [] ]~* s

  cons : ∀ { ctx ctxs s s' s'' i is }
    -> ctx ⊢ s ~[ i ]~> s'
    -> ctxs ⊢ s' ~[ is ]~* s''
    -------------------------
    -> (ctx ∷ ctxs) ⊢ s ~[ (i ∷ is) ]~* s''


_∈_ : ∀ (x : PubKeyHash) (xs : Label ) → Set
x ∈ xs = Any (\y -> x ≡ fst y) xs

_∉_ : ∀ (x : PubKeyHash) (xs : Label) → Set
x ∉ xs = ¬ (x ∈ xs)


data Unique : Label → Set where
  root : Unique []
  _::_ : {x : PubKeyHash} {v : Value} {l : Label} -> x ∉ l -> Unique l -> Unique ((x , v) ∷ l)



data Valid : State -> Set where

  Always : ∀ {s}
    ---> value (context s) ≡ sumVal (label s)
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


fidelity : ∀ {s s' : State} {i : Input} {ctx : Context}
         -> valueIn ctx ≡ sumVal (label s)
         -> ctx ⊢ s ~[ i ]~> s'
         -> valueOut ctx ≡ sumVal (label s')
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



{-
data NonEmpty : ∀ {a} List a -> Set where

   Asdf : ∀ {ctx ctxs}
    ----------------
    -> NonEmpty (ctx ∷ ctxs) -}



firstCtx : ( a : List Context ) -> NonEmpty a -> Context
firstCtx (x ∷ a) p = x


lastCtx : ( a : List Context ) -> NonEmpty a -> Context
lastCtx (x ∷ []) p = x
lastCtx (x ∷ y ∷ a) p = lastCtx (y ∷ a) itsNonEmpty


fidelityMulti : ∀ {s s' : State} {is : List Input} {ctxs : List Context}
  -> (pf : NonEmpty ctxs)
  -> valueIn (firstCtx ctxs pf) ≡ sumVal (label s)
  -> ctxs ⊢ s ~[ is ]~* s'
  -> valueOut (lastCtx ctxs pf) ≡ sumVal (label s')
fidelityMulti {s} {s'} {i ∷ .[]} {ctx ∷ []} p1 p2 (cons {ctx} {.[]} {i = i} {.[]} x root) = fidelity p2 x
fidelityMulti {s} {s'} {.(Open _) ∷ .(Open _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = .(Open _)} {.(Open _ ∷ is)} (TOpen x x₅ x₆ x₇) (cons p@(TOpen x₁ x₂ x₃ x₄) p3)) = fidelityMulti itsNonEmpty {!!} (cons p p3)
fidelityMulti {s} {s'} {.(Close _) ∷ .(Open _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = .(Close _)} {.(Open _ ∷ is)} (TClose x x₅ x₆ x₇) (cons p@(TOpen x₁ x₂ x₃ x₄) p3)) = fidelityMulti itsNonEmpty {!!} (cons p p3)
fidelityMulti {s} {s'} {.(Withdraw _ _) ∷ .(Open _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = .(Withdraw _ _)} {.(Open _ ∷ is)} (TWithdraw x x₅ x₆ x₇ x₈ x₉) (cons p@(TOpen x₁ x₂ x₃ x₄) p3)) = fidelityMulti itsNonEmpty {!!} (cons p p3)
fidelityMulti {s} {s'} {.(Deposit _ _) ∷ .(Open _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = .(Deposit _ _)} {.(Open _ ∷ is)} (TDeposit x x₅ x₆ x₇ x₈) (cons p@(TOpen x₁ x₂ x₃ x₄) p3)) = fidelityMulti itsNonEmpty {!!} (cons p p3)
fidelityMulti {s} {s'} {.(Transfer _ _ _) ∷ .(Open _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = .(Transfer _ _ _)} {.(Open _ ∷ is)} (TTransfer x x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) (cons p@(TOpen x₁ x₂ x₃ x₄) p3)) = fidelityMulti itsNonEmpty {!!} (cons p p3)
fidelityMulti {s} {s'} {i ∷ .(Close _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = i} {.(Close _ ∷ is)} x (cons p@(TClose x₁ x₂ x₃ x₄) p3))
  = {!!}
fidelityMulti {s} {s'} {i ∷ .(Withdraw _ _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = i} {.(Withdraw _ _ ∷ is)} x (cons p@(TWithdraw x₁ x₂ x₃ x₄ x₅ x₆) p3))
  = {!!}
fidelityMulti {s} {s'} {i ∷ .(Deposit _ _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = i} {.(Deposit _ _ ∷ is)} x (cons p@(TDeposit x₁ x₂ x₃ x₄ x₅) p3))
  = {!!}
fidelityMulti {s} {s'} {i ∷ .(Transfer _ _ _) ∷ is} {ctx ∷ ctx' ∷ ctxs} p1 p2 (cons {ctx} {.(ctx' ∷ ctxs)} {i = i} {.(Transfer _ _ _ ∷ is)} x (cons p@(TTransfer x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) p3))
  = {!!}

--fidelityMulti itsNonEmpty {!!} (cons p p3)

--fidelityMulti itsNonEmpty {!!} p3


{-
fidelityMulti p1 (root x) rewrite x = p1
fidelityMulti {s} {s'} {i ∷ is} {ctx} p1 (cons {is = is} x p2) = fidelityMulti {!!} p2 -}

--fidelityMulti (fidelity p1 {!x!}) p2
{-
fidelityMulti {s} {s} {[]} p1 ? = {!!} --fidelity p1 {!root!} --p1
fidelityMulti {s} {s'} {(i ∷ is)} p1 (cons {s' = s''} x p2) = fidelityMulti (fidelity p1 x) {!!} --p2 -}
{-

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



makeIs : Label -> List Input
makeIs [] = []
makeIs ((a , b) ∷ l) = (Withdraw a b) ∷ (Close a) ∷ (makeIs l)

makeL : Label -> Label
makeL [] = []
makeL ((a , b) ∷ l) = (a , emptyValue) ∷ (makeL l)



lastSig : State -> PubKeyHash
lastSig record { label = [] ; context = record { value = value ; tsig = tsig } } = tsig
lastSig record { label = (x ∷ []) ; context = record { value = value ; tsig = tsig } } = fst x
lastSig record { label = (x ∷ y ∷ label) ; context = ctx }
  = lastSig (record { label = y ∷ label ; context = ctx })


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



liquidity : ∀ (s : State)
          -> value (context s) ≡ sumVal (label s)
          -> Valid s
          -> ∃[ s' ] ∃[ is ] ((s ~[ is ]~* s') × (value (context s') ≡ 0) )

liquidity s p1 p2 =
  ⟨ record { label = [] ; context = record { value = 0 ; tsig = lastSig s } } ,
  ⟨ makeIs (label s) , (prop1 s (record { label = [] ; context = record { value = 0 ; tsig = lastSig s } }) {label s}
  refl refl refl refl p1 p2 , refl) ⟩ ⟩

-}
