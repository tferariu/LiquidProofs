--open import Haskell.Prelude hiding (_×_; _×_×_; _,_; _,_,_)

open import DoubleSatisfaction

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer --hiding (_+_; _-_)
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
open import Haskell.Prim hiding (⊥ ; All)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup)

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)


module DoubleSatisfactionProofs2 where

--open import ListInsertLib (PubKeyHash) (==ito≡) (=/=ito≢)

record Context : Set where
  field
    value         : Value  
    outVal        : Value
    outAdr        : PubKeyHash
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
 --   -> label s' ≡ (insert pkh (v - val) (label s))
    -> value (context s') ≡ value (context s) - val
    -> pkh ≡ outAdr (context s') 
    -> val ≡ outVal (context s') 
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


sumVal : Label -> Integer
sumVal [] = 0
sumVal ((k , v) ∷ xs) =  v + sumVal xs

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


fidelity : ∀ (s s' : State) (i : Input)
         -> value (context s) ≡ sumVal (label s)
         -> s ~[ i ]~> s'
         -> value (context s') ≡ sumVal (label s')
fidelity s s' .(Open _) pf (TOpen p1 p2 p3 p4)
         rewrite pf | p4 | p3 = svLemma1 (label s) p2
fidelity s s' .(Close _) pf (TClose p1 p2 p3 p4)
         rewrite pf | p4 | p3 = svLemma2 (label s) p2
fidelity s s' .(Withdraw _ _) pf (TWithdraw p1 p2 p3 p4 p5 p6 p7)
         rewrite p5 | p6 | pf = {!!} --svLemma3 (label s) p2
fidelity s s' .(Deposit _ _) pf (TDeposit p1 p2 p3 p4 p5)
         rewrite p5 | pf | p4 = svLemma3 (label s) p2
fidelity s s' .(Transfer _ _ _) pf (TTransfer p1 p2 p3 p4 p5 p6 p7 p8)
         rewrite p8 | pf | p7 = svLemma4 (label s) p2 p3 p6



{-
liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) (d : Deadline)
          -> ValidS s -> ValidP par
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value (context s') ≡ 0) )-}



{-
record Context : Set where
  field
    value         : Value  
    outVal        : Value
    outAdr        : PubKeyHash
    tsig          : PubKeyHash
open Context

record State : Set where
  field
    label         : Label
    context       : Context
open State
-}

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
validatorImpliesTransition : ∀ {oV oA sig} (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator l i ctx ≡ true)
                           -> record { label = l ; context = record { value = (inputVal ctx) ;
                              outVal = oV ; outAdr = oA ; tsig = sig } }
                              ~[ i ]~>
                              record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                              outVal = payAmt ctx ; outAdr = payTo ctx ; tsig = signature ctx } }

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
              (geqto≤ (get (geq val +0) (get (checkWithdraw (Just v) pkh val l ctx) (go (pkh == (signature ctx)) pf))))
              (geqto≤ (go (geq val +0) (here (go (pkh == (signature ctx)) pf))))
              ((rewriteSub (inputVal ctx) val (==ito≡ (outputVal ctx) (subInteger (inputVal ctx) val)
              (here (go (checkWithdraw (Just v) pkh val l ctx) (go (pkh == signature ctx) pf))))))
              (==ito≡ pkh (payTo ctx) (here (go (outputVal ctx == subInteger (inputVal ctx) val)
              (go (checkWithdraw (Just v) pkh val l ctx) (go (pkh == signature ctx) pf)))))
              (==ito≡ val (payAmt ctx) (go (pkh == payTo ctx) (go (outputVal ctx == subInteger (inputVal ctx) val)
              (go (checkWithdraw (Just v) pkh val l ctx) (go (pkh == signature ctx) pf))))) 

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




i=i : ∀ (i : Value) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = i=i (pos n)
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = i=i (pos n)

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

transitionImpliesValidator : ∀ {oV oA s} (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : record { label = l ; context = record { value = (inputVal ctx) ;
                              outVal = oV ; outAdr = oA ; tsig = s } }
                              ~[ i ]~>
                              record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                              outVal = payAmt ctx ; outAdr = payTo ctx ; tsig = signature ctx } })
                           -> agdaValidator l i ctx ≡ true
transitionImpliesValidator l (Open pkh) ctx (TOpen p1 p2 p3 p4)
  rewrite p1 | p2 | sym p3 | p4 | i=i (signature ctx) | l=l (outputLabel ctx) | i=i (inputVal ctx) = refl
transitionImpliesValidator l (Close pkh) ctx (TClose p1 p2 p3 p4)
  rewrite p1 | p2 | sym p3 | p4 | i=i (signature ctx) | l=l (outputLabel ctx) | i=i (inputVal ctx) = refl
transitionImpliesValidator l (Withdraw pkh val) ctx (TWithdraw {v = v} p1 p2 p3 p4 p5 p6 p7)
  rewrite p1 | p2 | p7 | i=i (payTo ctx) | i=i (payAmt ctx) | ≤toGeq p3 | ≤toGeq p4 |
  sym (sub≡ (inputVal ctx) (payAmt ctx)) | sym p6 | sym (sub≡ v (payAmt ctx)) | sym p5
  | l=l (outputLabel ctx) | i=i (signature ctx) | i=i (outputVal ctx) = refl
transitionImpliesValidator l (Deposit pkh val) ctx (TDeposit {v = v} p1 p2 p3 p4 p5)
  rewrite p1 | p2 | i=i (signature ctx) | ≤toGeq p3 | sym (add≡ (inputVal ctx) val) | sym p5 |
  i=i (outputVal ctx) | sym (add≡ v val) | sym p4 | l=l (outputLabel ctx) = refl
transitionImpliesValidator l (Transfer from to val) ctx (TTransfer {vF = vF} {vT = vT} p1 p2 p3 p4 p5 p6 p7 p8)
  rewrite sym p1 | p2 | p3 | p8 | i=i from | i=i (inputVal ctx) | ≤toGeq p4 | ≤toGeq p5 |
  ≢to/= from to p6 | sym (add≡ vT val) | sym (sub≡ vF val) | sym p7 | l=l (outputLabel ctx) = refl

--i≡i : ∀ (i : Integer) -> 

infidelity : ∃[ s ] ∃[ i ] ∃[ s' ] ( (value (context s) ≡ sumVal (label s)) × (s ~[ i ]~> s') × (value (context s') ≢ sumVal (label s')))
infidelity = ⟨ (record
                 { label = ((pos zero) , (pos 1000)) ∷ []
                 ; context =
                     record
                     { value = pos 1000
                     ; outVal = pos zero
                     ; outAdr = pos zero
                     ; tsig = pos zero
                     }
                 }) , ⟨ (Withdraw (pos zero) (pos 10)) ,
                 ⟨ (record { label = ((pos zero) , (pos 995)) ∷ []
                   ; context =  record
                     { value = pos 990
                     ; outVal = pos 10
                     ; outAdr = pos zero
                     ; tsig = pos zero
                     } }) , (refl , TWithdraw refl refl (+≤+ N.z≤n) (+≤+ (N.s≤s (N.s≤s (N.s≤s (N.s≤s
                     (N.s≤s (N.s≤s (N.s≤s (N.s≤s (N.s≤s (N.s≤s N.z≤n)))))))))))
                     refl refl refl , λ ())⟩ ⟩ ⟩
