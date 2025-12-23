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

open import Lib

module ProofLib where

--Various lemmas about the agda2hs Haskell prelude and relating it to the standard library

sub : ∀ {a b c : ℤ} -> a ≡ b -> a ≡ c -> b ≡ c
sub refl refl = refl

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

addComm : ∀ (a b : Integer) -> addInteger a b ≡ addInteger b a
addComm a b rewrite add≡ a b | add≡ b a = +-comm a b

addIdL : ∀ (a : Integer) -> addInteger 0 a ≡ a
addIdL a rewrite add≡ 0 a = +-identityˡ a

addIdR : ∀ (a : Integer) -> addInteger a 0 ≡ a
addIdR a rewrite add≡ a 0 = +-identityʳ a

sub≡ : ∀ (a b : Integer) -> subInteger a b ≡ a - b
sub≡ (+_ n) (+_ m) rewrite ni≡ (+ m) = add≡ (+ n) (- (+ m))
sub≡ (+_ n) (negsuc m) = refl
sub≡ (negsuc n) (+_ m) rewrite ni≡ (+ m) = add≡ (negsuc n) (- (+ m))
sub≡ (negsuc n) (negsuc m) = subN≡ (N.suc m) (N.suc n)

==to≡ : ∀ (a b : Nat) -> (a == b) ≡ true -> a ≡ b
==to≡ zero zero p = refl
==to≡ (Nat.suc a) (Nat.suc b) p = cong Nat.suc (==to≡ a b p)

==ito≡ : ∀ (a b : Integer) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong (+_) (==to≡ n m pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (==to≡ n m pf)

doubleMinus : ∀ (a b : Integer) -> a - - b ≡ a + b
doubleMinus a b rewrite neg-involutive b = refl

n=n : ∀ (n : Nat) -> eqNat n n ≡ true
n=n zero = refl
n=n (N.suc n) = n=n n

i=i : ∀ (i : Integer) -> (eqInteger i i) ≡ true
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

n≤n : ∀ (n : Nat) -> n N.≤ n
n≤n zero = N.z≤n
n≤n (N.suc n) = N.s≤s (n≤n n)

ltLem : ∀ (n : Nat) -> ltNat n n ≡ false
ltLem zero = refl
ltLem (N.suc n) = ltLem n

monusLem : ∀ (n : Nat) -> monusNat n n ≡ 0
monusLem zero = refl
monusLem (N.suc n) = monusLem n

minusLemma : ∀ (a b c : Integer) -> a ≡ b + c -> a - c ≡ b
minusLemma .(b + + n) b (pos n) refl rewrite +-assoc b (+ n) (- (+ n))
           | [+m]-[+n]≡m⊖n n n | n⊖n≡0 n | +-identityʳ b = refl
minusLemma .(b + negsuc n) b (negsuc n) refl rewrite +-assoc b (negsuc n) (- (negsuc n))
           | n⊖n≡0 (N.suc n) | +-identityʳ b = refl

refactor : ∀ (a b c : Integer) -> a ≡ b + c -> c ≡ a - b
refactor a b c p rewrite +-comm b c = sym (minusLemma a c b p)

unNot : {b : Bool} -> not b ≡ true -> b ≡ false
unNot {false} pf = refl

get⊥ : true ≡ false -> ⊥
get⊥ ()

n≠n : ∀ (n : Nat) -> eqNat n n ≡ false -> ⊥
n≠n n p rewrite n=n n = get⊥ p

/=to≢ : ∀ (a b : Nat) -> (a /= b) ≡ true -> a ≢ b
/=to≢ zero (N.suc b) pf = λ ()
/=to≢ (N.suc a) zero pf = λ ()
/=to≢ (N.suc a) (N.suc b) pf = λ { refl → n≠n a (unNot pf)}

&&false : ∀ (a : Bool) -> (a && false) ≡ true -> ⊥
&&false true ()

&&5false : ∀ (a b c d e : Bool) -> (a && b && c && d && e && false) ≡ true -> ⊥
&&5false true true true true true ()

&&4false : ∀ (a b c d : Bool) -> (a && b && c && d && false) ≡ true -> ⊥
&&4false true true true true ()

&&2false : ∀ (a b : Bool) -> (a && b && false) ≡ true -> ⊥
&&2false true true ()

rewriteJust : ∀ {a : Maybe ℤ} {v v'} -> a ≡ Just v -> v ≡ v' -> a ≡ Just v'
rewriteJust refl refl = refl

≤NtoLeqN : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤NtoLeqN {b = zero} N.z≤n = refl
≤NtoLeqN {b = N.suc b} N.z≤n = refl
≤NtoLeqN (N.s≤s p) = ≤NtoLeqN p

≤NtoLeqN' : ∀ {a b} -> a N.≤ b -> (ltNat a b || eqNat b a) ≡ true
≤NtoLeqN' {b = zero} N.z≤n = refl
≤NtoLeqN' {b = N.suc b} N.z≤n = refl
≤NtoLeqN' (N.s≤s p) = ≤NtoLeqN' p

≢to/= : ∀ (a b : Nat) -> a ≢ b -> (a /= b) ≡ true
≢to/= zero zero pf = ⊥-elim (pf refl)
≢to/= zero (N.suc b) pf = refl
≢to/= (N.suc a) zero pf = refl
≢to/= (N.suc a) (N.suc b) pf with eqNat a b in eq
...| False = refl
...| True rewrite ==to≡ a b eq = ⊥-elim (pf refl)

swapEqNat : ∀ (n m : Nat) -> eqNat n m ≡ eqNat m n
swapEqNat zero zero = refl
swapEqNat zero (suc m) = refl
swapEqNat (suc n) zero = refl
swapEqNat (suc n) (suc m) = swapEqNat n m

≤ᵇNto≤N : ∀ {a b} -> (ltNat a b || eqNat a b) ≡ true -> a N.≤ b
≤ᵇNto≤N {zero} {zero} pf = N.z≤n
≤ᵇNto≤N {zero} {N.suc b} pf = N.z≤n
≤ᵇNto≤N {N.suc a} {N.suc b} pf = N.s≤s (≤ᵇNto≤N pf)

≤ᵇNto≤N' : ∀ {a b} -> (ltNat a b || eqNat b a) ≡ true -> a N.≤ b
≤ᵇNto≤N' {zero} {zero} pf = N.z≤n
≤ᵇNto≤N' {zero} {N.suc b} pf = N.z≤n
≤ᵇNto≤N' {N.suc a} {N.suc b} pf = N.s≤s (≤ᵇNto≤N' pf)

≤ᵇto≤ : ∀ {a b} -> (ltInteger a b || eqInteger a b) ≡ true -> a ≤ b
≤ᵇto≤ {+_ a} {+_ b} pf = +≤+ (≤ᵇNto≤N pf)
≤ᵇto≤ {negsuc n} {+_ n₁} pf = -≤+
≤ᵇto≤ {negsuc a} {negsuc b} pf rewrite swapEqNat a b = -≤- (≤ᵇNto≤N pf)

≤ᵇto≤' : ∀ {a b} -> (ltInteger a b || eqInteger b a) ≡ true -> a ≤ b
≤ᵇto≤' {+_ a} {+_ b} pf rewrite swapEqNat b a = +≤+ (≤ᵇNto≤N pf)
≤ᵇto≤' {negsuc n} {+_ n₁} pf = -≤+
≤ᵇto≤' {negsuc a} {negsuc b} pf = -≤- (≤ᵇNto≤N pf)

≤Nto>N : ∀ {a b} -> (ltNat a b || eqNat a b) ≡ false -> N.suc b N.≤ a
≤Nto>N {N.suc a} {zero} p = N.s≤s N.z≤n
≤Nto>N {N.suc a} {N.suc b} p = N.s≤s (≤Nto>N p)

≤to> : ∀ {a b} -> (ltInteger a b || eqInteger a b) ≡ false -> a Data.Integer.> b
≤to> {+_ a} {+_ b} pf = +<+ (≤Nto>N pf)
≤to> {+_ a} {negsuc b} pf = -<+
≤to> {negsuc a} {negsuc b} pf rewrite swapEqNat a b  = -<- (≤Nto>N pf)

<ᵇNto<N : ∀ {a b : Nat} -> (a N.<ᵇ b) ≡ true -> a N.< b
<ᵇNto<N {zero} {suc b} pf = N.s≤s N.z≤n
<ᵇNto<N {suc a} {suc b} pf = N.s≤s (<ᵇNto<N pf)

<ᵇto< : ∀ {a b : Integer} -> (ltInteger a b) ≡ true -> a Data.Integer.< b
<ᵇto< {+_ n} {+_ n₁} p = +<+ (<ᵇNto<N p)
<ᵇto< {negsuc n} {+_ n₁} p = -<+
<ᵇto< {negsuc n} {negsuc n₁} p = -<- (<ᵇNto<N p)

≡ˡto≡ : ∀ {a b : List Nat} -> (a == b) ≡ true -> a ≡ b
≡ˡto≡ {[]} {[]} pf = refl
≡ˡto≡ {(x ∷ a)} {(y ∷ b)} pf rewrite (==to≡ x y (get pf)) = cong (λ x -> y ∷ x) (≡ˡto≡ (go (x == y) pf))

==lto≡ : ∀ (a b : List Nat) -> (a == b) ≡ true -> a ≡ b
==lto≡ [] [] pf = refl
==lto≡ (x ∷ a) (y ∷ b) pf rewrite (==to≡ x y (get pf)) = cong (λ x -> y ∷ x) (==lto≡ a b (go (x == y) pf))

orToSum : ∀ (a b : Bool) -> (a || b) ≡ true -> a ≡ true ⊎ b ≡ true
orToSum false true pf = inj₂ refl
orToSum true b pf = inj₁ refl

≡to≡ᵇ : ∀ {a b} -> a ≡ b -> (a N.≡ᵇ b) ≡ true
≡to≡ᵇ {zero} refl = refl
≡to≡ᵇ {suc a} refl = ≡to≡ᵇ {a} refl

≤Nto≤ᵇN : ∀ {a b} -> a N.≤ b -> (a N.<ᵇ b || b N.≡ᵇ a) ≡ true
≤Nto≤ᵇN {b = zero} N.z≤n = refl
≤Nto≤ᵇN {b = N.suc b} N.z≤n = refl
≤Nto≤ᵇN (N.s≤s p) = ≤Nto≤ᵇN p

≤to≤ᵇ : ∀ {a b : Integer} -> a ≤ b -> (ltInteger a b || eqInteger b a) ≡ true
≤to≤ᵇ {+_ n} {+_ m} (+≤+ m≤n) = ≤Nto≤ᵇN m≤n
≤to≤ᵇ {+_ n} {negsuc m} ()
≤to≤ᵇ {negsuc n} {+_ m} -≤+ = refl
≤to≤ᵇ {negsuc n} {negsuc m} (-≤- n≤m) rewrite swapEqNat m n = ≤Nto≤ᵇN n≤m


<Nto<ᵇN : ∀ {a b} -> a N.< b -> (a N.<ᵇ b) ≡ true
<Nto<ᵇN {zero} (N.s≤s p) = refl
<Nto<ᵇN {N.suc a} (N.s≤s p) = <Nto<ᵇN p

<to<ᵇ : ∀ {a b : Integer} -> a Data.Integer.< b -> (ltInteger a b) ≡ true
<to<ᵇ {+_ n} {+_ n₁} (+<+ m<n) = <Nto<ᵇN m<n
<to<ᵇ {+_ n} {negsuc n₁} ()
<to<ᵇ {negsuc n} {+_ n₁} -<+ = refl
<to<ᵇ {negsuc n} {negsuc n₁} (-<- n<m) = <Nto<ᵇN n<m

||true : ∀ {b} -> (b || true) ≡ true
||true {false} = refl
||true {true} = refl

t=f : ∀ (a : Bool) -> not a ≡ true -> a ≡ true -> true ≡ false
t=f false p1 p2 = sym p2
t=f true p1 p2 = sym p1

≡to== : ∀ {a b : Nat} -> a ≡ b -> (a == b) ≡ true
≡to== {zero} refl = refl
≡to== {suc a} refl = ≡to== {a} refl

≡to==i : ∀ {a b : Integer} -> a ≡ b -> (a == b) ≡ true
≡to==i {pos n} refl = n=n n
≡to==i {negsuc n} refl = n=n n

==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ r1@{record { num = num₁ ; den = den₁ }} r2@{record { num = num₂ ; den = den₂ }} pf
  rewrite ==ito≡ (numerator r1) (numerator r2) (get pf)
  | ==ito≡ (denominator r1) (denominator r2) (go (eqInteger (numerator r1) (numerator r2)) pf) = refl

lst=lst : ∀ (lst : List (Nat × Integer)) -> (lst == lst) ≡ true
lst=lst [] = refl
lst=lst (x ∷ lst) rewrite n=n (x .fst) | i=i (x .snd) = lst=lst lst

==tto≡ : ∀ (a b : AssetClass) -> (a == b) ≡ true -> a ≡ b
==tto≡ (cs , tn) (cs' , tn') p rewrite ==to≡ cs cs' (get p) | ==to≡ tn tn' (go (cs == cs') p) = refl

t=t : ∀ (t : AssetClass) -> (t == t) ≡ true
t=t (cs , tn) rewrite n=n cs | n=n tn = refl

ltNatFalseToGeq : ∀ (a b : Nat) -> ltNat a b ≡ false -> (ltNat b a || eqNat a b) ≡ true
ltNatFalseToGeq zero zero pf = refl
ltNatFalseToGeq (N.suc a) zero pf = refl
ltNatFalseToGeq (N.suc a) (N.suc b) pf = ltNatFalseToGeq a b pf

ltNatFalseToGeq' : ∀ (a b : Nat) -> ltNat a b ≡ false -> (ltNat b a || eqNat b a) ≡ true
ltNatFalseToGeq' zero zero pf = refl
ltNatFalseToGeq' (N.suc a) zero pf = refl
ltNatFalseToGeq' (N.suc a) (N.suc b) pf = ltNatFalseToGeq' a b pf

ltIntFalseToGeq : ∀ (a b : Integer) -> ltInteger a b ≡ false -> (ltInteger b a || eqInteger a b) ≡ true
ltIntFalseToGeq (+_ a) (+_ b) pf = ltNatFalseToGeq a b pf
ltIntFalseToGeq (+_ a) (negsuc b) pf = refl
ltIntFalseToGeq (negsuc a) (negsuc b) pf = ltNatFalseToGeq' b a pf

geqNatTrans : ∀ (a b c : Nat) -> (a Haskell.Prelude.>= b) ≡ true -> (b Haskell.Prelude.>= c) ≡ true -> (a Haskell.Prelude.>= c) ≡ true
geqNatTrans zero zero zero p1 p2 = p1
geqNatTrans (N.suc a) zero zero p1 p2 = p1
geqNatTrans (N.suc a) (N.suc b) zero p1 p2 = p2
geqNatTrans (N.suc a) (N.suc b) (N.suc c) p1 p2 = geqNatTrans a b c p1 p2

geqNatTrans' : ∀ (a b c : Nat) -> (ltNat a b || eqNat a b) ≡ true -> (ltNat b c || eqNat b c) ≡ true -> (ltNat a c || eqNat a c) ≡ true
geqNatTrans' zero zero zero p1 p2 = p1
geqNatTrans' zero zero (N.suc c) p1 p2 = p1
geqNatTrans' zero (N.suc b) (N.suc c) p1 p2 = p1
geqNatTrans' (N.suc a) (N.suc b) (N.suc c) p1 p2 = geqNatTrans' a b c p1 p2

geqIntegerTrans : ∀ (a b c : Integer) -> (a Haskell.Prelude.>= b) ≡ true -> (b Haskell.Prelude.>= c) ≡ true -> (a Haskell.Prelude.>= c) ≡ true
geqIntegerTrans (+_ zero) (+_ zero) (+_ zero) p1 p2 = p1
geqIntegerTrans +[1+ a ] (+_ zero) (+_ zero) p1 p2 = p1
geqIntegerTrans +[1+ a ] +[1+ b ] (+_ zero) p1 p2 = p2
geqIntegerTrans +[1+ a ] +[1+ b ] +[1+ c ] p1 p2 = geqNatTrans a b c p1 p2 
geqIntegerTrans (+_ zero) (+_ zero) (negsuc zero) p1 p2 = p1
geqIntegerTrans (+_ zero) (+_ zero) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans +[1+ a ] (+_ zero) (negsuc zero) p1 p2 = p1
geqIntegerTrans +[1+ a ] (+_ zero) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans +[1+ a ] +[1+ b ] (negsuc zero) p1 p2 = p2
geqIntegerTrans +[1+ a ] +[1+ b ] (negsuc (N.suc c)) p1 p2 = p2
geqIntegerTrans (+_ zero) (negsuc zero) (negsuc zero) p1 p2 = p1
geqIntegerTrans (+_ zero) (negsuc zero) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans (+_ zero) (negsuc (N.suc b)) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans +[1+ a ] (negsuc zero) (negsuc zero) p1 p2 = p1
geqIntegerTrans +[1+ a ] (negsuc zero) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans +[1+ a ] (negsuc (N.suc b)) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans (negsuc zero) (negsuc zero) (negsuc zero) p1 p2 = p1
geqIntegerTrans (negsuc zero) (negsuc zero) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans (negsuc zero) (negsuc (N.suc b)) (negsuc (N.suc c)) p1 p2 = p1
geqIntegerTrans (negsuc (N.suc a)) (negsuc (N.suc b)) (negsuc (N.suc c)) p1 p2 = geqNatTrans' a b c p1 p2

beforeLemma : ∀ (a : Integer) -> ltInteger (+ 0) a ≡ true
  -> ltInteger (addInteger (+ 0) (negateInteger a)) a ≡ true
beforeLemma +[1+ n ] pf = pf

addNatIdR : ∀ (a : Nat) -> addNat a 0 ≡ a
addNatIdR zero = refl
addNatIdR (N.suc a) = cong N.suc (addNatIdR a)

addNatComm : ∀ (a b : Nat) -> addNat a b ≡ addNat b a
addNatComm zero zero = refl
addNatComm zero (N.suc b) rewrite addNatIdR b = refl
addNatComm (N.suc a) zero rewrite addNatIdR a = refl
addNatComm (N.suc a) (N.suc b)
  rewrite addNatComm a (N.suc b) | addNatComm b (N.suc a) = cong N.suc (cong N.suc (addNatComm b a))

ltNatLemma : ∀ (a : Nat) -> ltNat a (N.suc a) ≡ true
ltNatLemma zero = refl
ltNatLemma (N.suc a) = ltNatLemma a

ltIntegerLemma : ∀ (a : Integer) -> ltInteger a (addInteger a (+ 1)) ≡ true
ltIntegerLemma (+_ zero) = refl
ltIntegerLemma +[1+ n ] rewrite addNatComm n 1 = ltNatLemma n
ltIntegerLemma (negsuc zero) = refl
ltIntegerLemma (negsuc (N.suc n)) = ltNatLemma n

lengthNatToLength : ∀ (n : Nat) (l : List Nat) -> (n N.<ᵇ lengthNat l || lengthNat l N.≡ᵇ n) ≡ true -> n N.≤ length l
lengthNatToLength zero [] pf = N.z≤n
lengthNatToLength zero (x ∷ l) pf = N.z≤n
lengthNatToLength (suc n) (x ∷ l) pf = N.s≤s (lengthNatToLength n l pf)

lengthToLengthNat : ∀ (n : Nat) (l : List Nat) -> n N.≤ length l -> (n N.<ᵇ lengthNat l || lengthNat l N.≡ᵇ n) ≡ true
lengthToLengthNat zero [] N.z≤n = refl
lengthToLengthNat zero (x ∷ l) N.z≤n = refl
lengthToLengthNat (N.suc n) [] ()
lengthToLengthNat (N.suc n) (x ∷ l) (N.s≤s p) = lengthToLengthNat n l p
