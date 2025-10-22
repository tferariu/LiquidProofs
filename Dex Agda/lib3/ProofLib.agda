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

module ProofLib where



sub : ∀ {a b c : ℤ} -> a ≡ b -> a ≡ c -> b ≡ c
sub refl refl = refl

maybe⊥ : ∀ {x : Integer} -> Nothing ≡ Just x -> ⊥
maybe⊥ ()

maybe≡ : ∀ {a b : Integer} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl


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



switchSides : ∀ {a b c : Integer} -> a - b ≡ c -> a ≡ b + c
switchSides {a} {b} refl rewrite +-comm a (- b) | sym (+-assoc b (- b) a)
                         | +-inverseʳ b | +-identityˡ a = refl

switchSides' : ∀ {a b c : Integer} -> a + b ≡ c -> a ≡ - b + c
switchSides' {a} {b} refl rewrite +-comm a b | sym (+-assoc (- b) b a)
                         | +-inverseˡ b | +-identityˡ a = refl

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

unNot : (b : Bool) -> not b ≡ true -> b ≡ false
unNot false pf = refl

get⊥ : true ≡ false -> ⊥
get⊥ ()

n≠n : ∀ (n : Nat) -> eqNat n n ≡ false -> ⊥
n≠n n p rewrite n=n n = get⊥ p

/=to≢ : ∀ (a b : Nat) -> (a /= b) ≡ true -> a ≢ b
/=to≢ zero (N.suc b) pf = λ ()
/=to≢ (N.suc a) zero pf = λ ()
/=to≢ (N.suc a) (N.suc b) pf = λ { refl → n≠n a (unNot (eqNat a a) pf)}

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
≤to≤ᵇ {+_ n} {+_ m} (+≤+ m≤n) rewrite swapEqNat n m = ≤Nto≤ᵇN m≤n
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

{-

get⊥ : ∀ (n : Nat) -> not (eqNat n n) ≡ true -> ⊥
get⊥ (N.suc n) p = get⊥ n p

==to≡ : ∀ (a b : Nat) -> (a == b) ≡ true -> a ≡ b
==to≡ zero zero p = refl
==to≡ (Nat.suc a) (Nat.suc b) p = cong Nat.suc (==to≡ a b p)

==ito≡ : ∀ (a b : Integer) -> (a == b) ≡ true -> a ≡ b
==ito≡ (pos n) (pos m) pf = cong (+_) (==to≡ n m pf)
==ito≡ (negsuc n) (negsuc m) pf = cong negsuc (==to≡ n m pf)



n=n : ∀ (n : Nat) -> eqNat n n ≡ true
n=n zero = refl
n=n (N.suc n) = n=n n

i=i : ∀ (i : Value) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = n=n n 
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = n=n n





{-
=/=ito≢ : ∀ {a b : Int} -> (a == b) ≡ false -> a ≢ b
=/=ito≢ {pos n} {pos .n} pf refl rewrite n=n n = get⊥ pf
=/=ito≢ {negsuc n} {negsuc .n} pf refl rewrite n=n n = get⊥ pf
-}

-}
