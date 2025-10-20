open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer.Base
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
import Data.Sign.Base as Sign

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
open import Haskell.Prelude using (lookup ; _<>_)

open import Lib

module ProofLib where


get⊥ : true ≡ false -> ⊥
get⊥ ()

go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl


==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p)

==ito≡ : ∀ {a b : Integer} -> (a == b) ≡ true -> a ≡ b
==ito≡ {(pos n)} {(pos m)} pf = cong +_ (==to≡ pf) --cong pos (==to≡ pf)
==ito≡ {(negsuc n)} {(negsuc m)} pf = cong negsuc (==to≡ pf) 

==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ {record { num = num ; den = den }} {record { num = num' ; den = den' }} pf
  rewrite ==ito≡ {num} {num'} (get pf) | ==ito≡ {den} {den'} (go (eqInteger num num') pf) = refl

unNot : ∀ {b : Bool} -> not b ≡ true -> b ≡ false
unNot {false} pf = refl

==pto≡ : {a b : (AssetClass × Integer)} -> (a == b) ≡ true -> a ≡ b
==pto≡ {ac , amt} {ac' , amt'} pf rewrite (==to≡ {ac} {ac'} (get pf)) | (==ito≡ {amt} {amt'} (go (ac == ac') pf)) = refl

==v'to≡ : {m m' : List (AssetClass × Integer)} -> (m == m') ≡ true -> m ≡ m'
==v'to≡ {[]} {[]} p = refl
==v'to≡ {x ∷ m} {y ∷ m'} pf rewrite (==pto≡ {x} {y} (get pf))= cong (λ z → y ∷ z) (==v'to≡ (go (x == y) pf))

==vto≡ : {a b : Value} -> (a == b) ≡ true -> a ≡ b
==vto≡ {MkMap x} {MkMap y} p = cong MkMap (==v'to≡ p)

t=f : ∀ (a : Bool) -> not a ≡ true -> a ≡ true -> true ≡ false
t=f false p1 p2 = sym p2
t=f true p1 p2 = sym p1

≡to== : ∀ {a b : Nat} -> a ≡ b -> (a == b) ≡ true
≡to== {zero} refl = refl
≡to== {suc a} refl = ≡to== {a} refl

n=n : ∀ (n : Nat) -> (n == n) ≡ true
n=n zero = refl
n=n (suc n) = n=n n

≡to==i : ∀ {a b : Integer} -> a ≡ b -> (a == b) ≡ true
≡to==i {pos n} refl = n=n n
≡to==i {negsuc n} refl = n=n n

i=i : ∀ (i : Int) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = n=n n 
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = n=n n

lst=lst : ∀ (lst : List (Nat × Integer)) -> (lst == lst) ≡ true
lst=lst [] = refl
lst=lst (x ∷ lst) rewrite n=n (x .fst) | i=i (x .snd) = lst=lst lst

v=v : ∀ (v : Value) -> (v == v) ≡ true
v=v (MkMap x) = lst=lst x

