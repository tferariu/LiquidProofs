open import DEx

{-
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Data.Nat as N
open import Data.Nat.Properties
open import Data.Integer
open import Data.Integer.Properties
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Agda.Builtin.Int
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
open import Data.Product

open import Haskell.Prim hiding (⊥ ; All; Any)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat) -}

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



module DExProofs where


record Context : Set where
  field
    value         : Value  
    payAmt        : Value
    payTo         : PubKeyHash
    buyAmt        : Value
    buyTo         : PubKeyHash
    tsig          : PubKeyHash
open Context

--raname to somtething appropriate

record State : Set where
  field
    label         : Label
    context       : Context
    continues     : Bool
open State

data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {amt r s s' par} 
    -> tsig (context s') ≡ owner (label s)
    -> value (context s') ≡ amt
    -> label s' ≡ record { ratio = r ; owner = owner (label s) }
    -> checkRational r ≡ True
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'

  TExchange : ∀ {amt pkh s s' par} 
    -> value (context s') ≡ value (context s') + amt
    -> label s' ≡ label s
    -> payTo (context s') ≡ owner (label s)
    -> payAmt (context s') * num (ratio (label s)) ≡ amt * den (ratio (label s)) 
    -> buyTo (context s') ≡ pkh 
    -> buyAmt (context s') ≡ amt
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

  TClose : ∀ {s s' par} 
    -> tsig (context s') ≡ owner (label s)
    -> continues s ≡ True
    -> continues s' ≡ False
    -------------------
    -> par ⊢ s ~[ Close ]~> s'


--Valid State
data ValidS : State -> Set where

  Stp : ∀ {s}
    -> continues s ≡ False
    ----------------
    -> ValidS s

  Oth : ∀ {s}
    -> checkRational (ratio (label s)) ≡ True
    ----------------
    -> ValidS s


--Multi-Step Transition
data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


get⊥ : true ≡ false -> ⊥
get⊥ ()

--State Validity Invariant
validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition iv (TUpdate p1 p2 p3 p4 p5 p6)
  = Oth (subst (λ x -> checkRational (ratio x) ≡ True) (sym p3) p4)
validStateTransition (Stp x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8) rewrite x = ⊥-elim (get⊥ (sym p7))
validStateTransition (Oth x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8) rewrite sym p2 = Oth x
validStateTransition iv (TClose p1 p2 p3) = Stp p3
