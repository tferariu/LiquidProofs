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
    -> tsig (context s) ≡ owner (label s)
    -> value (context s) ≡ amt
    -> label s' ≡ record { ratio = r ; owner = owner (label s) }
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'

  TExchange : ∀ {amt pkh s s' par} 
    -> value (context s) ≡ value (context s') + amt
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
    -> tsig (context s) ≡ owner (label s)
    -> continues s ≡ True
    -> continues s' ≡ False
    -------------------
    -> par ⊢ s ~[ Close ]~> s'

{-
  TAdd : ∀ {sig par s s' v pkh d sigs} 
    -> sig ∈ (authSigs par)
    -> tsig (context s') ≡ sig
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Collecting v pkh d (insert sig sigs)
    -> value (context s) ≡ value (context s')
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'

  TPay : ∀ {v pkh d sigs s s' par} 
    -> tsig (context s') ≡ pkh
    -> value (context s) ≡ value (context s') + v
    -> length sigs ≥ nr par
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding
    -> outVal (context s') ≡ v
    -> outAdr (context s') ≡ pkh 
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'

  TCancel : ∀ {s s' par v pkh d sigs} 
    -> now (context s') > d
    -> label s ≡ Collecting v pkh d sigs
    -> label s' ≡ Holding  
    -> value (context s) ≡ value (context s') 
    -> continues s ≡ True
    -> continues s' ≡ True 
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'

  TClose : ∀ {par s s'}
    -> label s ≡ Holding
    -> minValue > value (context s)
    -> continues s ≡ True
    -> continues s' ≡ False
    -------------------
    -> par ⊢ s ~[ Close ]~> s'

-}
