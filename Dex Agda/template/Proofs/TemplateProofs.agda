open import Validators.Template
open import Lib
open import Value

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer.Base --hiding (_+_; _-_)
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

open import Haskell.Prim hiding (⊥) -- ; All)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup ; _<>_)


open import ProofLib

module Proofs.TemplateProofs where



record State : Set where
  field
    datum      : Label
    value      : Value  
    payVal     : Value
    tsig       : PubKeyHash
    continues  : Bool
    spends     : TxOutRef
    hasToken   : Bool
    mint       : Integer
    token      : AssetClass
  --other      : Components  
open State

record MParams : Set where
    field
        optional : Placeholder
open MParams public

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s}
    -------------------
    -> par ⊢ s



data _⊢_~[_]~>_ : MParams -> State -> Input -> State -> Set where
 
  TTransition : ∀ {par s i s'}
    -------------------
    -> par ⊢ s ~[ i ]~> s'



data _⊢_~[_]~|_ : MParams -> State -> Input -> State -> Set where

  TClose : ∀ {s s' par i}
    -------------------
    -> par ⊢ s ~[ i ]~| s'
    


Valid : State -> Set 
Valid s = {!!}


--Multi-Step Transition
data _⊢_~[_]~*_ : MParams -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''

  fin : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~| s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


--State Validity Invariant
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> Valid s
validStateInitial = {!!}

validStateTransition : ∀ {s s' : State} {i par}
  -> Valid s
  -> par ⊢ s ~[ i ]~> s'
  -> Valid s'
validStateTransition = {!!}


liquidity : ∀ (par : MParams) (s : State) 
          -> Valid s
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value s' ≡ MkMap []) )

liquidity = {!!}



getS : Label -> ScriptContext -> State
getS (tok , lab) ctx = {!!}

getMintS : ScriptContext -> State
getMintS ctx = {!!}

getS' : Label -> ScriptContext -> State
getS' (tok , lab) ctx = {!!}


getPar : Params -> Address -> TxOutRef -> MParams
getPar par adr oref = {!!}


--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {adr oref} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> getPar par adr oref  ⊢ getS d ctx ~[ i ]~> getS' d ctx
validatorImpliesTransition = {!!}



mintingImpliesStart : ∀ {par tn} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≢ -1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> getPar par adr oref ⊢ getMintS ctx
mintingImpliesStart = {!!}


bothImplyClose : ∀ {tn} {closeInput : Input} (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> (agdaValidator par d closeInput ctx && agdaPolicy adr oref tn top ctx) ≡ true
               -> getPar par adr oref ⊢ getS d ctx ~[ closeInput ]~| getS' d ctx
bothImplyClose = {!!}


transitionImpliesValidator : ∀ {adr oref} (par : Params) (d : Label) (i : Input) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getS d ctx ~[ i ]~> getS' d ctx
                           -> agdaValidator par d i ctx ≡ true
transitionImpliesValidator = {!!}

startImpliesMinting : ∀ {par tn} (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
                           -> getPar par adr oref ⊢ getMintS ctx
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting = {!!}
  
closeImpliesBoth : ∀ {tn} {closeInput : Input} (par : Params) (d : Label) (adr : Address) (oref : TxOutRef) (top : ⊤) (ctx : ScriptContext)
               -> getPar par adr oref ⊢ getS d ctx ~[ closeInput ]~| getS' d ctx
               -> ((agdaValidator par d closeInput ctx && agdaPolicy adr oref tn top ctx) ≡ true)
closeImpliesBoth = {!!}

data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase

record Argument : Set where
  field
    par  : Params
    adr  : Address
    oref : TxOutRef
    dat  : Label
    inp  : Input
    ctx  : ScriptContext 
open Argument



record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

Classifier : Argument -> Phase
Classifier = {!!}



totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial  = agdaPolicy (arg .adr) (arg .oref) 0 tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) 
... | Terminal = agdaValidator (arg .par) (arg .dat) (arg .inp) (arg .ctx) &&
                 agdaPolicy (arg .adr) (arg .oref) 0 tt (arg .ctx)


totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial  = getPar (arg .par) (arg .adr) (arg .oref) ⊢ getMintS (arg .ctx)
... | Running  = getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~> getS' (arg .dat) (arg .ctx) 
... | Terminal =  getPar (arg .par) (arg .adr) (arg .oref) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .inp) ]~| getS' (arg .dat) (arg .ctx)



totalEquiv : totalF ≈ totalR
totalEquiv = {!!}
