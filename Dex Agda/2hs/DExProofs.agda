open import DEx

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

record State : Set where
  field
    label         : Label
    context       : Context
    continues     : Bool
open State

data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {amt r s s' par} 
    -> owner (label s) ≡ tsig (context s') 
    -> value (context s') ≡ amt
    -> label s' ≡ record { ratio = r ; owner = owner (label s) }
    -> checkRational r ≡ True
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'

  TExchange : ∀ {amt pkh s s' par} 
    -> value (context s) ≡ value (context s') + amt
    -> label s' ≡ label s
    -> payTo (context s') ≡ owner (label s)
    -> amt * num (ratio (label s)) ≤ payAmt (context s') * den (ratio (label s))
    -> buyTo (context s') ≡ pkh 
    -> buyAmt (context s') ≡ amt
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

  TClose : ∀ {s s' par} 
    -> owner (label s) ≡ tsig (context s')
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


validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x


liquidity : ∀ (par : Params) (s : State) --(pkh : PubKeyHash) 
          -> ValidS s -> continues s ≡ True
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value (context s') ≡ 0) )

liquidity par s (Stp x) p2 rewrite p2 = ⊥-elim (get⊥ x)
liquidity par s (Oth x) p2 = ⟨ s' , ⟨  Close ∷ [] , (cons (TClose refl p2 refl) root , refl) ⟩ ⟩
  where
    s' = record { label = record { ratio = ratio (label s) ; owner = owner (label s) } ;
                  context = record
                             { value = 0
                             ; payAmt = value (context s)
                             ; payTo = owner (label s)
                             ; buyAmt = 0
                             ; buyTo = 0
                             ; tsig = owner (label s)
                             } ;
                  continues = False }



{-
liquidity' : ∀ (par : Params) (s : State) (pkh : PubKeyHash) 
          -> ValidS s -> continues s ≡ True
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (value (context s') ≡ 0) )

liquidity' par s pkh (Stp x) p2 rewrite p2 = ⊥-elim (get⊥ x)
liquidity' par s@record { label = record { ratio = ratio ; owner = owner } ;
             context = record { value = value ; payAmt = payAmt ; payTo = payTo ; buyAmt = buyAmt ; buyTo = buyTo ; tsig = tsig } ;
             continues = continues } pkh (Oth x) p2
  = ⟨ s' , ⟨  (Exchange value pkh) ∷ [] , (cons (TExchange (sym (+-identityˡ value)) refl refl {!!} refl refl p2 refl) root , refl) ⟩ ⟩
--⟨ {!!} , ⟨ {!(Exchange) ∷ []!} , ({!!} , {!!}) ⟩ ⟩
--⟨ s' , ⟨  Close ∷ [] , (cons (TClose refl p2 refl) root , refl) ⟩ ⟩
  where
    s' = record { label = record { ratio = ratio ; owner = owner } ;
                  context = record
                             { value = 0
                             ; payAmt = value * num ratio -- den ratio
                             ; payTo = owner
                             ; buyAmt = value
                             ; buyTo = pkh
                             ; tsig = owner
                             } ;
                  continues = True } -}


--get : ∀ (a : Bool) {b} -> (a && b) ≡ true -> a ≡ true
--get true pf = refl

go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

--skip : ∀ {a b : Bool} -> (a && b) ≡ true -> b ≡ true
--skip {true} {true} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl

==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p)

==ito≡ : ∀ {a b : Integer} -> (a == b) ≡ true -> a ≡ b
==ito≡ {(pos n)} {(pos m)} pf = cong pos (==to≡ pf)
==ito≡ {(negsuc n)} {(negsuc m)} pf = cong negsuc (sym (==to≡ pf)) 

==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ {record { num = num ; den = den }} {record { num = num' ; den = den' }} pf
  rewrite ==ito≡ {num} {num'} (get pf) | ==ito≡ {den} {den'} (go (eqInteger num num') pf) = refl

unNot : ∀ {b : Bool} -> not b ≡ true -> b ≡ false
unNot {false} pf = refl

==lto≡ : ∀ (ctx : ScriptContext) (l : Label)
         -> ((ratio (outputLabel ctx) == (ratio l)) && (owner (outputLabel ctx) == owner l)) ≡ True
         -> outputLabel ctx ≡ l --record {ratio = r ; owner = owner l}
==lto≡ record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = record { ratio = ratio ; owner = owner } ; payTo = payTo ; payAmt = payAmt ; buyTo = buyTo ; buyAmt = buyAmt ; signature = signature ; continues = continues } record { ratio = ratio' ; owner = owner' } pf
  rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ {owner} {owner'} (go (ratio == ratio') pf)= refl

==lto≡' : ∀ (ctx : ScriptContext) (l : Label) {r}
          -> ((ratio (outputLabel ctx) == r) && (owner (outputLabel ctx) == owner l)) ≡ True
          -> outputLabel ctx ≡ record {ratio = r ; owner = owner l}
==lto≡' ctx@(record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = record { ratio = ratio ; owner = owner } ; payTo = payTo ; payAmt = payAmt ; buyTo = buyTo ; buyAmt = buyAmt ; signature = signature ; continues = continues }) l {r} pf rewrite ==rto≡ {ratio} {r} (get pf) | ==to≡ {owner} {Label.owner l} (go (ratio == r) pf) = refl

{-
(eqInteger (num (ratio (outputLabel ctx))) (num r) &&
         eqInteger (den (ratio (outputLabel ctx))) (den r))
        && eqNat (owner (outputLabel ctx)) (owner l)
-}

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


mul≡ : ∀ (a b : Integer) -> mulInteger a b ≡ a * b
mul≡ (pos zero) (pos zero) = refl
mul≡ +[1+ n ] (pos zero) = mul≡ (pos n) (pos zero)
mul≡ (pos zero) +[1+ m ] = refl
mul≡ +[1+ n ] +[1+ m ] = refl
mul≡ (pos zero) (negsuc zero) = refl
mul≡ +[1+ n ] (negsuc zero) = refl
mul≡ (pos zero) (negsuc (N.suc m)) = refl
mul≡ +[1+ n ] (negsuc (N.suc m)) = refl
mul≡ (negsuc zero) (pos zero) = refl
mul≡ (negsuc (N.suc n)) (pos zero) = mul≡ (negsuc n) (pos zero)
mul≡ (negsuc zero) +[1+ m ] = refl
mul≡ (negsuc (N.suc n)) +[1+ m ] = refl
mul≡ (negsuc zero) (negsuc zero) = refl
mul≡ (negsuc (N.suc n)) (negsuc zero) = refl
mul≡ (negsuc zero) (negsuc (N.suc m)) = refl
mul≡ (negsuc (N.suc n)) (negsuc (N.suc m)) = refl

rewriteAdd : ∀ {a} (b c : Value) -> a ≡ addInteger b c -> a ≡ b + c
rewriteAdd b c p rewrite add≡ b c = p

<=to≤ : ∀ {a b} -> (a N.<ᵇ b || a == b) ≡ true -> a N.≤ b
<=to≤ {zero} {zero} pf = N.z≤n
<=to≤ {zero} {suc b} pf = N.z≤n
<=to≤ {suc a} {suc b} pf = N.s≤s (<=to≤ pf)

{-
≤to<= : ∀ {a b} -> a N.≤ b -> (a N.<ᵇ b || a == b) ≡ true
≤to<= {b = zero} N.z≤n = refl
≤to<= {b = suc b} N.z≤n = refl
≤to<= (N.s≤s pf) = ≤to<= pf
-}

≤≡lem : ∀ (a b : Nat) -> ltNat a (N.suc b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡lem zero zero pf = refl
≤≡lem zero (N.suc b) pf = refl
≤≡lem (N.suc a) (N.suc b) pf = ≤≡lem a b pf

≤≡ : ∀ (a b : Nat) -> (a N.≤ᵇ b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡ zero zero pf = refl
≤≡ zero (N.suc b) pf = refl
≤≡ (N.suc a) (N.suc b) pf = ≤≡lem a b pf



--≤≡ {a} {b} {!!}
{-
<=ito≤ : ∀ {a b : Integer} -> (a ≤ᵇ b) ≡ true -> a ≤ b
<=ito≤ {pos n} {pos m} pf = +≤+ (<=to≤ (≤≡ n m pf))
<=ito≤ {negsuc n} {pos m} pf = -≤+
<=ito≤ {negsuc n} {negsuc m} pf = -≤- (<=to≤ (≤≡ m n pf))
-}

<=ito≤ : ∀ {a b : Integer} -> (ltInteger a b || eqInteger a b) ≡ true -> a ≤ b
<=ito≤ {pos n} {pos m} pf = +≤+ (<=to≤ pf)
<=ito≤ {negsuc n} {pos m} pf = -≤+
<=ito≤ {negsuc n} {negsuc m} pf = -≤- (<=to≤ pf)

{--}
rewriteMulCheck : ∀ (r : Rational) (ctx : ScriptContext) (val) ->
  ((mulInteger val (num r)) <= (mulInteger (payAmt ctx) (den r))) ≡ True ->
  (((sign val Sign.* sign (num r)) ◃ mulNat ∣ val ∣ ∣ num r ∣) ≤
  ((sign (payAmt ctx) Sign.* sign (den r)) ◃ mulNat ∣ payAmt ctx ∣ ∣ den r ∣))
rewriteMulCheck r ctx val p rewrite mul≡ val (num r) | mul≡ (payAmt ctx) (den r) = <=ito≤ p 


--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {pA pT bA bT s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payAmt = pA ; payTo = pT ; buyAmt = bA ; buyTo = bT ; tsig = s } ; continues = True }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                           payAmt = payAmt ctx ; payTo = payTo ctx ;
                           buyAmt = buyAmt ctx ; buyTo = buyTo ctx ; tsig = signature ctx } ;
                           continues = continuing ctx}

validatorImpliesTransition par l (Update val r) ctx pf
  = TUpdate (==to≡ (get pf)) (==ito≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
    (==lto≡' ctx l (get (go (outputVal ctx == val) (go (checkRational r) (go ((owner l) == (signature ctx)) pf)))))
    (get (go ((owner l) == (signature ctx)) pf)) refl
    (go (outputLabel ctx == record { ratio = r ; owner = owner l})
    (go (outputVal ctx == val) (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l (Exchange val pkh) ctx pf
  rewrite add≡ (outputVal ctx) val -- | mul≡ val (num (ratio l)) | mul≡ (payAmt ctx) (den (ratio l))
  = TExchange (==ito≡ (get pf)) (==lto≡ ctx l (get (go (inputVal ctx == outputVal ctx + val) pf)))
  (==to≡ (get (get (go (outputLabel ctx == l) (go (inputVal ctx == outputVal ctx + val) pf)))))
  (rewriteMulCheck (ratio l) ctx val ((go (payTo ctx == owner l) (get
  (go (outputLabel ctx == l) (go (inputVal ctx == outputVal ctx + val) pf))))))
  --(==ito≡ (go (payTo ctx == owner l) (get (go (outputLabel ctx == l) (go (inputVal ctx == outputVal ctx + val) {!!})))))
  (==to≡ (get (get (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf))))))
  (==ito≡ (go (buyTo ctx == pkh) (get (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf)))))) refl
  (go (checkBuyer par val pkh ctx) (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf))))
validatorImpliesTransition par l Close ctx pf
  = TClose (==to≡ (go (not (continues ctx)) pf)) refl (unNot (get pf))


{-
validatorImpliesTransition : ∀ {pA pT bA bT s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payAmt = pA ; payTo = pT ; buyAmt = bA ; buyTo = bT ; tsig = s } ; continues = True }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                           payAmt = payAmt ctx ; payTo = payTo ctx ;
                           buyAmt = buyAmt ctx ; buyTo = buyTo ctx ; tsig = signature ctx } ;
                           continues = continuing ctx}
-}


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
i=i (pos (suc n)) = i=i (pos n)
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = i=i (pos n)

≡to==l : ∀ {a b : Label} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl

≤to<= : ∀ {a b : Nat} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤to<= {b = zero} N.z≤n = refl
≤to<= {b = N.suc b} N.z≤n = refl
≤to<= (N.s≤s p) = ≤to<= p

≤ito<= : ∀ {a b : Integer} -> a ≤ b -> (ltInteger a b || eqInteger a b) ≡ true
≤ito<= (-≤- n≤m) = ≤to<= n≤m
≤ito<= -≤+ = refl
≤ito<= (+≤+ m≤n) = ≤to<= m≤n


transitionImpliesValidator : ∀ {pA pT bA bT s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payAmt = pA ; payTo = pT ; buyAmt = bA ; buyTo = bT ; tsig = s } ; continues = True }
                           ~[ i ]~>
                           record { label = (outputLabel ctx) ; context = record { value = (outputVal ctx) ;
                           payAmt = payAmt ctx ; payTo = payTo ctx ;
                           buyAmt = buyAmt ctx ; buyTo = buyTo ctx ; tsig = signature ctx } ;
                           continues = continuing ctx})
                           -> agdaValidator par l i ctx ≡ true
transitionImpliesValidator par l (Update val r) ctx (TUpdate p1 p2 p3 p4 p5 p6)
  rewrite ≡to== p1 | p4 | ≡to==i p2 | ≡to==l p3 = p6
transitionImpliesValidator par l (Exchange val pkh) ctx (TExchange p1 p2 p3 p4 p5 p6 p7 p8)
  rewrite add≡ (outputVal ctx) val | ≡to==i p1 | ≡to==l p2 | ≡to== p3 | mul≡ val (num (ratio l))
  | mul≡ (payAmt ctx) (den (ratio l)) | ≡to== p5 | ≡to==i p6 | ≤ito<= p4 = p8
transitionImpliesValidator par l Close ctx (TClose p1 p2 p3) rewrite p3 = ≡to== p1


--(go (checkRational r) (go ((owner l) == (signature ctx)) (get {!p!})))
--(==ito≡ (go (checkRational r) (go ((owner l) == (signature ctx)) {!!})))
{-
        inputVal    : Value
        outputVal   : Value
        outputLabel : Label
        payTo       : PubKeyHash
        payAmt      : Value
        buyTo       : PubKeyHash
        buyAmt      : Value
        signature   : PubKeyHash
        continues   : Bool -}


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
open import Data.Sign.Base -- as Sign


open import Haskell.Prim hiding (⊥ ; All; Any)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat) -}


--open import Data.Nat.Properties
--open import Data.List.Relation.Unary.Any hiding (lookup)
--open import Data.List.Relation.Unary.All as All hiding (lookup)
--open import Data.Product
--open import Haskell.Prim
