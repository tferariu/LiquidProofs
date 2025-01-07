open import DExpanded2

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


module DExpandedProofs2 where

{-
record TxOut : Set where
  field
    txOutAddress : Address
    txOutValue : Value
    txOutDatum : OutputDatum

record ScriptContext : Set where
    field
        txOutputs   : List TxOut
        inputVal    : Value
        signature   : PubKeyHash
        purpose     : ScriptPurpose
        
record ScriptContext : Set where
    field
        inputVal    : Value
        outputVal   : Value
        outputLabel : Label
        payTo       : PubKeyHash
        payAmt      : Value
        buyTo       : PubKeyHash
        buyAmt      : Value
        signature   : PubKeyHash
        continues   : Bool
open ScriptContext public -}

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
 
  TUpdate : ∀ {amt r s s' par lab}
    -> label s ≡ lab
    -> owner lab ≡ tsig (context s') 
    -> value (context s') ≡ amt
    -> label s' ≡ (record { ratio = r ; owner = owner lab })
    -> checkRational r ≡ True
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'

  TExchange : ∀ {amt pkh s s' par aux lab}
  
    -> value (context s) ≡ (value (context s')) + amt
    -> label s' ≡ label s
    -> label s ≡ lab
    -> payTo (context s') ≡ (owner lab)
    -> payAmt (context s') ≡ aux
    -> amt * num (ratio lab) ≤ aux * den (ratio lab)
    -> buyTo (context s') ≡ pkh 
    -> buyAmt (context s') ≡ amt
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

  TClose : ∀ {s s' par lab}
    -> label s ≡ lab
    -> owner lab ≡ tsig (context s')
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

  Oth : ∀ {s lab}
    -> label s ≡ lab
    -> checkRational (ratio lab) ≡ True
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
validStateTransition {record { label = .( (record { ratio = ratio₁ ; owner = tsig context })) ; context = context₁ ; continues = .true }} {record { label = .( (record { ratio = _ ; owner = tsig context })) ; context = context ; continues = .true }} iv (TUpdate {lab = record { ratio = ratio₁ ; owner = .(tsig context) }} refl refl refl refl p5 refl refl) = Oth refl p5
validStateTransition (Stp x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite x = ⊥-elim (get⊥ (sym p9))
validStateTransition (Oth x y) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) rewrite sym p2 = Oth x y
validStateTransition iv (TClose p1 p2 p3 p4) = Stp p4


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
liquidity par record { label = lab ; context = context ; continues = continues } (Oth refl y) p2 = ⟨ s' , ⟨  Close ∷ [] , (cons (TClose refl refl p2 refl ) root , refl) ⟩ ⟩
  where
    s' = record { label = (record { ratio = ratio lab ; owner = owner lab }) ;
                  context = record
                             { value = 0
                             ; payAmt = (value (context))
                             ; payTo = (owner lab)
                             ; buyAmt = 0
                             ; buyTo = 0
                             ; tsig = owner lab
                             } ;
                  continues = False } 



go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

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

==lto≡ : ∀ (l l' : Label)
       -> (l == l') ≡ True
       -> l ≡ l' 
==lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ {owner} {owner'} (go (ratio == ratio') pf) = refl

{-record { inputVal = inputVal ; outputVal = outputVal ; outputLabel = record { ratio = ratio ; owner = owner } ; payTo = payTo ; payAmt = payAmt ; buyTo = buyTo ; buyAmt = buyAmt ; signature = signature ; continues = continues } record { ratio = ratio' ; owner = owner' } pf
  rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ {owner} {owner'} (go (ratio == ratio') pf) = refl-}


neg≡ : ∀ (a : Integer) -> negateInteger a ≡ - a
neg≡ (pos zero) = refl
neg≡ +[1+ n ] = refl
neg≡ (negsuc zero) = refl
neg≡ (negsuc (N.suc n)) = refl

add≡ : ∀ (a b : Integer) -> addInteger a b ≡ a + b
add≡ (pos zero) (pos zero) = refl
add≡ (pos zero) +[1+ m ] = refl
add≡ +[1+ n ] (pos zero) = refl
add≡ +[1+ n ] +[1+ m ] = refl
add≡ (pos zero) (negsuc zero) = refl
add≡ (pos zero) (negsuc (N.suc m)) = refl
add≡ +[1+ n ] (negsuc zero) = refl
add≡ +[1+ n ] (negsuc (N.suc m)) with ltNat n (N.suc m)
...| True = neg≡ (pos (monusNat (N.suc m) n))
...| False = refl 
add≡ (negsuc zero) (pos zero) = refl
add≡ (negsuc zero) +[1+ m ] = refl
add≡ (negsuc (N.suc n)) (pos zero) = refl
add≡ (negsuc (N.suc n)) +[1+ m ] with ltNat m (N.suc n)
...| True = neg≡ (pos (monusNat (N.suc n) m))
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

≤≡lem : ∀ (a b : Nat) -> ltNat a (N.suc b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡lem zero zero pf = refl
≤≡lem zero (N.suc b) pf = refl
≤≡lem (N.suc a) (N.suc b) pf = ≤≡lem a b pf

≤≡ : ∀ (a b : Nat) -> (a N.≤ᵇ b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡ zero zero pf = refl
≤≡ zero (N.suc b) pf = refl
≤≡ (N.suc a) (N.suc b) pf = ≤≡lem a b pf


<=ito≤ : ∀ {a b : Integer} -> (ltInteger a b || eqInteger a b) ≡ true -> a ≤ b
<=ito≤ {pos n} {pos m} pf = +≤+ (<=to≤ pf)
<=ito≤ {negsuc n} {pos m} pf = -≤+
<=ito≤ {negsuc n} {negsuc m} pf = -≤- (<=to≤ pf)


{-
rewriteMulCheck : ∀ (r : Rational) (ctx : ScriptContext) (val) ->
  ((mulInteger val (num r)) <= (mulInteger (payAmt ctx) (den r))) ≡ True ->
  (((sign val Sign.* sign (num r)) ◃ mulNat ∣ val ∣ ∣ num r ∣) ≤
  ((sign (payAmt ctx) Sign.* sign (den r)) ◃ mulNat ∣ payAmt ctx ∣ ∣ den r ∣))
rewriteMulCheck r ctx val p rewrite mul≡ val (num r) | mul≡ (payAmt ctx) (den r) = <=ito≤ p 
-}

{-
getPayOutAmt : Label -> Input -> ScriptContext -> Maybe Value
getPayOutAmt l (Update r amt) ctx = Nothing
getPayOutAmt l (Exchange amt pkh) ctx = case getPaymentOutput (owner l) ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutValue x)
getPayOutAmt l Close ctx = case getPaymentOutput (owner l) ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutValue x)

getPayOutAdr : Label -> Input -> ScriptContext -> Maybe Address
getPayOutAdr l (Update r amt) ctx = Nothing
getPayOutAdr l (Exchange amt pkh) ctx = case getPaymentOutput (owner l) ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutAddress x)
getPayOutAdr l Close ctx = case getPaymentOutput (owner l) ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutAddress x)

getBuyOutAmt : Label -> Input -> ScriptContext -> Maybe Value
getBuyOutAmt l (Update r amt) ctx = Nothing
getBuyOutAmt l (Exchange amt pkh) ctx = case getPaymentOutput pkh ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutValue x)
getBuyOutAmt l Close ctx = Nothing

getBuyOutAdr : Label -> Input -> ScriptContext -> Maybe Address
getBuyOutAdr l (Update r amt) ctx = Nothing
getBuyOutAdr l (Exchange amt pkh) ctx = case getPaymentOutput pkh ctx of λ where
  Nothing -> Nothing
  (Just x) -> Just (txOutAddress x)
getBuyOutAdr l Close ctx = Nothing
-}

getPayOutAmt : Label -> ScriptContext -> Value
getPayOutAmt l ctx = (txOutValue (getPaymentOutput (owner l) ctx))

getPayOutAdr : Label -> ScriptContext -> Address
getPayOutAdr l ctx = (txOutAddress (getPaymentOutput (owner l) ctx))

getBuyOutAmt : Label -> Input -> ScriptContext -> Value
getBuyOutAmt l (Update r amt) ctx = -1
getBuyOutAmt l (Exchange amt pkh) ctx = (txOutValue (getPaymentOutput pkh ctx))
getBuyOutAmt l Close ctx = -1

getBuyOutAdr : Label -> Input -> ScriptContext -> Address
getBuyOutAdr l (Update r amt) ctx = 0
getBuyOutAdr l (Exchange amt pkh) ctx = (txOutAddress (getPaymentOutput pkh ctx))
getBuyOutAdr l Close ctx = 0


{-
==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p) -}

==mvto≡ : ∀ {a b : Maybe Value} -> (a == b) ≡ true -> a ≡ b
==mvto≡ {Nothing} {Nothing} p = refl
==mvto≡ {Just a} {Just b} p rewrite ==ito≡ {a} {b} p = refl

==mlto≡ : ∀ {a b : Maybe Label} -> (a == b) ≡ true -> a ≡ b
==mlto≡ {Nothing} {Nothing} p = refl
==mlto≡ {Just a} {Just b} p rewrite ==lto≡ a b p = refl

unJust : ∀ {a b : Value} -> a ≡ b -> Just a ≡ Just b
unJust refl = refl

isJust : ∀ {a : Set} -> Maybe a -> Bool
isJust Nothing = False
isJust (Just x) = True

{-
aaaa : ∀ {par val l ctx} -> checkPayment par val l ctx ≡ True -> True ≡ isJust (getPaymentOutput (owner l) ctx)
aaaa {l = l} {ctx = ctx} p = {!!}
with getPaymentOutput (owner l) ctx
...| Nothing = ?
...| Just tx = {!!}
-}


{-
aux2 : (x w : Maybe ℤ) →
    x ≡ w → {a b : ℤ}
    (pf : not ((case w of λ { Nothing → false ; (Just v) → true })) ≡ true) →
    a ≡ b
aux2 x w p pf = {!!}-}


bingus : ∀ {par l amt pkh ctx}
         -> (pf : checkPayment par amt l pkh ctx ≡ true)
         -> txOutAddress (getPaymentOutput (owner l) ctx) ≡ owner l
bingus {par} {l} {amt} {pkh} {ctx} pf = ==to≡ (go (ratioCompare amt (txOutValue (getPaymentOutput (owner l) ctx)) (ratio l)) pf)

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {pA pT bA bT s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payAmt = pA ; payTo = pT ; buyAmt = bA ; buyTo = bT ; tsig = s } ; continues = True }
                           ~[ i ]~>
                           record { label = newLabel ctx ; context = record { value = newValue ctx ;
                           payAmt = getPayOutAmt l ctx ; payTo = getPayOutAdr l ctx ;
                           buyAmt = getBuyOutAmt l i ctx ; buyTo = getBuyOutAdr l i ctx ;
                           tsig = signature ctx } ; continues = continuing ctx}
validatorImpliesTransition par l (Update val r) ctx pf
  = TUpdate refl (==to≡ (get pf)) (==ito≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
  ((==lto≡ (newLabel ctx) (record { ratio = r ; owner = owner l }) (get (go (newValue ctx == val)
  (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))))
  (get (go ((owner l) == (signature ctx)) pf)) refl (go (newLabel ctx == (record {ratio = r ; owner = owner l}))
    (go (newValue ctx == val) (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l (Exchange val pkh) ctx pf -- with getPaymentOutput (owner l) ctx 
  = TExchange (rewriteAdd (newValue ctx)  val (==ito≡ (get pf)))
    (==lto≡ (newLabel ctx) l (get (go (oldValue ctx == addInteger (newValue ctx) val) pf))) refl
    {!get!} refl {!!} {!!} {!!} refl {!!}
validatorImpliesTransition par l Close ctx pf = TClose refl (==to≡ (go (not (continuing ctx)) pf)) refl (unNot (get pf))

{--}



--TClose (==to≡ (go (not (continues ctx)) pf)) refl (unNot (get pf))
{-
validatorImpliesTransition par l (Update val r) ctx pf
  = TUpdate (==to≡ (get pf)) (==ito≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
    (==lto≡ ctx (record { ratio = r ; owner = owner l }) (get (go (outputVal ctx == val)
    (go (checkRational r) (go ((owner l) == (signature ctx)) pf)))))
    (get (go ((owner l) == (signature ctx)) pf)) refl
    (go (outputLabel ctx == record { ratio = r ; owner = owner l})
    (go (outputVal ctx == val) (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l (Exchange val pkh) ctx pf rewrite add≡ (outputVal ctx) val 
  = TExchange (==ito≡ (get pf)) (==lto≡ ctx l (get (go (inputVal ctx == outputVal ctx + val) pf)))
  (==to≡ (get (get (go (outputLabel ctx == l) (go (inputVal ctx == outputVal ctx + val) pf)))))
  (rewriteMulCheck (ratio l) ctx val ((go (payTo ctx == owner l) (get
  (go (outputLabel ctx == l) (go (inputVal ctx == outputVal ctx + val) pf))))))
  (==to≡ (get (get (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf))))))
  (==ito≡ (go (buyTo ctx == pkh) (get (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf)))))) refl
  (go (checkBuyer par val pkh ctx) (go (checkPayment par val l ctx) (go (outputLabel ctx == l)
  (go (inputVal ctx == outputVal ctx + val) pf))))
validatorImpliesTransition par l Close ctx pf
  = TClose (==to≡ (go (not (continues ctx)) pf)) refl (unNot (get pf))


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

-}
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



---------------------------------------------
{-
==mto≡ : ∀ {a : Set} {{eq a}} {x y : Maybe a} -> (x == y) ≡ true -> x ≡ y
==mto≡ p = {!!}-}

{-
==mlto≡ {Just record { ratio = ratio ; owner = owner }} {Just record { ratio = ratio' ; owner = owner' }} p
  rewrite ==rto≡ {ratio} {ratio'} (get p) | ==to≡ {owner} {owner'} (go (ratio == ratio') p) = {!!}-}
{-
bbbb : ∀ {ctx tx} -> continuing ctx ≡ true -> getContinuingOutput (purpose ctx) (txOutputs ctx) ≡ Just tx
bbbb {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = txOutDatum } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} p = {!refl!}
bbbb {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = txOutDatum } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} p = {!!}
bbbb {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = txOutDatum } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} p = {!!}

aaaa : ∀ {par val l ctx tx} -> checkPayment par val l ctx ≡ True -> getPaymentOutput (owner l) (purpose ctx) (txOutputs ctx) ≡ Just tx
aaaa {ctx = record { txOutputs = record { txOutAddress = txOutAddress ; txOutValue = txOutValue ; txOutDatum = Payment x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} p = {!!}
aaaa {par} {val} {l} {record { txOutputs = record { txOutAddress = txOutAddress ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {tx} p = aaaa {par} {val} {l} {record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {tx} p
aaaa {ctx = record { txOutputs = txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Minting x }} ()

asdf : ∀ {par val l ctx pkh} -> checkPayment par val l ctx ≡ True -> getPayOutAdr l (Exchange val pkh) ctx ≡ Just (owner l)
asdf {par} {val} {record { ratio = ratio ; owner = owner }} {record { txOutputs = record { txOutAddress = txOutAddress ; txOutValue = txOutValue ; txOutDatum = Payment x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {pkh} p = {!!}
{-with eqNat y x
...| True = ?
...| False = {!!}-}
asdf {par} {val} l@{record { ratio = ratio ; owner = owner }} {record { txOutputs = record { txOutAddress = txOutAddress ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {pkh} p = asdf {par} {val} {l} {record { txOutputs =  txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {pkh} p
asdf {par} {val} {record { ratio = ratio ; owner = owner }} {record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = Minting x }} {pkh} ()
asdf {par} {val} {record { ratio = ratio ; owner = owner }} {record { txOutputs = x₁ ∷ txOutputs₁ ; inputVal = inputVal ; signature = signature ; purpose = Minting x }} {pkh} ()

{-with getPaymentOutput (owner l) ctx
...| Nothing = ?
...| Just tx = {!!} -}

bingle : ∀ (a b : Nat) -> (eqNat a b && False) ≡ False
bingle zero zero = refl
bingle zero (N.suc b) = refl
bingle (N.suc a) zero = refl
bingle (N.suc a) (N.suc b) = bingle a b

bingle2 : ∀ (b : Bool) -> (b && False) ≡ False
bingle2 false = refl
bingle2 true = refl

asdd : ∀ {l val pkh ctx aux} -> getPayOutAdr l (Exchange val pkh) ctx ≡ Just aux -> aux ≡ pkh
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {.0} refl = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending zero }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment zero } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Payment (N.suc x) } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending (N.suc y) }} {aux} p = {!!}
asdd {record { ratio = ratio ; owner = owner }} {val} {pkh} {record { txOutputs = record { txOutAddress = txOutAddress ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} p = {!!}
{-with eqNat owner txOutAddress
...| True = ?
...| False = {!!} -}
asdd {l} {val} {pkh} {record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = Minting x }} {aux} ()
asdd {l} {val} {pkh} {record { txOutputs = x₁ ∷ txOutputs₁ ; inputVal = inputVal ; signature = signature ; purpose = Minting x }} {aux} ()

{-
asdd l@{record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} p = asdd {l} {val} {pkh} {record
              { txOutputs = txOutputs
              ; inputVal = inputVal
              ; signature = signature
              ; purpose = Spending y
              }} {aux} p
-- ∀ {l val pkh ctx aux} ->  getPayOutAdr l (Exchange val pkh) ctx ≡ Just aux -> aux ≡ pkh
asdd l@{record { ratio = ratio ; owner = zero }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress₁ ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} p = asdd {l} {val} {pkh} {record
              { txOutputs = txOutputs
              ; inputVal = inputVal
              ; signature = signature
              ; purpose = Spending y
              }} {aux} p
asdd l@{record { ratio = ratio ; owner = N.suc owner₁ }} {val} {pkh} {record { txOutputs = record { txOutAddress = zero ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} p = asdd {l} {val} {pkh} {record
              { txOutputs = txOutputs
              ; inputVal = inputVal
              ; signature = signature
              ; purpose = Spending y
              }} {aux} p
asdd {record { ratio = ratio ; owner = N.suc owner }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} p
  = asdd {record { ratio = ratio ; owner = owner }} {val} {pkh} {record { txOutputs = record { txOutAddress = N.suc txOutAddress ; txOutValue = txOutValue ; txOutDatum = Script x } ∷ txOutputs ; inputVal = inputVal ; signature = signature ; purpose = Spending y }} {aux} {!p!}
{-with eqNat owner txOutAddress
...| True = ?
...| False = {!!} -}-}
-}
