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
open import Haskell.Prelude using (lookup ; _<>_)


module DExpandedProofs2 where


record Context : Set where
  field
    value         : Value  
    payVal        : Value
    payTo         : PubKeyHash
    payDat        : OutputDatum -- Flat bits we need instead of nested strucutre
    buyVal        : Value
    buyTo         : PubKeyHash
    buyDat        : OutputDatum
    tsig          : PubKeyHash -- List?
    self          : Address
open Context

-- More structure? Optional ones?

record State : Set where
  field
    label         : Label    -- datum
    context       : Context
    continues     : Bool -- move to Context, because from context
open State


data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {amt r s s' par lab}
    -> label s ≡ lab
    -> owner lab ≡  tsig (context s')
    -> value (context s') ≡ record { amount = amt ; currency = sellC par }
    -> label s' ≡ (record { ratio = r ; owner = owner lab })
    -> checkRational r ≡ True -- automate this maybe?
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'

{-
 amt - going out to the user in SellC
 payval - going out to owner in BuyC
-}

  TExchange : ∀ {amt pkh s s' par lab}
    -> value (context s) ≡ (value (context s')) <> record { amount = amt ; currency = sellC par }
    -> label s' ≡ label s
    -> label s ≡ lab --??
    -> payTo (context s') ≡ (owner lab)
    -> amt * num (ratio lab) ≤ (amount (payVal (context s'))) * den (ratio lab) -- >
    -> currency (payVal (context s')) ≡ buyC par  -- factor these 2 out in 1 function
    -> payDat (context s') ≡ Payment (self (context s'))
    -> buyTo  (context s') ≡ pkh 
    -> buyVal (context s') ≡ record { amount = amt ; currency = sellC par }
    -> buyDat (context s') ≡ Payment (self (context s'))
    -> continues s ≡ True
    -> continues s' ≡ True
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

  TClose : ∀ {s s' par lab}
    -> label s ≡ lab --??
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

  Oth : ∀ {s}
    -> checkRational (ratio (label s)) ≡ True -- label s fix
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


selfContinuing : ∀ {s s' : State} {i par}
  -> i ≢ Close
  -> par ⊢ s ~[ i ]~> s'
  -> continues s' ≡ True
selfContinuing pf (TUpdate p1 p2 p3 p4 p5 p6 p7) = p7
selfContinuing pf (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) = p12
selfContinuing pf (TClose p1 p2 p3 p4) = ⊥-elim (pf refl)


noDoubleSatOut : ∀ {s s' : State} {i par amt pkh}
  -> i ≡ Exchange amt pkh
  -> par ⊢ s ~[ i ]~> s'
  -> (payDat (context s') ≡ Payment (self (context s')) × buyDat (context s') ≡ Payment (self (context s')))
noDoubleSatOut refl (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) = (p7 , p10)


--State Validity Invariant
validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition {record { label = .( (record { ratio = ratio₁ ; owner = tsig context })) ; context = context₁ ; continues = .true }} {record { label = .( (record { ratio = _ ; owner = tsig context })) ; context = context ; continues = .true }} iv (TUpdate {lab = record { ratio = ratio₁ ; owner = .(tsig context) }} refl refl refl refl p5 refl refl) = Oth p5
validStateTransition (Stp x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite x = ⊥-elim (get⊥ (sym p11))
validStateTransition (Oth y) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite sym p2 = Oth y
validStateTransition iv (TClose p1 p2 p3 p4) = Stp p4


validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x

--include minAda
--closeLiquidity -> value ≡ 0
--runtimeLiduqidity -> value ≡ minAda

--valid -> minAda OR closed
--Value -> (TokenName -> (CurrencyScipt -> Integer) )

--because we learned MinAda problems with previous Liquidity proof

liquidity : ∀ (par : Params) (s : State) --(pkh : PubKeyHash) 
          -> ValidS s -> continues s ≡ True
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (amount (value (context s')) ≡ 0) )
liquidity par s (Stp x) p2 rewrite p2 = ⊥-elim (get⊥ x)
liquidity par record { label = lab ; context = context ; continues = continues } (Oth y) p2 = ⟨ s' , ⟨  Close ∷ [] , (cons (TClose refl refl p2 refl ) root , refl) ⟩ ⟩
  where
    s' = record { label = (record { ratio = ratio lab ; owner = owner lab }) ;
                  context = record
                             { value = record { amount = 0 ; currency = sellC par }
                             ; payVal = (value (context))
                             ; payTo = (owner lab)
                             ; payDat = Payment 0
                             ; buyVal = record { amount = 0 ; currency = 0 }
                             ; buyTo = 0
                             ; buyDat = Payment 0
                             ; tsig = owner lab
                             ; self = self context
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

rewriteAdd : ∀ {a} (b c : Integer) -> a ≡ addInteger b c -> a ≡ b + c
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




getPayOutVal : Label -> ScriptContext -> Value
getPayOutVal l ctx = (txOutValue (getPaymentOutput (owner l) ctx))

getPayOutAdr : Label -> ScriptContext -> Address
getPayOutAdr l ctx = (txOutAddress (getPaymentOutput (owner l) ctx))

getPayOutDat : Label -> ScriptContext -> OutputDatum
getPayOutDat l ctx = (txOutDatum (getPaymentOutput (owner l) ctx))

getBuyOutVal : Label -> Input -> ScriptContext -> Value
getBuyOutVal l (Update r amt) ctx = record { amount = -1 ; currency = 0 }
getBuyOutVal l (Exchange amt pkh) ctx = (txOutValue (getPaymentOutput pkh ctx))
getBuyOutVal l Close ctx = record { amount = -1 ; currency = 0 }

getBuyOutAdr : Label -> Input -> ScriptContext -> Address
getBuyOutAdr l (Update r amt) ctx = 0
getBuyOutAdr l (Exchange amt pkh) ctx = (txOutAddress (getPaymentOutput pkh ctx))
getBuyOutAdr l Close ctx = 0

getBuyOutDat : Label -> Input -> ScriptContext -> OutputDatum
getBuyOutDat l (Update r amt) ctx = Payment 0
getBuyOutDat l (Exchange amt pkh) ctx = (txOutDatum (getPaymentOutput pkh ctx))
getBuyOutDat l Close ctx = Payment 0


==vto≡ : {a b : Value} -> (a == b) ≡ true -> a ≡ b
==vto≡ {record { amount = a1 ; currency = c1 }} {record { amount = a2 ; currency = c2 }} p
  rewrite (==ito≡ {a1} {a2} (get p)) | (==to≡ {c1} {c2} (go (a1 == a2) p)) = refl

rewriteMulCheck : ∀ (l : Label) (ctx : ScriptContext) (val) ->
  ((mulInteger val (num (ratio l))) <= (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)))) ≡ True ->
  (((sign val Sign.* sign (num (ratio l))) ◃ mulNat ∣ val ∣ ∣ num (ratio l) ∣) ≤
  ((sign (amount (txOutValue (getPaymentOutput (owner l) ctx))) Sign.* sign (den (ratio l))) ◃
  mulNat ∣ (amount (txOutValue (getPaymentOutput (owner l) ctx))) ∣ ∣ den (ratio l) ∣))
rewriteMulCheck l ctx val p rewrite mul≡ val (num (ratio l)) | mul≡ (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)) = <=ito≤ p


5&&false : ∀ {a b c d e : Bool} -> e ≡ False -> (a && b && c && d && e) ≡ False
5&&false {false} {b} {c} {d} refl = refl
5&&false {true} {false} {c} {d} refl = refl
5&&false {true} {true} {false} {d} refl = refl
5&&false {true} {true} {true} {false} refl = refl
5&&false {true} {true} {true} {true} refl = refl

contradict : ∀ {b : Bool} -> b ≡ True -> b ≡ False -> ⊥
contradict refl ()

prop0 : ∀ {par l i ctx cs } -> purpose ctx ≡ Minting cs -> i ≢ Close -> agdaValidator par l i ctx ≡ False
prop0 {par} {l} {Update amt r} ctx@{record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 =  5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} refl
prop0 {par} {l} {Update amt r} ctx@{record { txOutputs = x ∷ txOutputs₁ ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 =  5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} refl
prop0 {par} {l} {Exchange amt pkh} ctx@{record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0 {par} {l} {Exchange amt pkh} ctx@{record { txOutputs = x ∷ txOutputs₁ ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0 {i = Close} p1 p2 = ⊥-elim (p2 refl)

prop : ∀ {par l i ctx} -> agdaValidator par l i ctx ≡ True -> i ≢ Close -> ∃[ adr ] purpose ctx ≡ Spending adr
prop {par} {l} {i} {ctx} p1 p2 with (purpose ctx) in eq
...| Spending adr' = ⟨ adr' , refl ⟩
...| Minting cs = ⊥-elim (contradict p1 (prop0 eq p2)) --(get⊥ {!!})

prop0' : ∀ {par l amt pkh ctx cs } -> purpose ctx ≡ Minting cs -> agdaValidator par l (Exchange amt pkh) ctx ≡ False
prop0' {par} {l} {amt} {pkh} ctx@{ctx = record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting x }} p = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0' {par} {l} {amt} {pkh} ctx@{ctx = record { txOutputs = x ∷ txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting y }} p = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl

==dto≡ : {a b : OutputDatum} -> (a == b) ≡ True -> a ≡ b
==dto≡ {Payment x} {Payment y} p rewrite ==to≡ {x} {y} p = refl
==dto≡ {Script x} {Script y} p rewrite ==lto≡ x y p = refl

prop' : ∀ {par l amt pkh ctx} -> agdaValidator par l (Exchange amt pkh) ctx ≡ True ->  ∃[ adr ] (purpose ctx ≡ Spending adr × (txOutDatum (getPaymentOutput (owner l) ctx)) ≡ Payment adr)
prop' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Spending adr }} p = ⟨ adr , (refl , ==dto≡ (go (currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par) (go (ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l)) (go (txOutAddress (getPaymentOutput (owner l) ctx) == owner l) (get (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }) p))))))) ⟩
prop' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting cs }} p = ⊥-elim (contradict p (prop0' {par} {l} {amt} {pkh} {ctx} {cs} refl))

prop'' : ∀ {par l amt pkh ctx} -> agdaValidator par l (Exchange amt pkh) ctx ≡ True ->  ∃[ adr ] (purpose ctx ≡ Spending adr × (txOutDatum (getPaymentOutput pkh ctx)) ≡ Payment adr)
prop'' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Spending adr }} p = ⟨ adr , (refl , ==dto≡ (go ( (txOutValue (getPaymentOutput pkh ctx)) == record { amount = amt ; currency = sellC par }) (go (txOutAddress (getPaymentOutput pkh ctx) == pkh) (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }) p))))))) ⟩
prop'' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting cs }} p = ⊥-elim (contradict p (prop0' {par} {l} {amt} {pkh} {ctx} {cs} refl))


rewriteDatEq : ∀ {dat ctx} -> ∃[ adr ] (purpose ctx ≡ Spending adr × dat ≡ Payment adr) -> dat ≡ Payment (getSelf ctx)
rewriteDatEq {dat} {record { txOutputs = txOutputs₁ ; inputVal = inputVal₁ ; inputAc = inputAc₁ ; signature = signature₁ ; purpose = .(Spending adr) }} ⟨ adr , (refl , p2) ⟩ = p2

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {pV pT pD bV bT bD sf s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payVal = pV ; payTo = pT ; payDat = pD ;
                           buyVal = bV ; buyTo = bT ; buyDat = bD ;
                           tsig = s ; self = sf } ; continues = True }
                           ~[ i ]~>
                           record { label = newLabel ctx ; context = record { value = newValue ctx ;
                           payVal = getPayOutVal l ctx ; payTo = getPayOutAdr l ctx ; payDat = getPayOutDat l ctx  ;
                           buyVal = getBuyOutVal l i ctx ; buyTo = getBuyOutAdr l i ctx ; buyDat = getBuyOutDat l i ctx ;
                           tsig = signature ctx ; self = getSelf ctx} ; continues = continuing ctx}
validatorImpliesTransition par l (Update val r) ctx pf
  = TUpdate refl (==to≡ (get pf)) (==vto≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
  ((==lto≡ (newLabel ctx) (record { ratio = r ; owner = owner l }) (get (go
  (newValue ctx == record { amount = val ; currency = sellC par })
  (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))))
  (get (go ((owner l) == (signature ctx)) pf)) refl (go (newLabel ctx == (record {ratio = r ; owner = owner l}))
  (go (newValue ctx == record { amount = val ; currency = sellC par }) (go (checkRational r)
  (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l (Exchange amt pkh) ctx pf
  = TExchange (==vto≡ (get pf)) (==lto≡ (newLabel ctx) l
  (get (go (oldValue ctx == (newValue ctx) <> val) pf))) refl
  (==to≡ (get (get (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> val) pf)))))
  (rewriteMulCheck l ctx amt (get (go ((txOutAddress (getPaymentOutput (owner l) ctx)) == (owner l))
  (get (go (newLabel ctx == l) ((go (oldValue ctx == (newValue ctx) <> val) pf)))))))
  (==to≡ (get (go (ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l))
  (go ((txOutAddress (getPaymentOutput (owner l) ctx)) == (owner l))
  (get (go (newLabel ctx == l) ((go (oldValue ctx == (newValue ctx) <> val) pf))))))))
  (rewriteDatEq {txOutDatum (getPaymentOutput (owner l) ctx)} {ctx} (prop' {par} {l} {amt} {pkh} {ctx} pf))
  (==to≡ (get (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf))))))
  (==vto≡ (get (go (txOutAddress (getPaymentOutput pkh ctx) == pkh)
  (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf)))))))
  ((rewriteDatEq {txOutDatum (getPaymentOutput pkh ctx)} {ctx} (prop'' {par} {l} {amt} {pkh} {ctx} pf)))
  refl
  (go (checkBuyer par amt pkh ctx) (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf))))
    where
      val = record { amount = amt ; currency = sellC par }
validatorImpliesTransition par l Close ctx pf
  = TClose refl (==to≡ (go (not (continuing ctx)) pf)) refl (unNot (get pf))


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


≡to==v : ∀ {a b : Value} -> a ≡ b -> (a == b) ≡ true
≡to==v {a} {.a} refl rewrite i=i (amount a) | n=n (currency a) = refl

≤to<= : ∀ {a b : Nat} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤to<= {b = zero} N.z≤n = refl
≤to<= {b = N.suc b} N.z≤n = refl
≤to<= (N.s≤s p) = ≤to<= p

≤ito<= : ∀ {a b : Integer} -> a ≤ b -> (ltInteger a b || eqInteger a b) ≡ true
≤ito<= (-≤- n≤m) = ≤to<= n≤m
≤ito<= -≤+ = refl
≤ito<= (+≤+ m≤n) = ≤to<= m≤n

≡to==d : ∀ {a b : OutputDatum} -> a ≡ b -> (a == b) ≡ true
≡to==d {Payment x} refl rewrite n=n x = refl
≡to==d {Script x} refl rewrite n=n (owner x) | i=i (num (ratio x)) | i=i (den (ratio x)) = refl --rewrite r=r x = {!!}

transitionImpliesValidator : ∀ {pV pT pD bV bT bD sf s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payVal = pV ; payTo = pT ; payDat = pD ; buyVal = bV ; buyTo = bT ; buyDat = bD ; tsig = s ; self = sf } ; continues = True }
                           ~[ i ]~>
                           record { label = newLabel ctx ; context = record { value = newValue ctx ;
                           payVal = getPayOutVal l ctx ; payTo = getPayOutAdr l ctx ; payDat = getPayOutDat l ctx  ;
                           buyVal = getBuyOutVal l i ctx ; buyTo = getBuyOutAdr l i ctx ; buyDat = getBuyOutDat l i ctx ;
                           tsig = signature ctx ; self = getSelf ctx} ; continues = continuing ctx})
                           -> agdaValidator par l i ctx ≡ true

transitionImpliesValidator par l (Update amt r) ctx (TUpdate refl p2 p3 p4 p5 p6 p7)
  rewrite ≡to== p2 | p5 | ≡to==v p3 | ≡to==l p4 = p7
transitionImpliesValidator par l (Exchange amt pkh) ctx (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12)
  rewrite ≡to==v p1 | ≡to==l p2 | sym p3 | ≡to== p4 | mul≡ amt (num (ratio l)) |
  mul≡ (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)) |
  ≤ito<= p5 | ≡to== p6 | ≡to== p8 | ≡to==v p9 | ≡to==d p10 | ≡to==d p7 = p12 
transitionImpliesValidator par l Close ctx (TClose p1 p2 p3 p4) rewrite p4 | p1 = ≡to== p2





rewriteContinuing : ∀ {ctx} -> getContinuingOutputs ctx ≡ [] -> continuing ctx ≡ False
rewriteContinuing p rewrite p = refl

prop1 : ∀ {par l i ctx} -> getContinuingOutputs ctx ≡ [] -> i ≢ Close -> agdaValidator par l i ctx ≡ False
prop1 {par} {l} {Update amt r} {ctx} p1 p2 = 5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} (rewriteContinuing {ctx} p1)
prop1 {par} {l} {Exchange amt pkh} {ctx} p1 p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} (rewriteContinuing {ctx} p1)
prop1 {par} {l} {Close} {ctx} p1 p2 = ⊥-elim (p2 refl)

rewriteContinuing' : ∀ {ctx tx1 tx2 txs} -> getContinuingOutputs ctx ≡ (tx1 ∷ tx2 ∷ txs)  -> continuing ctx ≡ False
rewriteContinuing' p rewrite p = refl 

prop2 : ∀ {par l i ctx tx1 tx2 txs} -> getContinuingOutputs ctx ≡ (tx1 ∷ tx2 ∷ txs) -> i ≢ Close -> agdaValidator par l i ctx ≡ False
prop2 {par} {l} {Update amt r} {ctx} {tx1} {tx2} {txs} p1 p2 = 5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} (rewriteContinuing' {ctx} {tx1} {tx2} {txs} p1) 
prop2 {par} {l} {Exchange amt pkh} {ctx} {tx1} {tx2} {txs} p1 p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} (rewriteContinuing' {ctx} {tx1} {tx2} {txs} p1) 
prop2 {par} {l} {Close} {ctx} p1 p2 = ⊥-elim (p2 refl)


{-
rwr : ∀ {amt l txo ctx}
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue txo))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue txo))
        (den (ratio l)))) ≡ False
  -> (getPaymentOutput (owner l) ctx) ≡ txo
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))) ≡ False
rwr p1 refl = p1

prop3' : ∀ {l amt ctx}
  -> getPaymentOutput (owner l) ctx ≡ record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
                                      ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }
  -> ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l) ≡ False
  -- -> checkPayment par amt l pkh ctx ≡ False
prop3' {l} {amt} {ctx} p = rwr {amt} {l} {ctx = ctx} {!!} p


rwr' : ∀ {par l amt ctx asdf}
  -> (eqNat (txOutAddress (getPaymentOutput (owner l) ctx))
       (owner l)
       &&
       asdf
       &&
       eqNat (currency (txOutValue (getPaymentOutput (owner l) ctx)))
       (buyC par)
       &&
       eqDatum (txOutDatum (getPaymentOutput (owner l) ctx))
       (Payment (getSelf ctx)))
      ≡ false
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l))))
      ≡ asdf
  -> asdf ≡ False
  -> (eqNat (txOutAddress (getPaymentOutput (owner l) ctx))
       (owner l)
       &&
       (ltInteger (mulInteger amt (num (ratio l)))
        (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
         (den (ratio l)))
        ||
        eqInteger (mulInteger amt (num (ratio l)))
        (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
         (den (ratio l))))
       &&
       eqNat (currency (txOutValue (getPaymentOutput (owner l) ctx)))
       (buyC par)
       &&
       eqDatum (txOutDatum (getPaymentOutput (owner l) ctx))
       (Payment (getSelf ctx)))
      ≡ false
rwr' p1 p2 refl rewrite p2 = p1

rwr'' : ∀ {par l amt ctx}
  -> (eqNat (txOutAddress (getPaymentOutput (owner l) ctx))
       (owner l)
       &&
       False
       &&
       eqNat (currency (txOutValue (getPaymentOutput (owner l) ctx)))
       (buyC par)
       &&
       eqDatum (txOutDatum (getPaymentOutput (owner l) ctx))
       (Payment (getSelf ctx)))
      ≡ false
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l))))
      ≡ False
  -> (eqNat (txOutAddress (getPaymentOutput (owner l) ctx))
       (owner l)
       &&
       (ltInteger (mulInteger amt (num (ratio l)))
        (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
         (den (ratio l)))
        ||
        eqInteger (mulInteger amt (num (ratio l)))
        (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
         (den (ratio l))))
       &&
       eqNat (currency (txOutValue (getPaymentOutput (owner l) ctx)))
       (buyC par)
       &&
       eqDatum (txOutDatum (getPaymentOutput (owner l) ctx))
       (Payment (getSelf ctx)))
      ≡ false
rwr'' p1 p2 rewrite p2 = p1

3&&false : ∀ {a b : Bool} -> (a && b && false) ≡ false
3&&false {false} {b} = refl
3&&false {true} {false} = refl
3&&false {true} {true} = refl

2&&false : ∀ {a : Bool} -> (a && false) ≡ false
2&&false {false} = refl
2&&false {true} = refl


prop3'' : ∀ {par l amt ctx pkh}
  -> ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l) ≡ False
  -> checkPayment par amt l pkh ctx ≡ False
prop3'' {par} {l} {amt} {ctx} {pkh} p = rwr'' {par} {l} {amt} {ctx} (2&&false {eqNat (txOutAddress (getPaymentOutput (owner l) ctx))
       (owner l)}) p --(3&&false {{!!}} {{!!}}) p



prop3''' : ∀ {par l amt ctx pkh}
  -> checkPayment par amt l pkh ctx ≡ False
  -> agdaValidator par l (Exchange amt pkh) ctx ≡ False
prop3''' p rewrite p = {!!}

prop3 : ∀ {par l amt pkh ctx}
  -> getPaymentOutput (owner l) ctx ≡ record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
                                      ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }
  -> agdaValidator par l (Exchange amt pkh) ctx ≡ False
prop3 {par} {l} {amt} {pkh} {ctx} p = {!!}

-}

{-
dingus : ∀ (f : Nat -> Nat) (n : Nat) -> Nat
dingus f n = f $ n

bingus : ∀ {par l amt pkh ctx}
         -> (pf : checkPayment par amt l pkh ctx ≡ true)
         -> txOutAddress (getPaymentOutput (owner l) ctx) ≡ owner l
bingus {par} {l} {amt} {pkh} {ctx} pf = ==to≡ (get pf)


getf : ∀ {b : Bool} -> (b && false) ≡ False
getf {false} = refl
getf {true} = refl

asd : {ctx : ScriptContext} {lhs : List TxOut} →
      lhs ≡ [] → (case lhs of λ { (o ∷ []) → true ; _ → false }) ≡ false
asd pf rewrite pf = refl --refl
-}

--do validS validP



--agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool


{--}
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


{-
 (go (oldValue ctx == (newValue ctx) <> val) pf)
validatorImpliesTransition par l (Exchange val pkh) ctx pf -- with getPaymentOutput (owner l) ctx 
  = TExchange (rewriteAdd (newValue ctx)  val (==ito≡ (get pf)))
    (==lto≡ (newLabel ctx) l (get (go (oldValue ctx == addInteger (newValue ctx) val) pf))) refl
    (==to≡ (get (get (go (newLabel ctx == l) (go (oldValue ctx == addInteger (newValue ctx) val) pf))))) refl
    (rewriteMulCheck l ctx val (go ((txOutAddress (getPaymentOutput (owner l) ctx)) == (owner l))
    (get (go (newLabel ctx == l) (go (oldValue ctx == addInteger (newValue ctx) val) pf)))))
    (==to≡ (get (get (go (checkPayment par val l pkh ctx) (go (newLabel ctx == l)
    (go (oldValue ctx == addInteger (newValue ctx) val) pf))))))
    {!!} refl {!!}

 = TUpdate refl (==to≡ (get pf)) (==ito≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
  ((==lto≡ (newLabel ctx) (record { ratio = r ; owner = owner l }) (get (go (newValue ctx == val)
  (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))))
  (get (go ((owner l) == (signature ctx)) pf)) refl (go (newLabel ctx == (record {ratio = r ; owner = owner l}))
    (go (newValue ctx == val) (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l Close ctx pf = TClose refl (==to≡ (go (not (continuing ctx)) pf)) refl (unNot (get pf))
-}

{-
(eqNat (txOutAddress (getPaymentOutput (owner l) ctx)) (owner l) &&
        (ltInteger (mulInteger val (num (ratio l)))
         (mulInteger (txOutValue (getPaymentOutput (owner l) ctx))
          (den (ratio l)))
         ||
         eqInteger (mulInteger val (num (ratio l)))
         (mulInteger (txOutValue (getPaymentOutput (owner l) ctx))
          (den (ratio l)))))
-}



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
  = TClose (==to≡ (go (not (continues ctx)) pf)) refl (unNot (get pf)) -}


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

--  = {!!} -- <=ito≤ p 
{-
sign val Sign.* sign (num (ratio l)) ◃
      mulNat ∣ val ∣ ∣ num (ratio l) ∣
      ≤
      sign (txOutValue (getPaymentOutput (owner l) ctx)) Sign.*
      sign (den (ratio l))
      ◃
      mulNat ∣ txOutValue (getPaymentOutput (owner l) ctx) ∣
      ∣ den (ratio l) ∣


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

{-
==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p)

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
 -}
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
