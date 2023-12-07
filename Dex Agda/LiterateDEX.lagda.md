This is the example I wrote in the e-mail with the specification, I decided to paste it in
here as a refresher of what we are looking at, but feel free to skip to later on if you
remember this part well. 

The idea is that each individual instance of an Order Book DEx contract serves as an exchange
point for 2 currencies. Users can then post offers on this contract, saying that they are
looking to sell a certain amount of one of the two currencies at a fixed rate. This essentially
means you are guaranteed the exchange rate that you want, but not when you might get it. The
purpose of an Order Book DEx is not to match these orders to one another. Instead, other users
can request to consume certain offers, either totally or partially, and then pay the commensurate
price for the exchange. For this option, you get the money you want now, but at whatever rates
are available for you. You can also cancel previously posted offers, but this is not a very
interesting case.

Note that this is completely separate from the account simulation at the moment. They could
be made to work together though

Quick Example: There are some offers in the contract: 
User1 is selling 1000 Dogcoins at a rate of 0.8 Catcoin/Dogcoin
User2 is selling 1000 Dogcoins at a rate of 0.7 Catcoin/Dogcoin
User3 is selling 10000 Dogcoins at a rate of 0.9 Catcoin/Dogcoin
User4 is selling 10000 Catcoins at a rate of 1.4 Dogcoin/Catcoin

User5 wants to buy 1500 Dogcoins, they will obviously want to pay the least amount possible,
so they will request 1000 Dogcoins from User2 and 500 Dogcoins from User1, paying 700
(1000 * 0.7) Catcoins to User 2 and 400 (500 * 0.8) Catcoins to User1 for a total of 1100
Catcoins. User1's offer is only partially consumed and User3's offer is untouched, because
there was not enough demand, and they offered the worst exchange rates. User4's offer is
irrelevant to us, since we are not buying Catcoins. 

If for some reason they wanted to use a specific offer, User5 could also choose to buy all
1500 Dogcoins from User3, paying them 1350 Catcoins by requesting that specific order.


```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (dec-yes)
open import Data.Integer hiding (_⊔_) -- hiding (_≤_;)
open import Data.Rational  hiding (_⊔_) -- hiding (_≤_;)
open import Data.String
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core
open import Agda.Builtin.Equality



private variable A B C : Set

```
In PlutusTx, "Currencies" are a pair of CurrencyScript (hash of the minting policy)
and TokenName, which are both wrappers around BuiltinByteString. In order to simplify
some of that, I made it a data type with 3 constructors, since all we really care
about are the two currencies in the contract (C1 and C2), and all other currencies.

Attached is decidable equality for Currencies which is needed but uninteresting.
```agda

data Currency : Set where
  C1    : Currency
  C2    : Currency
  Other : Currency

_c=?_ : ∀ (x y : Currency) -> Dec (x ≡ y)
C1 c=? C1 = yes refl
C1 c=? C2 = no (λ ())
C1 c=? Other = no (λ ())
C2 c=? C1 = no (λ ())
C2 c=? C2 = yes refl
C2 c=? Other = no (λ ())
Other c=? C1 = no (λ ())
Other c=? C2 = no (λ ())
Other c=? Other = yes refl

```
In agda, I have not written an implementation of maps, instead we postulate an interface for
interacting with maps. The concrete implementation is probably going to based on lists of pairs.
```agda

postulate
  Map : (A : Set) → (B : Set) → Set
  
  insert : A -> B → Map A B → Map A B
  singleton : A -> B -> Map A B

```
Notably insert is not your traditional map insertion, but I kept the name due to lack of a
better alternative. In haskell it would look something like this:

{-# INLINABLE insert' #-} 
insert' :: (Ord k, Addable v) => k -> v -> [(k, v)] -> [(k, v)]
insert' key val [] = (key,val):[]
insert' key val ((k,v):xs)
    | key < k = (key,val):((k,v):xs)
    | key == k = (key,(v + val)):xs
    | otherwise = (k,v):insert' key val xs

The main difference is that if the key already is present in the map, we add to the existing
value instead of replacing it. The fact the list is ordered is not particularly relevant
to us at the moment, but the value type B has to be "Addable". I gloss over this in this in
the agda interface because it is postulated anyway, and our values are ℤ or Map _ ℤ, which
are obviosly addable. (Adding two maps is equivalent to inserting all elements of one into
the other)
```agda

  query : ∀ (k : A) (m : Map A B) → B

```
Normally a query would have return type Maybe B, but instead of doing that, if the key is
not present in the map we return the 0 value for our B type, 0ℤ and an empty map respectively.
```agda

  _≤ᵐ_ : Map A B → Map A B → Set
  _≤?ᵐ_ : ∀ (m m′ : Map A B) → Dec (m ≤ᵐ m′)
  _-ᵐ_ : Map A B → Map A B → Map A B

```
We have a notion of map comparison in order to establish when a request is valid. More details
later, but in essence m1 ≤ᵐ m2 if ∀ (k,v) ∈ m1, ∃ (k, v') ∈ m2 such that v ≤ v'. This is
essentially a "subset" relation.
```agda

  sum : Map A B -> B
  compute : Map A (Map B C) -> B -> Currency -> Currency -> Map B (Map Currency C)

```
These are functions specifically needed for our DEx implementation. Sum calculates the sum of
all values in the map, ignoring keys. Compute is a complex function that I am mostly glossing
over for now, but it computes the list of outputs for the REQUEST operation.
```agda


  
record State : Set where
  field
    curr1 : Currency
    curr2 : Currency
    pf    : curr1 ≢ curr2
    omap1 : Map ℚ ( Map String ℤ )
    omap2 : Map ℚ ( Map String ℤ )
    v1    : ℤ
    v2    : ℤ
    out   : Map String (Map Currency ℤ)

open State

```
State here encompasses both internal contract state and blockchain UTxO state.
Internally:

curr1, curr2 : Currency the 2 currencies it is exchanging

pf is a proof that the two currencies are different, because this is an invariant on our State

omap1 : Map ℚ ( Map String ℤ ) a map representing the offers (Limit Orders) where ℚ is represents
the exchange rate, "String" is the public key hash of the users who submitted offers, and ℤ is
the amount of curr1 being offered.

omap2 : Map ℚ ( Map String ℤ ) similarly for curr2.

Here, having two maps, one for each currency makes it much easier to write the code and express
properties without having to contrantly deal with maps containing two different types of currency.

Blockchain:

v1 : ℤ is the blockchain amount of curr1 in the UTxO representing the contract

v2 : ℤ similarly for curr2

out : Map String (Map Currency ℤ) is the map representing the outputs that need to be present
alongside the contract for specific transactions. "String" is the public key hash of the users
who need to be paid, Currency is the currency they need to be paid in, and ℤ the amount.

I am abstracting inputs and signatures away completely, and assuming that if they are part
of the input to the transition function, they also valid blockchain inputs and signatures.
```agda


offer : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
offer st pkh v cur r =
  if (Dec.does (0ℤ Data.Integer.<? v))
    then if (Dec.does (0ℚ Data.Rational.<? r))
      then if (Dec.does (cur c=? (curr1 st)))
        then just (record st { omap1 = (insert r (singleton pkh v) (omap1 st)); v1 = (v1 st) Data.Integer.+ v } )
        else if (Dec.does (cur c=? (curr2 st)))
          then just (record st { omap2 = (insert r (singleton pkh v) (omap2 st)) ; v2 = (v2 st) Data.Integer.+ v } )
          else nothing
      else nothing
    else nothing

```

Offers (Limit Orders):
"offer st pkh val cur rate"
Is the transition that indicates when a user with a certain pkh wants to offer an amount val of
tokens of type cur at exchange rate "rate".

Preconditions: 
val > 0 
rate > 0
curr == curr1 st or curr == curr2 st

Postconditions:
if curr == curr1 st:
omap1 = (insert r (singleton pkh v) (omap1 st)
v1 = v1 + val

if curr == curr2 st:
omap2 = (insert r (singleton pkh v) (omap2 st)
v2 = v2 + val

no putputs
```agda

request : State -> String -> Currency -> Map ℚ (Map String ℤ) -> Maybe State
request st pkh cur cmap =
  if (Dec.does (cur c=? (curr1 st)))
    then if (Dec.does (cmap ≤?ᵐ (omap1 st)))
      then just (record st { omap1 = (omap1 st) -ᵐ cmap ; out = compute cmap pkh cur (curr2 st)
        ; v1 = (v1 st) Data.Integer.- sum(sum cmap)})
      else nothing
    else if (Dec.does (cur c=? (curr2 st)))
      then if (Dec.does (cmap ≤?ᵐ (omap2 st)))
        then just (record st { omap2 = (omap2 st) -ᵐ cmap ; out = compute cmap pkh cur (curr1 st)
          ; v2 = (v2 st) Data.Integer.- sum(sum cmap)})
        else nothing
      else nothing

```
Requests (Market Order):
"request st pkh cur cmap"
Is the transaction that indicates when a user with a certain pkh wants to post a request
for buying a specific currency "curr". "cmap" is a map with the same type as omap,
representing partially or totally consumed orders for the request.

Preconditions: 
cur == curr1 st or cur == curr2 st,

if curr == curr1 st:
cmap <ᵐ (omap1 st)

if curr == curr2 st:
cmap <ᵐ (omap2 st)

Postconditions:

if curr == curr1 st:
omap1 = (omap1 st) -ᵐ cmap
v1 = (v1 st) Data.Integer.- sum(sum cmap)
out = compute cmap pkh cur (curr2 st)

if curr == curr2 st:
omap2 = (omap2 st) -ᵐ cmap
v2 = (v2 st) Data.Integer.- sum(sum cmap)
out = compute cmap pkh cur (curr1 st)

```agda

cancel : State -> String -> ℤ -> Currency -> ℚ -> Maybe State
cancel st pkh v cur r =
  if (Dec.does (cur c=? (curr1 st)))
    then if ( Dec.does ( 0ℤ Data.Integer.<? v ) ∧ Dec.does ( v Data.Integer.≤? (query pkh (query r (omap1 st))) ) )
      then just (record st { omap1 = insert r (singleton pkh ( Data.Integer.- v )) (omap1 st)
        ; v1 = (v1 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
      else nothing
    else if (Dec.does (cur c=? (curr2 st)))
      then if ( Dec.does ( 0ℤ Data.Integer.<? v ) ∧ Dec.does ( v Data.Integer.≤? (query pkh (query r (omap2 st))) ) )
        then just (record st { omap2 = insert r (singleton pkh ( Data.Integer.- v )) (omap2 st)
          ; v2 = (v2 st) Data.Integer.- v ; out = singleton pkh (singleton cur v) })
        else nothing
      else nothing

```
Cancel (for Limit Orders):
"cancel st pkh val cur rate"
Is the transaction that indicates when a user with a certain pkh wants to cancel an offer that they
previously made with val, cur and rate parameters

Preconditions: 

val > 0
cur == curr1 st or cur == curr2 st,

if cur == curr1 st:
val < (query pkh (query rate (omap1 st))

if cur == curr2 st:
val < (query pkh (query rate (omap2 st))

Postconditions:
if cur == curr1 st:
omap1 = insert r (singleton pkh ( Data.Integer.- v )) (omap1 st)
v1 = (v1 st) Data.Integer.- v ;

if cur == curr2 st:
omap2 = insert r (singleton pkh ( Data.Integer.- v )) (omap2 st)
v2 = (v2 st) Data.Integer.- v ;
 
out = singleton pkh (singleton cur v)

```agda




prop1 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} {cur : Currency}
      -> (cur ≢ (curr1 st) )
      -> (cur ≢ (curr2 st) )
      --------------------------
      -> (offer st pkh v cur r) ≡ nothing
prop1 {v = +_ zero} nc1 nc2 = refl
prop1 {v = -[1+_] n} nc1 nc2 = refl
prop1 {v = +[1+ n ]} {mkℚ (-[1+_] n₁) denominator-1 isCoprime} nc1 nc2 = refl
prop1 {v = +[1+ n ]} {mkℚ (+_ zero) denominator-1 isCoprime} nc1 nc2 = refl
prop1 {st}  {v = +[1+ n ]} {mkℚ +[1+ n₁ ] denominator-1 isCoprime} {cur} nc1 nc2 with cur c=? curr1 st | cur c=? curr2 st
...| yes x | _     = ⊥-elim (nc1 x)
...| no  x | yes y = ⊥-elim (nc2 y)
...| no  x | no  y = refl


prop2 : ∀ {st : State} {pkh : String} {curr : Currency} {r : ℚ} -> (offer st pkh -1ℤ curr r) ≡ nothing
prop2 = refl

prop3 : ∀ {st : State} {pkh : String} {v : ℤ} {curr : Currency} -> (offer st pkh v curr -½ ) ≡ nothing
prop3 {v = +_ zero}  = refl
prop3 {v = +[1+ n ]} = refl
prop3 {v = -[1+_] n} = refl


prop4 : ∀ {st : State} {pkh : String} {v : ℤ} {r : ℚ} {cur : Currency}
      -> (cur ≢ (curr1 st) )
      -> (cur ≢ (curr2 st) )
      --------------------------
      -> (cancel st pkh v cur r) ≡ nothing
prop4 {st} {cur = cur} nc1 nc2 with cur c=? curr1 st | cur c=? curr2 st
...| yes x | _     = ⊥-elim (nc1 x)
...| no  x | yes y = ⊥-elim (nc2 y)
...| no  x | no  y = refl




lemma1 : ∀ (n : ℕ) -> ( (n Data.Nat.<ᵇ ℕ.suc n) ≡ true )
lemma1 zero = refl
lemma1 (ℕ.suc n) = lemma1 n

lemma2 : ∀ (n : ℕ) -> ( (n Data.Nat.≤ᵇ n) ≡ true )
lemma2 zero = refl
lemma2 (ℕ.suc n) = lemma1 n


lemmaCUR1 : ∀ (s : State) (n : ℕ) (pkh : String) (r : ℚ) {mst : Maybe State}
  -> (query pkh (query r (omap1 s)) ≡ (+ n))
  -> 0 Data.Nat.< n
  -> (if Dec.does (curr1 s c=? curr1 s) then
       if Dec.does (0ℤ Data.Integer.<? + n) ∧ Dec.does ( + n Data.Integer.≤? (query pkh (query r (omap1 s))) ) 
       then
       just
       (record
        { curr1 = curr1 s
        ; curr2 = curr2 s
        ; omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s)
        ; omap2 = omap2 s
        ; v1 = v1 s Data.Integer.+ Data.Integer.- (+ n)
        ; v2 = v2 s
        ; out = singleton pkh (singleton (curr1 s) (+ n))
        ; pf = pf s
        })
       else nothing
       else mst )
      ≡
      just
      (record
       { curr1 = curr1 s
       ; curr2 = curr2 s
       ; omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s)
       ; omap2 = omap2 s
       ; v1 = v1 s Data.Integer.- + n
       ; v2 = v2 s
       ; out = singleton pkh (singleton (curr1 s) (+ n))
       ; pf = pf s
       })
lemmaCUR1 s (ℕ.suc n) pkh r pf (Data.Nat.s≤s pn) with curr1 s c=? curr1 s
... | yes x rewrite pf | lemma1 n = refl
... | no  x = ⊥-elim (x refl)





lemmaCUR2 : ∀ (s : State) (n : ℕ) (pkh : String) (r : ℚ) {mst : Maybe State}
  -> (query pkh (query r (omap2 s)) ≡ (+ n))
  -> 0 Data.Nat.< n
  -> ( if Dec.does (curr2 s c=? curr1 s)
       then mst
       else if Dec.does (curr2 s c=? curr2 s)
         then if Dec.does (0ℤ Data.Integer.<? + n) ∧ Dec.does (+ n Data.Integer.≤? query pkh (query r (omap2 s)))
           then just (record
                     { curr1 = curr1 s
                     ; curr2 = curr2 s
                     ; omap1 = omap1 s
                     ; omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s)
                     ; v1 = v1 s
                     ; v2 = v2 s Data.Integer.- + n
                     ; out = singleton pkh (singleton (curr2 s) (+ n))
                     ; pf = pf s
                     })
           else nothing
         else nothing )
     ≡ just (record
            { curr1 = curr1 s
            ; curr2 = curr2 s
            ; omap1 = omap1 s
            ; omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s)
            ; v1 = v1 s
            ; v2 = v2 s Data.Integer.- + n
            ; out = singleton pkh (singleton (curr2 s) (+ n))
            ; pf = pf s
            })
lemmaCUR2 s (ℕ.suc n) pkh r prf (Data.Nat.s≤s pn) with curr2 s c=? curr1 s | curr2 s c=? curr2 s
... | yes x | _ = ⊥-elim (pf s (sym x)) --rewrite pf | lemma1 n = refl
... | no  x | yes y rewrite prf | lemma1 n = refl
... | no  x | no  y = ⊥-elim (y refl)


lemneg : ∀ (m n : ℕ) -> Data.Integer.- (+ m) Data.Integer.< +[1+ n ]
lemneg zero n = +<+ (Data.Nat.s≤s Data.Nat.z≤n)
lemneg (ℕ.suc m) n = -<+

lemsuc : ∀ (m n : ℕ) -> m Data.Nat.≤ n -> m Data.Nat.≤ ℕ.suc n
lemsuc zero n Data.Nat.z≤n = Data.Nat.z≤n
lemsuc (ℕ.suc n) (ℕ.suc m) (Data.Nat.s≤s p) = Data.Nat.s≤s (lemsuc n m p)

lemmonus : ∀ (m n : ℕ) -> m ∸ n Data.Nat.≤ m
lemmonus zero zero = Data.Nat.z≤n
lemmonus zero (ℕ.suc n) = Data.Nat.z≤n
lemmonus (ℕ.suc m) zero = Data.Nat.s≤s (lemmonus m zero)
lemmonus (ℕ.suc m) (ℕ.suc n) = lemsuc (m ∸ n) m (lemmonus m n)

lemplus : ∀ (m n : ℕ) -> m Data.Nat.≤ m Data.Nat.+ n
lemplus zero zero = Data.Nat.z≤n
lemplus (ℕ.suc m) zero = Data.Nat.s≤s (lemplus m zero)
lemplus zero (ℕ.suc n) = Data.Nat.z≤n
lemplus (ℕ.suc m) (ℕ.suc n) = Data.Nat.s≤s (lemplus m (ℕ.suc n))

lemminus : ∀ (z : ℤ) (n : ℕ)
  -> 0ℤ Data.Integer.< + n
  -> z Data.Integer.- + n  Data.Integer.< z
lemminus (+_ m) zero (+<+ ())
lemminus (+_ zero) (ℕ.suc n) p = -<+
lemminus +[1+ m ] (ℕ.suc n) p with m Data.Nat.<ᵇ n
... | true = lemneg (n ∸ m) m
... | false = +<+ (Data.Nat.s≤s (lemmonus m n))
lemminus (-[1+_] n) zero (+<+ ())
lemminus (-[1+_] zero) (ℕ.suc n) p = -<- (Data.Nat.s≤s Data.Nat.z≤n)
lemminus (-[1+_] (ℕ.suc m)) (ℕ.suc n) p = -<- (Data.Nat.s≤s (Data.Nat.s≤s (lemplus m n)))


-- Liquidity
prop5 : ∀ (s : State)
  -> ∃[ pkh ] ∃[ r ] ∃[ v ] (((query pkh (query r (omap1 s)) ≡ v) ⊎ (query pkh (query r (omap2 s)) ≡ v)) × (0ℤ Data.Integer.< v ) )
  -> ∃[ pkh ] ∃[ v ] ∃[ c ] ∃[ r ] ∃[ s' ] ( cancel s pkh v c r ≡ ( just s' ) × (v1 s' Data.Integer.< v1 s ⊎ v2 s' Data.Integer.< v2 s ) )
-----------------------------------------
--  -> cancel s pkh c r ≡ just s' 
-- ∨ (∃ c map s' -> reqest s c map = just s')
prop5 s ⟨ pkh , ⟨ r , ⟨ +_ n , ⟨ inj₁ x , +<+ m<n ⟩ ⟩ ⟩ ⟩ = ⟨ pkh , ⟨ (+_ n) , ⟨ (curr1 s) , ⟨ r , ⟨ ((record s { omap1 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap1 s) ; v1 = (v1 s) Data.Integer.- (+_ n) ; out = singleton pkh (singleton (curr1 s) (+_ n)) })) , ⟨ lemmaCUR1 s n pkh r x m<n , inj₁ (lemminus (v1 s) n (+<+ m<n)) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
prop5 s ⟨ pkh , ⟨ r , ⟨ +_ n , ⟨ inj₂ y , +<+ m<n ⟩ ⟩ ⟩ ⟩ = ⟨ pkh , ⟨ (+_ n) , ⟨ (curr2 s) , ⟨ r , ⟨ ((record s { omap2 = insert r (singleton pkh (Data.Integer.- (+ n))) (omap2 s) ; v2 = (v2 s) Data.Integer.- (+_ n) ; out = singleton pkh (singleton (curr2 s) (+_ n)) })) , ⟨ lemmaCUR2 s n pkh r y m<n , inj₂ (lemminus (v2 s) n (+<+ m<n)) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


eqLemma : ∀ {a b c : Currency} -> a ≡ b -> a ≡ c -> b ≡ c
eqLemma ab ac rewrite ac = sym ab

postulate
  mapLemma : ∀ {map : Map ℚ (Map String ℤ)} {r : ℚ} {pkh : String} {v : ℤ} -> sum (sum (insert r (singleton pkh v) map)) ≡ sum (sum map) Data.Integer.+ v 


sumLemma : ∀ {map : Map ℚ (Map String ℤ)} {r : ℚ} {pkh : String} {x v : ℤ} -> sum (sum map) ≡ x -> x Data.Integer.+ v ≡ sum (sum (insert r (singleton pkh v) map))
sumLemma refl = sym mapLemma


--DaoProof
prop6 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((offer s pkh v cur r ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ ( offer s pkh v cur r ≡ nothing )
prop6 s pkh (+_ zero) cur r p1 p2 = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ (+_ zero) denominator-1 isCoprime) p1 p2 = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ +[1+ n₁ ] denominator-1 isCoprime) p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes x | yes z = ⊥-elim (pf s (eqLemma x z))
... | yes x | no t  = inj₁ ⟨ (record s { omap1 = (insert (mkℚ +[1+ n₁ ] denominator-1 isCoprime) (singleton pkh +[1+ n ]) (omap1 s)); v1 = (v1 s) Data.Integer.+ +[1+ n ] } ) , ⟨ refl , ⟨ sumLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | no y  | yes z = inj₁ ⟨ (record s { omap2 = (insert (mkℚ +[1+ n₁ ] denominator-1 isCoprime) (singleton pkh +[1+ n ]) (omap2 s)); v2 = (v2 s) Data.Integer.+ +[1+ n ] } ) , ⟨ refl , ⟨ p1 , (sumLemma (sym p2)) ⟩ ⟩ ⟩
... | no y  | no  t = inj₂ refl
prop6 s pkh +[1+ n ] cur (mkℚ (-[1+_] n₁) denominator-1 isCoprime) p1 p2 = inj₂ refl
prop6 s pkh (-[1+_] n) cur r p1 p2 = inj₂ refl



postulate
  mapMinusLemma : ∀ {map1 map2 : Map ℚ (Map String ℤ)} -> sum (sum (map1 -ᵐ map2)) ≡ sum (sum map1) Data.Integer.- sum (sum map2) 


minusMLemma : ∀ {map1 map2 : Map ℚ (Map String ℤ)} {x : ℤ} -> sum (sum map1) ≡ x -> x Data.Integer.- sum (sum map2) ≡ sum (sum (map1 -ᵐ map2))
minusMLemma refl = sym mapMinusLemma

prop7 : ∀ (s : State) (cur : Currency) (pkh : String) (map : Map ℚ (Map String ℤ))
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((request s pkh cur map ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ ( request s pkh cur map ≡ nothing )
prop7 s cur pkh map p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | map ≤?ᵐ (omap1 s) | map ≤?ᵐ (omap2 s)
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y))
... | yes _ | no _  | yes _ | _ = inj₁ ⟨ (record s { omap1 = (omap1 s) -ᵐ map ; out = compute map pkh cur (curr2 s) ; v1 = (v1 s) Data.Integer.- sum(sum map)}) , ⟨ refl , ⟨ minusMLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | yes _ | no _  | no _  | _ = inj₂ refl
... | no _  | yes _ | _ | yes _ = inj₁ ⟨ (record s { omap2 = (omap2 s) -ᵐ map ; out = compute map pkh cur (curr1 s) ; v2 = (v2 s) Data.Integer.- sum(sum map)}) , ⟨ refl , ⟨ p1 , minusMLemma (sym p2) ⟩ ⟩ ⟩
... | no _  | yes _ | _ | no _  = inj₂ refl
... | no _  | no  _ | _ | _ = inj₂ refl


prop8 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (v1 s ≡ sum (sum (omap1 s)))
  -> (v2 s ≡ sum (sum (omap2 s)))
  -> ∃[ s' ] ((cancel s pkh v cur r ≡ just s') × ((v1 s' ≡ sum (sum (omap1 s'))) × (v2 s' ≡ sum (sum (omap2 s'))))) ⊎ (cancel s pkh v cur r ≡ nothing)
prop8 s pkh (+_ zero) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = inj₂ refl
... | no  _ | yes _ = inj₂ refl
... | no  _ | no  _ = inj₂ refl
prop8 s pkh (-[1+_] n) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = inj₂ refl
... | no  _ | yes _ = inj₂ refl
... | no  _ | no  _ = inj₂ refl
prop8 s pkh +[1+ n ] cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap1 s))) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap2 s)))
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y)) 
... | yes _ | no  _ | yes _ | _ = inj₁ ⟨ (record s { omap1 = insert r (singleton pkh ( Data.Integer.- +[1+ n ] )) (omap1 s) ; v1 = (v1 s) Data.Integer.- +[1+ n ] ; out = singleton pkh (singleton cur +[1+ n ]) }) , ⟨ refl , ⟨ sumLemma (sym p1) , p2 ⟩ ⟩ ⟩
... | yes _ | no  _ | no _ | _  = inj₂ refl
... | no  _ | yes _ | _ | yes _ = inj₁ ⟨  (record s { omap2 = insert r (singleton pkh ( Data.Integer.- +[1+ n ] )) (omap2 s) ; v2 = (v2 s) Data.Integer.- +[1+ n ] ; out = singleton pkh (singleton cur +[1+ n ]) }) , ⟨ refl , ⟨ p1 , sumLemma (sym p2) ⟩ ⟩ ⟩
... | no  _ | yes _ | _ | no _  = inj₂ refl
... | no  _ | no  _ | _ | _ = inj₂ refl



nonsenseLemma : ∀ {a : ℤ} {n : ℕ} -> +[1+ n ] Data.Integer.≤ a -> a ≡ +0 -> ⊥
nonsenseLemma (+≤+ ()) refl

-- Authorized Access
prop9 : ∀ (s : State) (pkh : String) (v : ℤ) (cur : Currency) (r : ℚ)
  -> (query pkh (query r (omap1 s))) ≡ 0ℤ
  -> (query pkh (query r (omap2 s))) ≡ 0ℤ
  -> (cancel s pkh v cur r ≡ nothing)
prop9 s pkh (+_ zero) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = refl
... | no  _ | yes _ = refl
... | no  _ | no  _ = refl
prop9 s pkh (-[1+_] n) cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s)
... | yes _ | _ = refl 
... | no  _ | yes _ = refl 
... | no  _ | no  _ = refl 
prop9 s pkh +[1+ n ] cur r p1 p2 with cur c=? (curr1 s) | cur c=? (curr2 s) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap1 s))) | +[1+ n ] Data.Integer.≤? (query pkh (query r (omap2 s)))
... | yes x | yes y | _ | _ = ⊥-elim (pf s (eqLemma x y)) 
... | yes x | no  y | yes z | _ = ⊥-elim (nonsenseLemma z p1)
... | yes _ | no  _ | no _ | _  = refl
... | no  x | yes y | _ | yes z = ⊥-elim (nonsenseLemma z p2)
... | no  _ | yes _ | _ | no _  = refl
... | no  _ | no  _ | _ | _ = refl






```
