module MultiSig where

import Numeric.Natural (Natural)

type Deadline = Natural

data Label = Holding
           | Collecting Value PubKeyHash Deadline [PubKeyHash]

type Datum = (AssetClass, Label)

data Input = Propose Value PubKeyHash Deadline
           | Add PubKeyHash
           | Pay
           | Cancel
           | Close

data Params = Params{authSigs :: [PubKeyHash], nr :: Natural,
                     maxWait :: Deadline}

query :: PubKeyHash -> [PubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || query pkh l'

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if pkh == x then x : l' else x : insert pkh l'

agdaValidator :: Params -> Datum -> Input -> ScriptContext -> Bool
agdaValidator param (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case _,_,_ (checkTokenOut tok ctx) lab red of
          _,_,_ True Holding (Propose v pkh d) -> newValue ctx ==
                                                    oldValue ctx
                                                    &&
                                                    geq (oldValue ctx) v &&
                                                      geq v minValue &&
                                                        notTooLate param d ctx &&
                                                          continuing ctx &&
                                                            case newDatum ctx of
                                                                (tok', Holding) -> False
                                                                (tok',
                                                                 Collecting v' pkh' d'
                                                                   sigs') -> v == v' &&
                                                                               pkh == pkh' &&
                                                                                 d == d' &&
                                                                                   sigs' == [] &&
                                                                                     tok == tok'
          _,_,_ True (Collecting v pkh d sigs) (Add sig) -> newValue ctx ==
                                                              oldValue ctx
                                                              &&
                                                              checkSigned sig ctx &&
                                                                query sig (authSigs param) &&
                                                                  continuing ctx &&
                                                                    case newDatum ctx of
                                                                        (tok', Holding) -> False
                                                                        (tok',
                                                                         Collecting v' pkh' d'
                                                                           sigs') -> v == v' &&
                                                                                       pkh == pkh'
                                                                                         &&
                                                                                         d == d' &&
                                                                                           sigs' ==
                                                                                             insert
                                                                                               sig
                                                                                               sigs
                                                                                             &&
                                                                                             tok ==
                                                                                               tok'
          _,_,_ True (Collecting v pkh d sigs) Pay -> lengthNat sigs >=
                                                        nr param
                                                        &&
                                                        continuing ctx &&
                                                          case newDatum ctx of
                                                              (tok', Holding) -> checkPayment pkh v
                                                                                   ctx
                                                                                   &&
                                                                                   oldValue ctx ==
                                                                                     newValue ctx +
                                                                                       v
                                                                                     && tok == tok'
                                                              (tok',
                                                               Collecting v' pkh' d' sigs') -> False
          _,_,_ True (Collecting v pkh d sigs) Cancel -> newValue ctx ==
                                                           oldValue ctx
                                                           &&
                                                           continuing ctx &&
                                                             case newDatum ctx of
                                                                 (tok', Holding) -> expired d ctx &&
                                                                                      tok == tok'
                                                                 (tok',
                                                                  Collecting v' pkh' d'
                                                                    sigs') -> False
          _,_,_ False Holding Close -> gt minValue (oldValue ctx) &&
                                         not (continuing ctx)
          _ -> False

agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx
  = if amt == 1 then
      continuingAddr addr ctx && isInitial addr oref ctx else
      if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

