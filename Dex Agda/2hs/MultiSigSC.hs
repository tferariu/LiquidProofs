module MultiSigSC where

import Numeric.Natural (Natural)

data Datum = Holding ThreadToken
           | Collecting ThreadToken Integer PubKeyHash Integer [PubKeyHash]

data Redeemer = Propose Integer PubKeyHash Integer
              | Add PubKeyHash
              | Pay
              | Cancel

(¸) :: PubKeyHash -> [PubKeyHash] -> Bool
pkh ¸ [] = False
pkh ¸ (x : l') = x == pkh || (pkh ¸ l')

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

count :: [PubKeyHash] -> Natural
count [] = 0
count (x : l) = 1 + count l

agdaValidator ::
              Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator param dat red ctx
  = case dat of
        Collecting tok v pkh d sigs -> checkToken tok ctx &&
                                         case red of
                                             Propose _ _ _ -> False
                                             Add sig -> case oDat ctx of
                                                            Holding _ -> False
                                                            Collecting tok' v' pkh' d'
                                                              sigs' -> checkSigned sig &&
                                                                         (sig ¸ authSigs param) &&
                                                                           tok == tok' &&
                                                                             v == v' &&
                                                                               pkh == pkh' &&
                                                                                 d == d' &&
                                                                                   sigs' ==
                                                                                     insert sig sigs
                                             Pay -> case oDat ctx of
                                                        Holding tok' -> tok == tok' &&
                                                                          count sigs >= nr param &&
                                                                            checkPayment pkh v
                                                                              (scriptContextTxInfo
                                                                                 ctx)
                                                        Collecting _ _ _ _ _ -> False
                                             Cancel -> case oDat ctx of
                                                           Holding tok' -> tok == tok' &&
                                                                             after d
                                                                               (scriptContextTxInfo
                                                                                  ctx)
                                                           Collecting _ _ _ _ _ -> False
        Holding tok -> checkToken tok ctx &&
                         case red of
                             Propose v pkh d -> case oDat ctx of
                                                    Holding _ -> False
                                                    Collecting tok' v' pkh' d' sigs' -> tok == tok'
                                                                                          &&
                                                                                          v == v' &&
                                                                                            pkh ==
                                                                                              pkh'
                                                                                              &&
                                                                                              d ==
                                                                                                d'
                                                                                                &&
                                                                                                sigs'
                                                                                                  ==
                                                                                                  []
                             Add _ -> False
                             Pay -> False
                             Cancel -> False

