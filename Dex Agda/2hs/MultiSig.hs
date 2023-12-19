module MultiSig where

import Numeric.Natural (Natural)

type PubKeyHash = String

data State = Holding
           | Collecting Integer PubKeyHash Integer [PubKeyHash]

data Input = Propose Integer PubKeyHash Integer
           | Add PubKeyHash
           | Pay
           | Cancel

type Outputs = [(Natural, String)]

(¸) :: PubKeyHash -> [PubKeyHash] -> Bool
pkh ¸ [] = False
pkh ¸ (x : l') = x == pkh || (pkh ¸ l')

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

agdaValidator ::
              [PubKeyHash] ->
                State -> Input -> Interval -> Outputs -> State -> Bool
agdaValidator l s i t o s'
  = case s of
        Collecting v pkh d sigs -> case i of
                                       Propose _ _ _ -> False
                                       Add sig -> case s' of
                                                      Holding -> False
                                                      Collecting v' pkh' d' sigs' -> checkSigned sig
                                                                                       &&
                                                                                       (sig ¸ l) &&
                                                                                         v == v' &&
                                                                                           pkh ==
                                                                                             pkh'
                                                                                             &&
                                                                                             d == d'
                                                                                               &&
                                                                                               sigs'
                                                                                                 ==
                                                                                                 insert
                                                                                                   sig
                                                                                                   sigs
                                       Pay -> case s' of
                                                  Holding -> checkPayment pkh v o
                                                  Collecting _ _ _ _ -> False
                                       Cancel -> case s' of
                                                     Holding -> before d t
                                                     Collecting _ _ _ _ -> False
        Holding -> case i of
                       Propose v pkh d -> case s' of
                                              Holding -> False
                                              Collecting v' pkh' d' sigs' -> v == v' &&
                                                                               pkh == pkh' &&
                                                                                 d == d' &&
                                                                                   sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False

