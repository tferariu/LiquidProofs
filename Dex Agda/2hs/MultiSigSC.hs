module MultiSigSC where

data Datum = Holding
           | Collecting Value PubKeyHash Deadline [PubKeyHash]

data Redeemer = Propose Value PubKeyHash Deadline
              | Add PubKeyHash
              | Pay
              | Cancel

(∈) :: PubKeyHash -> [PubKeyHash] -> Bool
pkh ∈ [] = False
pkh ∈ (x : l') = x == pkh || (pkh ∈ l')

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

count :: [PubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l

data Params = Params{authSigs :: [PubKeyHash], nr :: Integer}

agdaValidator ::
              Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator param dat red ctx
  = case dat of
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> checkSigned sig &&
                                                    (sig ∈ authSigs param) &&
                                                      case oDat ctx of
                                                          Holding -> False
                                                          Collecting v' pkh' d' sigs' -> v == v' &&
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
                                       Pay -> count sigs >= nr param &&
                                                case oDat ctx of
                                                    Holding -> checkPayment pkh v
                                                                 (scriptContextTxInfo ctx)
                                                    Collecting _ _ _ _ -> False
                                       Cancel -> case oDat ctx of
                                                     Holding -> expired d (scriptContextTxInfo ctx)
                                                     Collecting _ _ _ _ -> False
        Holding -> case red of
                       Propose v pkh d -> oldValue ctx >= v &&
                                            case oDat ctx of
                                                Holding -> False
                                                Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                 pkh == pkh' &&
                                                                                   d == d' &&
                                                                                     sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False

