module MultiSig where

type Deadline = Integer

data Label = Holding
           | Collecting Value PubKeyHash Deadline [PubKeyHash]

data Input = Propose Value PubKeyHash Deadline
           | Add PubKeyHash
           | Pay
           | Cancel

query :: PubKeyHash -> [PubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || query pkh l'

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

count :: [PubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l

data Params = Params{authSigs :: [PubKeyHash], nr :: Integer}

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx
  = case dat of
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> checkSigned sig ctx &&
                                                    query sig (authSigs param) &&
                                                      case newLabel ctx of
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
                                                case newLabel ctx of
                                                    Holding -> checkPayment pkh v ctx &&
                                                                 oldValue ctx == newValue ctx + v
                                                    Collecting _ _ _ _ -> False
                                       Cancel -> case newLabel ctx of
                                                     Holding -> expired d ctx
                                                     Collecting _ _ _ _ -> False
        Holding -> case red of
                       Propose v pkh d -> oldValue ctx >= v &&
                                            case newLabel ctx of
                                                Holding -> False
                                                Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                 pkh == pkh' &&
                                                                                   d == d' &&
                                                                                     sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False

