module MultiSigSC where

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
agdaValidator param oldLabel red ctx
  = case oldLabel of
        Collecting v pkh d sigs -> True
        Holding -> case red of
                       Propose v pkh d -> case newLabel ctx of
                                              Holding -> False
                                              Collecting v' pkh' d' sigs' -> True
                       Add _ -> False
                       Pay -> False
                       Cancel -> False

