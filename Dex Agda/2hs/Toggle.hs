module Toggle where

data Shape = Circle
           | Square

data Input = Toggle
           | Other

toggled :: Shape -> Shape -> Bool
toggled Circle Circle = False
toggled Circle Square = True
toggled Square Circle = True
toggled Square Square = False

toggle :: Shape -> Input -> Shape -> Bool
toggle s i s'
  = case i of
        Other -> False
        Toggle -> toggled s s'

