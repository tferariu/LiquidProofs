module Toggle where

open import Haskell.Prelude
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

data Shape : Set where
  Circle : Shape
  Square : Shape

{-# COMPILE AGDA2HS Shape #-}

data Input : Set where
  Toggle : Input
  Other  : Input

{-# COMPILE AGDA2HS Input #-}

toggled : Shape -> Shape -> Bool
toggled Circle Circle = False
toggled Circle Square = True
toggled Square Circle = True
toggled Square Square = False
 
{-# COMPILE AGDA2HS toggled #-}

toggle : Shape -> Input -> Shape -> Bool
toggle s i s' = case i of λ where
  Other -> False
  Toggle -> toggled s s'

{-# COMPILE AGDA2HS toggle #-}


prop1 : ∀ (s s' : Shape) -> toggle s Other s' ≡ False
prop1 s s' = refl

prop2 : ∀ (s s' : Shape) (i : Input) -> toggle s i s' ≡ True -> toggled s s' ≡ True
prop2 Circle Square i pf = refl
prop2 Circle Circle Toggle ()
prop2 Circle Circle Other pf = pf
prop2 Square Square Toggle ()
prop2 Square Square Other pf = pf
prop2 Square Circle i pf = refl


prop3 : ∀ (s : Shape) -> ∃[ i ] ∃[ s' ] (toggle s i s' ≡ True)
prop3 Circle = ⟨ Toggle , ⟨ Square , refl ⟩ ⟩
prop3 Square = ⟨ Toggle , ⟨ Circle , refl ⟩ ⟩
