
-- Ad-hoc monoid typeclass module

module Utils.Monoid where

open import Data.List
open import Data.String

record Monoid {α}(A : Set α) : Set α where
  constructor rec
  field
    append   : A → A → A
    identity : A

infixr 5 _<>_
_<>_ : ∀ {α}{A : Set α} ⦃ _ : Monoid A ⦄ → A → A → A
_<>_ ⦃ dict ⦄ a b = Monoid.append dict a b

mempty : ∀ {α}{A : Set α} ⦃ _ : Monoid A ⦄ → A
mempty ⦃ dict ⦄ = Monoid.identity dict

instance
  MonoidList : ∀ {α A} → Monoid {α} (List A)
  MonoidList = rec Data.List._++_ []

  MonoidString : Monoid String
  MonoidString = rec Data.String._++_ ""
    
