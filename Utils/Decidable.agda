

module Utils.Decidable where

open import Data.Nat
open import Data.Char
open import Data.String
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable hiding (True; False)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function
import Level as L

_=>_ : ∀ {α β} → Set α → Set β → Set (α L.⊔ β)
Dict => A = ⦃ _ : Dict ⦄ → A
infixr 5 _=>_

record Decidable {a}(A : Set a) : Set a where
  constructor rec
  field
    decide : Dec A    

DecRel : ∀ {a b}{A : Set a}{B : Set b} → (A → B → Set (a L.⊔ b)) → Set (a L.⊔ b)
DecRel Rel = ∀ {x y} → Decidable (Rel x y)

DecEq : ∀ {a} → Set a → Set a
DecEq A = DecRel (_≡_ {_} {A})

_⁇ : ∀ {a} A → Decidable {a} A => Dec A
_⁇ A ⦃ dict ⦄ = Decidable.decide dict

_≡⁇_ : ∀ {a A} → DecEq {a} A => ((x y : A) → Dec (x ≡ y))
x ≡⁇ y = (x ≡ y) ⁇

True : ∀ {a} A → Decidable {a} A => Set
True A = T ⌊ A ⁇ ⌋

F : Bool → Set
F = T ∘ not

False : ∀ {a} A → Decidable {a} A => Set
False A = F ⌊ A ⁇ ⌋

_≤⁇_ : ∀ a b → Dec (a ≤ b)
_≤⁇_ = _≤?_

_<⁇_ : ∀ a b → Dec (a < b)
a <⁇ b = suc a ≤⁇ b

module _ where
  open import Data.Nat.Properties
  _≤′⁇_ : ∀ a b → Dec (a ≤′ b)
  _≤′⁇_ a b with a ≤⁇ b
  ... | yes p = yes (≤⇒≤′ p)
  ... | no  p = no (p ∘ ≤′⇒≤)

_<′⁇_ : ∀ a b → Dec (a <′ b)
a <′⁇ b = suc a ≤′⁇ b


instance
  DecEqBool : DecEq Bool
  DecEqBool = rec (_ Data.Bool.≟ _)

instance
  DecEqChar : DecEq Char
  DecEqChar = rec (_ Data.Char.≟ _)

module _ where
  open import Data.Fin
  open import Data.Fin.Properties
  
  instance
    DecEqFin : ∀ {n} → DecEq (Fin n)
    DecEqFin = rec (_ Data.Fin.Properties.≟ _)

instance
  DecEqℕ : DecEq ℕ
  DecEqℕ = rec (_ Data.Nat.≟ _)

instance
  DecEqString : DecEq String
  DecEqString = rec (_ Data.String.≟ _)

instance
  Decℕ≤ : DecRel _≤_
  Decℕ≤ = rec (_ ≤⁇ _)
  
instance
  Decℕ≤′ : DecRel _≤′_
  Decℕ≤′ = rec (_ ≤′⁇ _)
  
  
-- Conversions between decidable / boolean 
--------------------------------------------------

T→∧ : ∀ {a b} → T (a ∧ b) → T a × T b
T→∧ {true} {true} x = _
T→∧ {true} {false} ()
T→∧ {false} ()

∧→T : ∀ {a b} → T a → T b → T (a ∧ b)
∧→T {true} {true} p1 p2 = _
∧→T {true} {false} p1 ()
∧→T {false} () p2

F-not-elim : ∀ {b} → F (not b) → T b
F-not-elim {true} p = p
F-not-elim {false} p = p

F-not-add : ∀ {b} → T b → F (not b)
F-not-add {true}  p = p
F-not-add {false} p = p

F-not-≡ : ∀ b → T b ≡ F (not b)
F-not-≡ true  = refl
F-not-≡ false = refl

TrueA→A : ∀ {a A}⦃ _ : Decidable {a} A ⦄ → True A → A
TrueA→A = toWitness

FalseA→¬A : ∀ {a A}⦃ _ : Decidable {a} A ⦄ → False A → ¬ A
FalseA→¬A = toWitnessFalse

A→TrueA : ∀ {a A}⦃ _ : Decidable {a} A ⦄ → A → True A
A→TrueA = fromWitness

¬A→FalseA : ∀ {a A}⦃ _ : Decidable {a} A ⦄ → ¬ A → False A
¬A→FalseA = fromWitnessFalse

T→≡true : ∀ {b} → T b → b ≡ true
T→≡true {true} p = refl
T→≡true {false} ()

≡true→T : ∀ {b} → b ≡ true → T b
≡true→T {true} p = _
≡true→T {false} ()

≡false→F : ∀ {b} → b ≡ false → F b
≡false→F {true} ()
≡false→F {false} p = _

F→≡false : ∀ {b} → F b → b ≡ false
F→≡false {true} ()
F→≡false {false} p = refl

A→≡true : ∀ {a A}{Q : Dec {a} A} → A → ⌊ Q ⌋ ≡ true
A→≡true = T→≡true ∘ fromWitness

¬A→≡false : ∀ {a A}{Q : Dec {a} A} → ¬ A → ⌊ Q ⌋ ≡ false
¬A→≡false = F→≡false ∘ fromWitnessFalse

≡true→A : ∀ {a A}{Q : Dec {a} A} → ⌊ Q ⌋ ≡ true → A
≡true→A = toWitness ∘ ≡true→T

≡false→¬A : ∀ {a A}{Q : Dec {a} A} → ⌊ Q ⌋ ≡ false → ¬ A
≡false→¬A = toWitnessFalse ∘ ≡false→F


-----------------------------------------------------------

instance
  Dec¬ :
    ∀ {α A}
    →  Decidable {α} A
    => Decidable (¬ A)
    
  Dec¬ {_}{A} = rec dec¬ where
  
    dec¬ : Dec (¬ A)
    dec¬ with A ⁇
    ... | yes p = no (λ z → z p)
    ... | no ¬p = yes ¬p

instance
  Dec⊎ : 
    ∀ {α β A B}
    →  Decidable {α} A
    => Decidable {β} B
    => Decidable (A ⊎ B)
    
  Dec⊎ {_}{_}{A}{B} = rec dec⊎ where
  
    dec⊎ : Dec (A ⊎ B)
    dec⊎ with A ⁇ | B ⁇
    ... | yes p   | _      = yes (inj₁ p)
    ... | _       | yes p  = yes (inj₂ p)
    ... | no ¬p₁  | no ¬p₂ = no [ ¬p₁ , ¬p₂ ]′

instance
  Dec× :
    ∀ {α β A B}
    →  Decidable {α} A
    => Decidable {β} B
    => Decidable (A × B)
    
  Dec× {_}{_}{A}{B} = rec dec× where
  
    dec× : Dec (A × B)
    dec× with A ⁇ | B ⁇
    ... | yes p | yes p₁ = yes (p , p₁)
    ... | yes p | no ¬p  = no (¬p ∘ proj₂)
    ... | no ¬p | _      = no (¬p ∘ proj₁)

