
module Basic.DeBruijnVars.AST where

import Data.Bool as Bool using (not)
open import Data.Bool hiding (not; if_then_else_)
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat 
open import Data.Vec 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Utils.Decidable

data Ty : Set where
  bool nat : Ty

-- Interpretation of types
⟦_⟧ᵗ : Ty → Set
⟦ nat  ⟧ᵗ = ℕ
⟦ bool ⟧ᵗ = Bool

State : ℕ → Set
State = Vec ℕ 

data Exp (n : ℕ) : Ty → Set where
  lit         : ℕ → Exp n nat
  add mul sub : Exp n nat → Exp n nat → Exp n nat
  var         : Fin n → Exp n nat
  tt ff       : Exp n bool
  eq lte lt   : Exp n nat → Exp n nat → Exp n bool
  and         : Exp n bool → Exp n bool → Exp n bool
  not         : Exp n bool → Exp n bool

-- Statements
infixr 5 _:=_
infixr 4 _,_
data St (n : ℕ) : Set where
  _:=_          : Fin n → Exp n nat → St n
  skip          : St n
  _,_           : St n → St n → St n
  if_then_else_ : Exp n bool → St n → St n → St n
  while_do_     : Exp n bool → St n → St n

-- (total) semantics of expressions
⟦_⟧ᵉ : ∀ {n t} → Exp n t → State n → ⟦ t ⟧ᵗ
⟦ lit x   ⟧ᵉ s = x
⟦ add a b ⟧ᵉ s = ⟦ a ⟧ᵉ s + ⟦ b ⟧ᵉ s
⟦ mul a b ⟧ᵉ s = ⟦ a ⟧ᵉ s * ⟦ b ⟧ᵉ s
⟦ sub a b ⟧ᵉ s = ⟦ a ⟧ᵉ s ∸ ⟦ b ⟧ᵉ s
⟦ var x   ⟧ᵉ s = lookup x s
⟦ tt      ⟧ᵉ s = true
⟦ ff      ⟧ᵉ s = false
⟦ eq  a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s ≡⁇ ⟦ b ⟧ᵉ s ⌋
⟦ lte a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s ≤⁇ ⟦ b ⟧ᵉ s ⌋
⟦ lt  a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s <⁇ ⟦ b ⟧ᵉ s ⌋
⟦ and a b ⟧ᵉ s =   ⟦ a ⟧ᵉ s ∧  ⟦ b ⟧ᵉ s 
⟦ not e   ⟧ᵉ s = Bool.not (⟦ e ⟧ᵉ s)

  
