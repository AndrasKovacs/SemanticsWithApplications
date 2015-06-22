module Basic.DeBruijnVars.Compiler.Machine where

open import Basic.DeBruijnVars.AST
open import Basic.DeBruijnVars.BigStep
open import Basic.DeBruijnVars.Compiler.Code

open import Utils.Decidable
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.List
open import Data.Bool
open import Data.Nat

step : ∀ {n} (c : Code n) e s → Dec (∃₂ λ c' e' -> ∃ λ s' → ⟨ c , e , s ⟩▷⟨ c' , e' , s' ⟩)
step [] e s = no (λ {(c' , e' , s' , ())})
step (PUSH x ∷ c) e s = yes (c , nat x ∷ e , s , PUSH x)
step (FETCH x ∷ c) e s = yes (c , nat _ ∷ e , s , FETCH x)
step (STORE x ∷ c) [] s = no (λ {(c' , e' , s' , ())})
step (STORE x ∷ c) (nat x₁ ∷ e) s = yes (c , e , _ , STORE x)
step (STORE x ∷ c) (bool x₁ ∷ e) s = no (λ {(c' , e' , s' , ())})
step (ADD ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (ADD ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (ADD ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , nat _ ∷ e , s , ADD x x₁)
step (ADD ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (ADD ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (MUL ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (MUL ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (MUL ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , nat _ ∷ e , s , MUL x x₁)
step (MUL ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (MUL ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (SUB ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (SUB ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (SUB ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , nat _ ∷ e , s , SUB x x₁)
step (SUB ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (SUB ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (TRUE ∷ c) e s = yes (c  , bool true ∷ e , s , TRUE)
step (FALSE ∷ c) e s = yes (c , bool false ∷ e , s , FALSE)

step (EQ ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (EQ ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (EQ ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , bool ⌊ x ≡⁇ x₁ ⌋ ∷ e , s , EQ x x₁)
step (EQ ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (EQ ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (LTE ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (LTE ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (LTE ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , bool ⌊ x ≤⁇ x₁ ⌋ ∷ e , s , LTE x x₁)
step (LTE ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (LTE ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (LT ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (LT ∷ c) (nat x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (LT ∷ c) (nat x ∷ nat x₁ ∷ e) s = yes (c , bool ⌊ x <⁇ x₁ ⌋ ∷ e , s , LT x x₁)
step (LT ∷ c) (nat x ∷ bool x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (LT ∷ c) (bool x ∷ e) s = no (λ { (c' , e' , s' , ()) })

step (AND ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (AND ∷ c) (nat x ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (AND ∷ c) (bool x ∷ []) s = no (λ { (c' , e' , s' , ()) })
step (AND ∷ c) (bool x ∷ nat x₁ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (AND ∷ c) (bool x ∷ bool x₁ ∷ e) s = yes (c , bool (x ∧ x₁) ∷ e , s , AND x x₁)

step (NOT ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (NOT ∷ c) (nat x ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (NOT ∷ c) (bool x ∷ e) s = yes (c , bool _ ∷ e , s , NOT x)
step (NOOP ∷ c) e s = yes (c , e , s , NOOP)

step (BRANCH x x₁ ∷ c) [] s = no (λ { (c' , e' , s' , ()) })
step (BRANCH x x₁ ∷ c) (nat x₂ ∷ e) s = no (λ { (c' , e' , s' , ()) })
step (BRANCH x x₁ ∷ c) (bool true ∷ e) s = yes (x ++ c , e , s , BRANCH)
step (BRANCH x x₁ ∷ c) (bool false ∷ e) s = yes (x₁ ++ c , e , s , BRANCH)

step (LOOP x x₁ ∷ c) e s = yes (x ++ BRANCH (x₁ ++ LOOP x x₁ ∷ []) (NOOP ∷ []) ∷ c , e , s , LOOP)


steps : ∀ {n} → Code n → Stack → State n → ℕ → (Code n × Stack × State n)
steps c e s zero = c , e , s
steps c e s (suc n) with step c e s
... | yes (c' , e' , s' , p) = steps c' e' s' n
... | no _ = c , e , s

trace : ∀ {n} → Code n → Stack → State n → ℕ → List (Code n × Stack × State n)
trace c e s zero = []
trace c e s (suc n) with step c e s
... | yes  (c' , e' , s' , p) = (c , e , s) ∷ trace c' e' s' n
... | no _ = (c , e , s) ∷ []
