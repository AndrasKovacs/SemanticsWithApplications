

module Basic.Compiler.CorrectTo where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Basic.Compiler.Code
open import Basic.AST
open import Basic.BigStep
open import Utils.Decidable

𝓒-correct-to :
  ∀ {n}{S : St n}{s s'} 
  → ⟨ S , s ⟩⟱ s' → ⟨ 𝓒⟦ S ⟧ˢ , [] , s ⟩▷*⟨ [] , [] , s' ⟩

𝓒-correct-to (ass {_}{x}{a}) = 𝓒-Exp-nat a ▷*<> STORE x ∷ done
𝓒-correct-to skip = NOOP ∷ done
𝓒-correct-to (a , b) = 𝓒-correct-to a ▷*<> 𝓒-correct-to b

𝓒-correct-to (if-true {s = s}{b = b} x p) with 𝓒-Exp-bool {e = []}{s = s} b
... | condition rewrite T→≡true x = 
  condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p

𝓒-correct-to (if-false {s = s}{b = b} x p) with 𝓒-Exp-bool {e = []}{s = s} b
... | condition rewrite F→≡false x = 
  condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p

𝓒-correct-to (while-true {s}{b = b} x p k) with 𝓒-Exp-bool {e = []}{s = s} b
... | condition rewrite T→≡true x = 
  LOOP ∷ condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p ▷*<> 𝓒-correct-to k

𝓒-correct-to (while-false {s}{S}{b} x) with 𝓒-Exp-bool {e = []}{s = s} b
... | condition rewrite F→≡false x = 
  LOOP ∷ condition ▷*<> BRANCH-[] ∷ NOOP ∷ done
