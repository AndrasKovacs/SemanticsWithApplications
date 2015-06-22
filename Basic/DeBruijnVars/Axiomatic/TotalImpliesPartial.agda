
module Basic.DeBruijnVars.Axiomatic.TotalImpliesPartial where

open import Basic.DeBruijnVars.AST
open import Basic.DeBruijnVars.BigStep
open import Basic.DeBruijnVars.Axiomatic.Total as T
  renaming (〈_〉_〈_〉 to total〈_〉_〈_〉) 
open import Basic.DeBruijnVars.Axiomatic.Partial as P
  renaming (〈_〉_〈_〉 to partial〈_〉_〈_〉) hiding (_==>_; _∧_)

open import Function
open import Data.Product

P==>wp→P==>wlp : ∀{n S}{P Q : State n → Set} → (P ==> wp S Q) → (P ==> wlp S Q)
P==>wp→P==>wlp pwp ps runS with pwp ps
... | _ , runS' , qs' rewrite deterministic runS runS' = qs'

total→partial : ∀ {n S}{P Q : State n → Set} → total〈 P 〉 S 〈 Q 〉 → partial〈 P 〉 S 〈 Q 〉
total→partial = P.complete _ ∘ P==>wp→P==>wlp ∘ T.sound
