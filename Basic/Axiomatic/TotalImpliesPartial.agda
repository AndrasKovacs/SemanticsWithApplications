
module Basic.Axiomatic.TotalImpliesPartial where

open import Basic.AST
open import Basic.BigStep
open import Basic.Axiomatic.Total as T
  renaming (〈_〉_〈_〉 to total〈_〉_〈_〉) 
open import Basic.Axiomatic.Partial as P
  renaming (〈_〉_〈_〉 to partial〈_〉_〈_〉) hiding (_==>_; _∧_)

open import Function
open import Data.Product

{-
The proof that total correctness implies partial correctness (exercise 6.33)
is fortunately really simple.

We already proved soundness and completeness for both systems, so instead of
trying to construct the partial proof directly from the total proof, we can
just take a detour and prove the analoguous implication about the *validity*
of triples.
-}

{-
The total validity of Hoare triples implies partial validity, if the language semantics is
deterministic. 
-}
P==>wp→P==>wlp : ∀{n S}{P Q : State n → Set} → (P ==> wp S Q) → (P ==> wlp S Q)
P==>wp→P==>wlp pwp ps runS with pwp ps
... | _ , runS' , qs' rewrite deterministic runS runS' = qs'

{- And now we just do an excursion to semantics-land and then back -}
total→partial : ∀ {n S}{P Q : State n → Set} → total〈 P 〉 S 〈 Q 〉 → partial〈 P 〉 S 〈 Q 〉
total→partial = P.complete _ ∘ P==>wp→P==>wlp ∘ T.sound
