module Basic.EqvSemantics where

open import Data.Vec 
open import Function
open import Data.Product
open import Data.Maybe

open import Utils.Decidable
open import Basic.AST
open import Basic.BigStep
open import Basic.SmallStep

{-

Equivalence of big step and small step semantics (Theorem 2.26 in the book).

The main difference from the book is the proof for the

  ⟨ S , s ⟩ k ⟶ s' → ⟨ S , s ⟩⟱ s'

direction. The book does case analysis directly on the transition the
"cons" case of the computation sequence, and then uses Lemma 2.19 (which
I named "seq-split" in the SmallStep module) to split the sequence into
two parts corresponding to the two parts of a composite statement.

The problem with this is that it relies on the usual well-ordering of natural
numbers, and it's not immediately structurally recursive. In other words, it relies
on the fact that the resulting parts of a split sequence are both shorter than the
original sequence. 

However, the book omits the proof that no splitting ever produces computation
sequences of length zero. This is required for the recursion to be well-founded,
and in Agda we would indeed have to prove this too.

It's simpler to use "prepend". It essentially digs down to the leftmost "edge" of
a small-step transition, and composes it with a big-step derivation. It's evidently
structurally recursive and I find it a bit neater than the proof in the book. 

-}

Small≡Big : ∀ {n}{S : St n}{s s'} → ⟨ S , s ⟩⟱ s' ⇔ ⟨ S , s ⟩⟶* s'
Small≡Big {n} = to , from ∘ proj₂
  where
  to : ∀ {S s s'} → ⟨ S , s ⟩⟱ s' → ⟨ S , s ⟩⟶* s'
  to ass                 = , ass stop
  to skip                = , skip stop
  to (A , B)             = , append (proj₂ $ to A) (proj₂ $ to B)
  to (if-true x p)       = , if-true x ∷ proj₂ (to p)
  to (if-false x p)      = , if-false x ∷ proj₂ (to p)
  to (while-true x p p₁) = , while ∷ if-true x ∷ append (proj₂ $ to p) (proj₂ $ to p₁)
  to (while-false x)     = , while ∷ if-false x ∷ skip stop

  mutual
    prepend : 
      ∀ {s₁ s₂ s₃}{S₁ S₂ : St n}
      → ⟨ S₁ , s₁ ⟩⟶⟨ S₂ , s₂ ⟩
      → ⟨ S₂ , s₂ ⟩⟱ s₃ 
      → ⟨ S₁ , s₁ ⟩⟱ s₃
    prepend (p1 ◄) (p2 , p3)            = prepend p1 p2 , p3
    prepend (x ∙) p2                    = from (x stop) , p2
    prepend (if-true x) p2              = if-true x p2
    prepend (if-false x) p2             = if-false x p2
    prepend while (if-true x (p2 , p3)) = while-true x p2 p3
    prepend while (if-false x skip)     = while-false x       
  
    from : ∀ {k S s s'} → ⟨ S , s ⟩ k ⟶ s' → ⟨ S , s ⟩⟱ s'
    from (ass stop)  = ass
    from (skip stop) = skip
    from (x ∷ p)     = prepend x (from p)







