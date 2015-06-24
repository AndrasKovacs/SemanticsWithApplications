
module Basic.Compiler.SplitCode where

open import Basic.Compiler.Code
open import Basic.AST
open import Basic.BigStep
open import Utils.Monoid

open import Data.Vec hiding (_++_; [_]; _∷ʳ_)
open import Data.Bool renaming (if_then_else_ to ifBool_then_else_)
open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Algebra
import Level as L

private
  module LM {a}{A : Set a} = Algebra.Monoid (Data.List.monoid A)

{-
Exercise 3.5

This code logically belongs to either Compiler.Code or Compiler.CorrectFrom.
It has its own module solely because it slows down typechecking for the module
it's in, which is rather annoying.
-}

▷*-split : 
  ∀ {n}{s s' : State n}{e e'} c₁ {c₂}
  → (p : ⟨ c₁ <> c₂ , e , s ⟩▷*⟨ [] , e' , s' ⟩)
  → ∃₂ λ s'' e''
  → ∃₂ λ (p1 : ⟨ c₁ , e  , s    ⟩▷*⟨ [] , e'' , s'' ⟩)
         (p2 : ⟨ c₂ , e'' , s'' ⟩▷*⟨ [] , e'  , s'  ⟩)
  → ▷*-length p1 + ▷*-length p2 ≡ ▷*-length p

▷*-split []       p = _ , _ , done , p , refl
▷*-split (.ADD ∷ cs) (ADD a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , ADD a b ∷ p1 , p2 , cong suc eqn
▷*-split (.MUL ∷ cs) (MUL a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , MUL a b ∷ p1 , p2 , cong suc eqn
▷*-split (.SUB ∷ cs) (SUB a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , SUB a b ∷ p1 , p2 , cong suc eqn
▷*-split (.EQ ∷ cs) (EQ a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , EQ a b ∷ p1 , p2 , cong suc eqn
▷*-split (.LT ∷ cs) (LT a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , LT a b ∷ p1 , p2 , cong suc eqn
▷*-split (.LTE ∷ cs) (LTE a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , LTE a b ∷ p1 , p2 , cong suc eqn
▷*-split (.AND ∷ cs) (AND a b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , AND a b ∷ p1 , p2 , cong suc eqn
▷*-split (.(PUSH n₁) ∷ cs) (PUSH n₁ ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , PUSH n₁ ∷ p1 , p2 , cong suc eqn
▷*-split (.TRUE ∷ cs) (TRUE ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , TRUE ∷ p1 , p2 , cong suc eqn
▷*-split (.FALSE ∷ cs) (FALSE ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , FALSE ∷ p1 , p2 , cong suc eqn
▷*-split (.NOT ∷ cs) (NOT b ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , NOT b ∷ p1 , p2 , cong suc eqn
▷*-split (.(FETCH x) ∷ cs) (FETCH x ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , FETCH x ∷ p1 , p2 , cong suc eqn
▷*-split (.(STORE x) ∷ cs) (STORE x ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , STORE x ∷ p1 , p2 , cong suc eqn
▷*-split (.NOOP ∷ cs) (NOOP ∷ p) with ▷*-split cs p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , NOOP ∷ p1 , p2 , cong suc eqn
▷*-split (._ ∷ cs){c₂} (BRANCH{ca}{cb}{._}{t}{e} ∷ p) 
  rewrite sym $ LM.assoc (ifBool t then ca else cb) cs c₂ 
  with ▷*-split ((ifBool t then ca else cb) <> cs) p 
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , BRANCH ∷ p1 , p2 , cong suc eqn 
▷*-split (._ ∷ cs){c₁} (LOOP{ca}{cb}{._}{e}{s} ∷ p) 
  rewrite sym $ LM.assoc ca (BRANCH (cb ∷ʳ LOOP ca cb) (NOOP ∷ []) ∷ cs) c₁
  with ▷*-split (ca <> (BRANCH (cb ∷ʳ LOOP ca cb) (NOOP ∷ []) ∷ cs)) p
... | s'' , e'' , p1 , p2 , eqn = s'' , e'' , LOOP ∷ p1 , p2 , cong suc eqn
