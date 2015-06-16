

module Basic.DeBruijnVars.Impl where

open import Basic.DeBruijnVars.AST
open import Basic.DeBruijnVars.BigStep
open import Utils.NatOrdLemmas
open import Utils.Decidable
open import Utils.Monoid

open import Data.Fin using (Fin; #_)
open import Data.Vec hiding (_∷ʳ_; _++_; [_])
open import Data.Nat
open import Data.Bool renaming (not to notBool; if_then_else_ to ifBool_then_else)
open import Data.List hiding ([_])
open import Data.List.Properties
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Algebra
import Level as L
module LM {a A} = Algebra.Monoid (Data.List.monoid {a} A)

-- Types
------------------------------------------------------------
data StackEntry : Set where
  nat  : ℕ → StackEntry
  bool : Bool → StackEntry

nat-inj : ∀ {n m} → (StackEntry ∋ nat n) ≡ nat m → n ≡ m
nat-inj refl = refl

bool-inj : ∀ {b b'} → (StackEntry ∋ bool b) ≡ bool b' → b ≡ b'
bool-inj refl = refl

Stack : Set
Stack = List StackEntry

mutual
  data Inst (n : ℕ) : Set where
    PUSH : ℕ → Inst n
    FETCH STORE : Fin n → Inst n
    ADD MUL SUB TRUE FALSE EQ LTE LT AND NOT NOOP : Inst n
    BRANCH LOOP : Code n → Code n → Inst n
  
  Code : ℕ → Set
  Code = List ∘ Inst


-- Code semantics
------------------------------------------------------------

data ⟨_,_,_⟩▷⟨_,_,_⟩ {n} : Code n → Stack → State n → Code n → Stack → State n → Set where

  PUSH : 
                    ∀ n {c e s}
    → --------------------------------------------
      ⟨ PUSH n ∷ c , e , s ⟩▷⟨ c , nat n ∷ e , s ⟩

  ADD :
                              ∀ a b {c e s}
    → ---------------------------------------------------------------
      ⟨ ADD ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , nat (a + b) ∷ e , s ⟩

  MUL :
                              ∀ a b {c e s}
    → ----------------------------------------------------------------
      ⟨ MUL ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , nat (a * b) ∷ e , s ⟩

  SUB :
                              ∀ a b {c e s}
    → ----------------------------------------------------------------
      ⟨ SUB ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , nat (a ∸ b) ∷ e , s ⟩

  TRUE :
                         ∀ {c e s}
    → -----------------------------------------------
      ⟨ TRUE ∷ c , e , s ⟩▷⟨ c , bool true ∷ e , s ⟩

  FALSE :
                         ∀ {c e s}
    → ------------------------------------------------
      ⟨ FALSE ∷ c , e , s ⟩▷⟨ c , bool false ∷ e , s ⟩

  EQ :
                               ∀ a b {c e s}
    → -------------------------------------------------------------------
      ⟨ EQ ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , bool ⌊ a ≡⁇ b ⌋ ∷ e , s ⟩

  LT :
                               ∀ a b {c e s}
    → -------------------------------------------------------------------
      ⟨ LT ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , bool ⌊ a <⁇ b ⌋ ∷ e , s ⟩

  LTE :
                               ∀ a b {c e s}
    → --------------------------------------------------------------------
      ⟨ LTE ∷ c , nat a ∷ nat b ∷ e , s ⟩▷⟨ c , bool ⌊ a ≤⁇ b ⌋ ∷ e , s ⟩

  AND :
                               ∀ a b {c e s}
    → -------------------------------------------------------------------
      ⟨ AND ∷ c , bool a ∷ bool b ∷ e , s ⟩▷⟨ c , bool (a ∧ b) ∷ e , s ⟩

  NOT :
                             ∀ b {c e s}
    → -----------------------------------------------------------
      ⟨ NOT ∷ c , bool b ∷ e , s ⟩▷⟨ c , bool (notBool b) ∷ e , s ⟩

  FETCH :
                             ∀ x {c e s}  
    → ---------------------------------------------------------
      ⟨ FETCH x ∷ c , e , s ⟩▷⟨ c , nat (lookup x s) ∷ e , s ⟩

  STORE :
                         ∀ x {n c e s}  
    → ------------------------------------------------------
      ⟨ STORE x ∷ c , nat n ∷ e , s ⟩▷⟨ c , e , s [ x ]≔ n ⟩

  BRANCH :
       ∀ {c₁ c₂ c t e s} → let c' = (ifBool t then c₁ else c₂) <> c in
      --------------------------------------------------------------
          ⟨ BRANCH c₁ c₂ ∷ c , bool t ∷ e , s ⟩▷⟨ c' , e , s ⟩

  NOOP :
                   ∀ {c e s}
    → ------------------------------------
       ⟨ NOOP ∷ c , e , s ⟩▷⟨ c , e , s ⟩

  LOOP :
        ∀ {c₁ c₂ c e s} → let c' = c₁ <> BRANCH (c₂ ∷ʳ LOOP c₁ c₂ ) (NOOP ∷ []) ∷ c in
      -----------------------------------------------------------------------------------
                     ⟨ LOOP c₁ c₂ ∷ c , e , s ⟩▷⟨ c' , e , s ⟩


-- Computation sequences
------------------------------------------------------------

infixr 5 _∷_
data ⟨_,_,_⟩▷*⟨_,_,_⟩ {n} : Code n → Stack → State n → Code n → Stack → State n → Set where

  done : 
                 ∀ {e s}
    → ---------------------------------
      ⟨ [] , e , s ⟩▷*⟨ [] , e , s ⟩

  stuck : 
       ∀ {c cs e s} → (∀ c' e' s' → ¬ ⟨ c ∷ cs , e , s ⟩▷⟨ c' , e' , s' ⟩)
    → ------------------------------------------------------------
                   ⟨ c ∷ cs , e , s ⟩▷*⟨ c ∷ cs , e , s ⟩

  _∷_ :
                          ∀ {c e s c' e' s' c'' e'' s''} → 
       ⟨ c , e , s ⟩▷⟨ c' , e' , s' ⟩ → ⟨ c' , e' , s' ⟩▷*⟨ c'' , e'' , s'' ⟩
    → ------------------------------------------------------------------------
                      ⟨ c , e , s ⟩▷*⟨ c'' , e'' , s'' ⟩


-- Determinism
------------------------------------------------------------

-- ▷-deterministic : 
--   ∀ {n}{c c' c'' e e' e''}{s s' s'' : State n} 
--   → ⟨ c , e , s ⟩▷⟨ c' , e' , s' ⟩ → ⟨ c , e , s ⟩▷⟨ c'' , e'' , s'' ⟩
--   → (c' ≡ c'') × (e' ≡ e'') × (s' ≡ s'')
-- ▷-deterministic (PUSH n₁) (PUSH .n₁)  = refl , refl , refl
-- ▷-deterministic (ADD a b) (ADD .a .b) = refl , refl , refl
-- ▷-deterministic (MUL a b) (MUL .a .b) = refl , refl , refl
-- ▷-deterministic (SUB a b) (SUB .a .b) = refl , refl , refl
-- ▷-deterministic TRUE      TRUE        = refl , refl , refl
-- ▷-deterministic FALSE     FALSE       = refl , refl , refl
-- ▷-deterministic (EQ a b)  (EQ .a .b)  = refl , refl , refl
-- ▷-deterministic (LT a b)  (LT .a .b)  = refl , refl , refl
-- ▷-deterministic (LTE a b) (LTE .a .b) = refl , refl , refl
-- ▷-deterministic (AND a b) (AND .a .b) = refl , refl , refl
-- ▷-deterministic (NOT b)   (NOT .b)    = refl , refl , refl
-- ▷-deterministic (FETCH x) (FETCH .x)  = refl , refl , refl
-- ▷-deterministic (STORE x) (STORE .x)  = refl , refl , refl
-- ▷-deterministic BRANCH    BRANCH      = refl , refl , refl
-- ▷-deterministic NOOP      NOOP        = refl , refl , refl
-- ▷-deterministic LOOP      LOOP        = refl , refl , refl

▷*-deterministic :
  ∀ {n}{c c' c'' e e' e''}{s s' s'' : State n}
  → ⟨ c , e , s ⟩▷*⟨ c' , e' , s' ⟩ → ⟨ c , e , s ⟩▷*⟨ c'' , e'' , s'' ⟩
  → (c' ≡ c'') × (e' ≡ e'') × (s' ≡ s'')
▷*-deterministic = {!!}
-- ▷*-deterministic done done = refl , refl , refl
-- ▷*-deterministic done (() ∷ p2)
-- ▷*-deterministic (stuck x) (stuck x₁) = refl , refl , refl
-- ▷*-deterministic (stuck x) (x₁ ∷ p2) = ⊥-elim (x _ _ _ x₁)
-- ▷*-deterministic (() ∷ p1) done
-- ▷*-deterministic (x ∷ p1) (stuck x₁) = ⊥-elim (x₁ _ _ _ x)
-- ▷*-deterministic (x ∷ p1) (x₁ ∷ p2) with ▷-deterministic x x₁
-- ... | eq1 , eq2 , eq3 rewrite eq1 | eq2 | eq3 = ▷*-deterministic p1 p2


-- Compilation 
------------------------------------------------------------

𝓒⟦_⟧ᵉ : ∀ {n t} → Exp n t → Code n
𝓒⟦ lit x       ⟧ᵉ = PUSH x ∷ []
𝓒⟦ add a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ ADD
𝓒⟦ mul a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ MUL
𝓒⟦ sub a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ SUB
𝓒⟦ var x       ⟧ᵉ = FETCH x ∷ []
𝓒⟦ tt          ⟧ᵉ = TRUE ∷ []
𝓒⟦ ff          ⟧ᵉ = FALSE ∷ []
𝓒⟦ eq  a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ EQ
𝓒⟦ lte a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ LTE
𝓒⟦ lt  a b     ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ LT
𝓒⟦ Exp.and a b ⟧ᵉ = 𝓒⟦ b ⟧ᵉ <> 𝓒⟦ a ⟧ᵉ ∷ʳ AND
𝓒⟦ not e       ⟧ᵉ = 𝓒⟦ e ⟧ᵉ ∷ʳ NOT

𝓒⟦_⟧ˢ : ∀ {n} → St n → Code n
𝓒⟦ x := e                 ⟧ˢ = 𝓒⟦ e ⟧ᵉ ∷ʳ STORE x
𝓒⟦ skip                   ⟧ˢ = NOOP ∷ []
𝓒⟦ s₁ , s₂                ⟧ˢ = 𝓒⟦ s₁ ⟧ˢ <> 𝓒⟦ s₂ ⟧ˢ
𝓒⟦ if b then st₁ else st₂ ⟧ˢ = 𝓒⟦ b ⟧ᵉ ∷ʳ BRANCH 𝓒⟦ st₁ ⟧ˢ 𝓒⟦ st₂ ⟧ˢ
𝓒⟦ while b do st          ⟧ˢ = LOOP 𝓒⟦ b ⟧ᵉ 𝓒⟦ st ⟧ˢ ∷ []


-- Compilation correctness
------------------------------------------------------------

weaken-step-code : 
  ∀ {n}{c c' c'' e e'}{s s' : State n}
  → ⟨ c        , e , s ⟩▷⟨ c'        , e' , s' ⟩
  → ⟨ c <> c'' , e , s ⟩▷⟨ c' <> c'' , e' , s' ⟩
weaken-step-code = {!!}
-- weaken-step-code (PUSH n₁) = PUSH n₁
-- weaken-step-code (ADD a b) = ADD a b
-- weaken-step-code (MUL a b) = MUL a b
-- weaken-step-code (SUB a b) = SUB a b
-- weaken-step-code TRUE      = TRUE
-- weaken-step-code FALSE     = FALSE
-- weaken-step-code (EQ a b)  = EQ a b
-- weaken-step-code (LT a b)  = LT a b
-- weaken-step-code (LTE a b) = LTE a b
-- weaken-step-code (AND a b) = AND a b
-- weaken-step-code (NOT b)   = NOT b
-- weaken-step-code (FETCH x) = FETCH x
-- weaken-step-code (STORE x) = STORE x
-- weaken-step-code {c'' = c''}(BRANCH {c₁}{c₂}{c}{t})
--   rewrite LM.assoc (ifBool t then c₁ else c₂) c c'' = BRANCH
-- weaken-step-code {c'' = c''}(LOOP {c₁}{c₂}{c}) 
--   rewrite LM.assoc c₁ (BRANCH (c₂ ∷ʳ LOOP c₁ c₂) (NOOP ∷ []) ∷ c) c'' = LOOP
-- weaken-step-code NOOP = NOOP

infixr 5 _▷*<>_
_▷*<>_ :
  ∀ {n c c' e e' e''}{s s' s'' : State n}
  → ⟨ c       , e  , s  ⟩▷*⟨ [] , e'  , s'  ⟩
  → ⟨ c'      , e' , s' ⟩▷*⟨ [] , e'' , s'' ⟩
  → ⟨ c <> c' , e  , s  ⟩▷*⟨ [] , e'' , s'' ⟩
_▷*<>_ done        p2 = p2
_▷*<>_ (step ∷ p1) p2 = weaken-step-code step ∷ p1 ▷*<> p2


𝓒-Exp-nat : 
  ∀ {n e}{s : State n} exp -> ⟨ 𝓒⟦ exp ⟧ᵉ , e , s ⟩▷*⟨ [] , nat (⟦ exp ⟧ᵉ s) ∷ e , s ⟩
𝓒-Exp-nat (lit x)   = PUSH x ∷ done
𝓒-Exp-nat (add a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (ADD _ _ ∷ done)
𝓒-Exp-nat (mul a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (MUL _ _ ∷ done)
𝓒-Exp-nat (sub a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (SUB _ _ ∷ done)
𝓒-Exp-nat (var x)   = FETCH x ∷ done

𝓒-Exp-bool :
  ∀ {n e}{s : State n} exp -> ⟨ 𝓒⟦ exp ⟧ᵉ , e , s ⟩▷*⟨ [] , bool (⟦ exp ⟧ᵉ s) ∷ e , s ⟩
𝓒-Exp-bool tt            = TRUE ∷ done
𝓒-Exp-bool ff            = FALSE ∷ done
𝓒-Exp-bool (eq a b)      = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> EQ  _ _ ∷ done
𝓒-Exp-bool (lte a b)     = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> LTE _ _ ∷ done
𝓒-Exp-bool (lt a b)      = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> LT  _ _ ∷ done
𝓒-Exp-bool (Exp.and a b) = (𝓒-Exp-bool b ▷*<> 𝓒-Exp-bool a) ▷*<> AND _ _ ∷ done
𝓒-Exp-bool (not e)       = 𝓒-Exp-bool  e ▷*<> NOT _ ∷ done

-- getting rid of the (<> []) at the end of a branch
-- (if there isn't code after the branch)
BRANCH-[] : 
  ∀ {n c₁ c₂ e t}{s : State n} → let c' = ifBool t then c₁ else c₂ in
  ⟨ BRANCH c₁ c₂ ∷ [] , bool t ∷ e , s ⟩▷⟨ c' , e , s ⟩
BRANCH-[] {n}{c₁}{c₂}{e}{t}{s} =
  subst
    (λ b → ⟨ BRANCH c₁ c₂ ∷ [] , bool t ∷ e , s ⟩▷⟨ b , e , s ⟩)
    (proj₂ LM.identity (ifBool t then c₁ else c₂))
    BRANCH

-- 𝓒-correct-to :
--   ∀ {n}{S : St n}{s s'} 
--   → ⟨ S , s ⟩⟱ s' → ⟨ 𝓒⟦ S ⟧ˢ , [] , s ⟩▷*⟨ [] , [] , s' ⟩

-- 𝓒-correct-to (ass {_}{x}{a}) = 𝓒-Exp-nat a ▷*<> STORE x ∷ done
-- 𝓒-correct-to skip = NOOP ∷ done
-- 𝓒-correct-to (a , b) = 𝓒-correct-to a ▷*<> 𝓒-correct-to b

-- 𝓒-correct-to (if-true {s = s}{b = b} x p) with 𝓒-Exp-bool {e = []}{s = s} b
-- ... | condition rewrite T→≡true x = 
--   condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p

-- 𝓒-correct-to (if-false {s = s}{b = b} x p) with 𝓒-Exp-bool {e = []}{s = s} b
-- ... | condition rewrite F→≡false x = 
--   condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p

-- 𝓒-correct-to (while-true {s}{b = b} x p k) with 𝓒-Exp-bool {e = []}{s = s} b
-- ... | condition rewrite T→≡true x = 
--   LOOP ∷ condition ▷*<> BRANCH-[] ∷ 𝓒-correct-to p ▷*<> 𝓒-correct-to k

-- 𝓒-correct-to (while-false {s}{S}{b} x) with 𝓒-Exp-bool {e = []}{s = s} b
-- ... | condition rewrite F→≡false x = 
--   LOOP ∷ condition ▷*<> BRANCH-[] ∷ NOOP ∷ done


▷*-split : 
  ∀ {n}{s s' : State n}{e e'} c₁ {c₂}
  → ⟨ c₁ <> c₂ , e , s ⟩▷*⟨ [] , e' , s' ⟩
  → ∃₂ λ s'' e''  
  → ⟨ c₁ , e  , s    ⟩▷*⟨ [] , e'' , s'' ⟩ ×
    ⟨ c₂ , e'' , s'' ⟩▷*⟨ [] , e'  , s'  ⟩
▷*-split = {!!}
-- ▷*-split [] p = _ , _ , done , p
-- ▷*-split (._ ∷ c₁) (PUSH n₁ ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , PUSH n₁ ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (ADD a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , ADD a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (MUL a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , MUL a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (SUB a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , SUB a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (TRUE ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , TRUE ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (FALSE ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , FALSE ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (EQ a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , EQ a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (LT a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , LT a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (LTE a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , LTE a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (AND a b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , AND a b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (NOT b ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , NOT b ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (FETCH x ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , FETCH x ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (STORE x ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , STORE x ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) {c₂} (BRANCH{ca}{cb}{._}{true}{e}{s} ∷ p)
--   rewrite sym $ LM.assoc ca c₁ c₂ with ▷*-split (ca <> c₁) p
-- ... | _ , _ , p1 , p2 = _ , _ , BRANCH ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) {c₂} (BRANCH{ca}{cb}{._}{false}{e}{s} ∷ p)
--   rewrite sym $ LM.assoc cb c₁ c₂ with ▷*-split (cb <> c₁) p
-- ... | _ , _ , p1 , p2 = _ , _ , BRANCH ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) (NOOP ∷ p) with ▷*-split c₁ p
-- ... | _ , _ , p1 , p2 = _ , _ , NOOP ∷ p1 , p2
-- ▷*-split (._ ∷ c₁) {c₂}(LOOP{ca}{cb}{._}{e}{s} ∷ p) 
--   rewrite sym $ LM.assoc ca (BRANCH (cb ∷ʳ LOOP ca cb) (NOOP ∷ []) ∷ c₁) c₂
--   with ▷*-split (ca <> (BRANCH (cb ∷ʳ LOOP ca cb) (NOOP ∷ []) ∷ c₁)) p
-- ... | _ , _ , p1 , p2 = _ , _ , LOOP ∷ p1 , p2


-- Well founded recursion needed on while-true !!!

𝓒-correct-from : 
  ∀ {n}{S : St n}{e s s'} 
  → ⟨ 𝓒⟦ S ⟧ˢ , [] , s ⟩▷*⟨ [] , e , s' ⟩ → (⟨ S , s ⟩⟱ s') × e ≡ []

-- -- Assignment
-- 𝓒-correct-from {_}{x := exp}{e}{s} p with 𝓒-Exp-nat {e = []}{s = s} exp | ▷*-split 𝓒⟦ exp ⟧ᵉ p
-- 𝓒-correct-from {n} {.x := exp} p | exp' | s₁ , ._ , p1 , STORE x ∷ () ∷ p2 
-- 𝓒-correct-from {n} {.x := exp} p | exp' | s₁ , ._ , p1 , STORE x ∷ done with ▷*-deterministic exp' p1
-- ... | _ , eqe , eqs rewrite eqs with ∷-injective eqe
-- ... | eqn , eqe' rewrite sym $ nat-inj eqn = ass , sym eqe'

-- -- Skip
-- 𝓒-correct-from {S = skip} (NOOP ∷ done) = skip , refl
-- 𝓒-correct-from {S = skip} (NOOP ∷ () ∷ _)

-- -- Composition
-- 𝓒-correct-from {S = S , S₁} p with ▷*-split 𝓒⟦ S ⟧ˢ p
-- ... | s'' , e'' , p1 , p2 with 𝓒-correct-from {S = S} p1 
-- ... | p1' , eqe'' rewrite eqe'' with 𝓒-correct-from {S = S₁} p2
-- ... | p2' , eqe = (p1' , p2') , eqe

-- -- If-then-else
-- 𝓒-correct-from {S = if b then S else S₁}{e}{s}{s'} p with 𝓒-Exp-bool {e = []}{s = s} b | ▷*-split 𝓒⟦ b ⟧ᵉ p
-- ... | b' | s'' , [] , p1 , () ∷ p2
-- ... | b' | s'' , nat x ∷ e'' , p1 , () ∷ p2
-- ... | b' | s'' , bool x ∷ e' , p1 , BRANCH ∷ p2 with ▷*-deterministic b' p1
-- ... | _ , eqe , eqs rewrite sym eqs with ∷-injective eqe
-- ... | eq-cond , []≡e' 
--   rewrite sym $ bool-inj eq-cond | sym []≡e' with ⟦ b ⟧ᵉ s | inspect ⟦ b ⟧ᵉ s

-- ... | true  | [ condTrue ] rewrite proj₂ LM.identity 𝓒⟦ S ⟧ˢ 
--   = if-true (≡true→T condTrue) (proj₁ rest) , proj₂ rest 
--   where rest = 𝓒-correct-from {S = S} p2

-- ... | false | [ condFalse ] rewrite proj₂ LM.identity 𝓒⟦ S₁ ⟧ˢ 
--   = if-false (≡false→F condFalse) (proj₁ rest) , proj₂ rest 
--   where rest = 𝓒-correct-from {S = S₁} p2
  

-- while
𝓒-correct-from {S = while b do S}{e}{s}{s'} (LOOP ∷ p) 
  with 𝓒-Exp-bool {e = []}{s = s} b | ▷*-split 𝓒⟦ b ⟧ᵉ p
... | b' | s'' , ._ , p1 , BRANCH ∷ p2 with ▷*-deterministic b' p1
... | _ , eqe , eqs rewrite sym eqs with ∷-injective eqe
... | eq-cond , []≡e' rewrite 
    sym $ bool-inj eq-cond 
  | sym []≡e' 
  | proj₂ LM.identity (ifBool ⟦ b ⟧ᵉ s then 𝓒⟦ S ⟧ˢ ++ LOOP 𝓒⟦ b ⟧ᵉ 𝓒⟦ S ⟧ˢ ∷ [] else (NOOP ∷ []))
    with ⟦ b ⟧ᵉ s | inspect ⟦ b ⟧ᵉ s
... | true  | [ condTrue ]  = {!!}
... | false | [ condFalse ] = {!!} , {!!}

𝓒-while-false : 





-- ... | cond  | [ condTrue  ] = {!!}




-- catchall
𝓒-correct-from {S = S} p = {!!}



-- 𝓒⟦_⟧ˢ : ∀ {n} → St n → Code n
-- 𝓒⟦ x := e                 ⟧ˢ = 𝓒⟦ e ⟧ᵉ ∷ʳ STORE x
-- 𝓒⟦ skip                   ⟧ˢ = NOOP ∷ []
-- 𝓒⟦ s₁ , s₂                ⟧ˢ = 𝓒⟦ s₁ ⟧ˢ <> 𝓒⟦ s₂ ⟧ˢ
-- 𝓒⟦ if b then st₁ else st₂ ⟧ˢ = 𝓒⟦ b ⟧ᵉ ∷ʳ BRANCH 𝓒⟦ st₁ ⟧ˢ 𝓒⟦ st₂ ⟧ˢ
-- 𝓒⟦ while b do st          ⟧ˢ = LOOP 𝓒⟦ b ⟧ᵉ 𝓒⟦ st ⟧ˢ ∷ []
