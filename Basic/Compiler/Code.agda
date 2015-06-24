
module Basic.Compiler.Code where

open import Basic.AST
open import Basic.BigStep
open import Utils.Decidable
open import Utils.Monoid

open import Data.Fin using (Fin; #_)
open import Data.Vec hiding (_∷ʳ_; _++_; [_])
open import Data.Nat
open import Data.Bool renaming (not to notBool; if_then_else_ to ifBool_then_else)
open import Data.List hiding ([_])
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Empty
open import Algebra
import Level as L
private
  module LM {a A} = Algebra.Monoid (Data.List.monoid {a} A)

{-
Chapter 3.1 and 3.2. 

Semantics of an abstract machine and specification of the translation from
While syntax to the abstract machine syntax.
-}





{-
Definition of the stack and the AM

We follow the book closely here.

"nat-inj" and "bool-inj" just establish injectivity of context entry
constructors.

That we had to prove this is something of a limitation of the current Agda.
For example, Coq would derive supply these lemmas automatically. 
-}

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


-- Semantics
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

{-
The book doesn't give an explicit definition to the constructors, but we have to. 
-}
infixr 5 _∷_
data ⟨_,_,_⟩▷*⟨_,_,_⟩ {n} : Code n → Stack → State n → Code n → Stack → State n → Set where

  done : 
                 ∀ {e s}
    → ---------------------------------
      ⟨ [] , e , s ⟩▷*⟨ [] , e , s ⟩

  {- We define "being stuck" explicitly as a configuration from which no transitions exist -}   
  stuck : 
       ∀ {c cs e s} → (∀ c' e' s' → ¬ ⟨ c ∷ cs , e , s ⟩▷⟨ c' , e' , s' ⟩)
    → ------------------------------------------------------------
                   ⟨ c ∷ cs , e , s ⟩▷*⟨ c ∷ cs , e , s ⟩

  _∷_ :
                          ∀ {c e s c' e' s' c'' e'' s''} → 
       ⟨ c , e , s ⟩▷⟨ c' , e' , s' ⟩ → ⟨ c' , e' , s' ⟩▷*⟨ c'' , e'' , s'' ⟩
    → ------------------------------------------------------------------------
                      ⟨ c , e , s ⟩▷*⟨ c'' , e'' , s'' ⟩

{- We will need the length of computation sequences for the compiler correctness proof -} 
▷*-length : ∀ {n}{c c' e e'}{s s' : State n} → ⟨ c , e , s ⟩▷*⟨ c' , e' , s' ⟩ → ℕ
▷*-length done      = 0
▷*-length (stuck x) = 0
▷*-length (x ∷ p)   = suc (▷*-length p)


-- Determinism (exercise 3.6)
------------------------------------------------------------

▷-deterministic : 
  ∀ {n}{c c' c'' e e' e''}{s s' s'' : State n} 
  → ⟨ c , e , s ⟩▷⟨ c' , e' , s' ⟩ → ⟨ c , e , s ⟩▷⟨ c'' , e'' , s'' ⟩
  → (c' ≡ c'') × (e' ≡ e'') × (s' ≡ s'')
▷-deterministic (PUSH n₁) (PUSH .n₁)  = refl , refl , refl
▷-deterministic (ADD a b) (ADD .a .b) = refl , refl , refl
▷-deterministic (MUL a b) (MUL .a .b) = refl , refl , refl
▷-deterministic (SUB a b) (SUB .a .b) = refl , refl , refl
▷-deterministic TRUE      TRUE        = refl , refl , refl
▷-deterministic FALSE     FALSE       = refl , refl , refl
▷-deterministic (EQ a b)  (EQ .a .b)  = refl , refl , refl
▷-deterministic (LT a b)  (LT .a .b)  = refl , refl , refl
▷-deterministic (LTE a b) (LTE .a .b) = refl , refl , refl
▷-deterministic (AND a b) (AND .a .b) = refl , refl , refl
▷-deterministic (NOT b)   (NOT .b)    = refl , refl , refl
▷-deterministic (FETCH x) (FETCH .x)  = refl , refl , refl
▷-deterministic (STORE x) (STORE .x)  = refl , refl , refl
▷-deterministic BRANCH    BRANCH      = refl , refl , refl
▷-deterministic NOOP      NOOP        = refl , refl , refl
▷-deterministic LOOP      LOOP        = refl , refl , refl

▷*-deterministic :
  ∀ {n}{c c' c'' e e' e''}{s s' s'' : State n}
  → ⟨ c , e , s ⟩▷*⟨ c' , e' , s' ⟩ → ⟨ c , e , s ⟩▷*⟨ c'' , e'' , s'' ⟩
  → (c' ≡ c'') × (e' ≡ e'') × (s' ≡ s'')
▷*-deterministic done done = refl , refl , refl
▷*-deterministic done (() ∷ p2)
▷*-deterministic (stuck x) (stuck x₁) = refl , refl , refl
▷*-deterministic (stuck x) (x₁ ∷ p2) = ⊥-elim (x _ _ _ x₁)
▷*-deterministic (() ∷ p1) done
▷*-deterministic (x ∷ p1) (stuck x₁) = ⊥-elim (x₁ _ _ _ x)
▷*-deterministic (x ∷ p1) (x₁ ∷ p2) with ▷-deterministic x x₁
... | eq1 , eq2 , eq3 rewrite eq1 | eq2 | eq3 = ▷*-deterministic p1 p2


-- Compilation (chapter 3.2)
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


------------------------------------------------------------

{-
Some additional lemmas needed to the compiler correctness proofs.
-}


{- A weaker variant of exercise 3.4 -}
weaken-step-code : 
  ∀ {n}{c c' c'' e e'}{s s' : State n}
  → ⟨ c        , e , s ⟩▷⟨ c'        , e' , s' ⟩
  → ⟨ c <> c'' , e , s ⟩▷⟨ c' <> c'' , e' , s' ⟩
weaken-step-code (PUSH n₁) = PUSH n₁
weaken-step-code (ADD a b) = ADD a b
weaken-step-code (MUL a b) = MUL a b
weaken-step-code (SUB a b) = SUB a b
weaken-step-code TRUE      = TRUE
weaken-step-code FALSE     = FALSE
weaken-step-code (EQ a b)  = EQ a b
weaken-step-code (LT a b)  = LT a b
weaken-step-code (LTE a b) = LTE a b
weaken-step-code (AND a b) = AND a b
weaken-step-code (NOT b)   = NOT b
weaken-step-code (FETCH x) = FETCH x
weaken-step-code (STORE x) = STORE x
weaken-step-code {c'' = c''}(BRANCH {c₁}{c₂}{c}{t})
  rewrite LM.assoc (ifBool t then c₁ else c₂) c c'' = BRANCH
weaken-step-code {c'' = c''}(LOOP {c₁}{c₂}{c}) 
  rewrite LM.assoc c₁ (BRANCH (c₂ ∷ʳ LOOP c₁ c₂) (NOOP ∷ []) ∷ c) c'' = LOOP
weaken-step-code NOOP = NOOP

{-
This lemma is not in the book, but it's very convenient to use in the following
proofs. It's just the analogue of Basic.SmallStep.append for the computation
sequences here. 
-}
infixr 5 _▷*<>_
_▷*<>_ :
  ∀ {n c c' e e' e''}{s s' s'' : State n}
  → ⟨ c       , e  , s  ⟩▷*⟨ [] , e'  , s'  ⟩
  → ⟨ c'      , e' , s' ⟩▷*⟨ [] , e'' , s'' ⟩
  → ⟨ c <> c' , e  , s  ⟩▷*⟨ [] , e'' , s'' ⟩
_▷*<>_ done        p2 = p2
_▷*<>_ (step ∷ p1) p2 = weaken-step-code step ∷ p1 ▷*<> p2

{- Lemma 3.18 -}
𝓒-Exp-nat : 
  ∀ {n e}{s : State n} exp -> ⟨ 𝓒⟦ exp ⟧ᵉ , e , s ⟩▷*⟨ [] , nat (⟦ exp ⟧ᵉ s) ∷ e , s ⟩
𝓒-Exp-nat (lit x)   = PUSH x ∷ done
𝓒-Exp-nat (add a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (ADD _ _ ∷ done)
𝓒-Exp-nat (mul a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (MUL _ _ ∷ done)
𝓒-Exp-nat (sub a b) = (𝓒-Exp-nat b ▷*<> 𝓒-Exp-nat a) ▷*<> (SUB _ _ ∷ done)
𝓒-Exp-nat (var x)   = FETCH x ∷ done


{- Lemma 3.19 -}
𝓒-Exp-bool :
  ∀ {n e}{s : State n} exp -> ⟨ 𝓒⟦ exp ⟧ᵉ , e , s ⟩▷*⟨ [] , bool (⟦ exp ⟧ᵉ s) ∷ e , s ⟩
𝓒-Exp-bool tt            = TRUE ∷ done
𝓒-Exp-bool ff            = FALSE ∷ done
𝓒-Exp-bool (eq a b)      = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> EQ  _ _ ∷ done
𝓒-Exp-bool (lte a b)     = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> LTE _ _ ∷ done
𝓒-Exp-bool (lt a b)      = (𝓒-Exp-nat  b ▷*<> 𝓒-Exp-nat a) ▷*<> LT  _ _ ∷ done
𝓒-Exp-bool (Exp.and a b) = (𝓒-Exp-bool b ▷*<> 𝓒-Exp-bool a) ▷*<> AND _ _ ∷ done
𝓒-Exp-bool (not e)       = 𝓒-Exp-bool  e ▷*<> NOT _ ∷ done


{-
A "smart constructor" that gets rid of the trailing (++[]) at the end of the branch.
This is not mentioned in the book, because it (rightfully) assumes that appendding an
empty list to the end of a list results in the same list, while here we have to make
this property explicit
-}

BRANCH-[] : 
  ∀ {n c₁ c₂ e t}{s : State n} → let c' = ifBool t then c₁ else c₂ in
  ⟨ BRANCH c₁ c₂ ∷ [] , bool t ∷ e , s ⟩▷⟨ c' , e , s ⟩
BRANCH-[] {n}{c₁}{c₂}{e}{t}{s} =
  subst
    (λ b → ⟨ BRANCH c₁ c₂ ∷ [] , bool t ∷ e , s ⟩▷⟨ b , e , s ⟩)
    (proj₂ LM.identity (ifBool t then c₁ else c₂))
    BRANCH

