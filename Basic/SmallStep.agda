 
module Basic.SmallStep where

import Data.Bool as Bool using (not)
open import Data.Bool hiding (not; if_then_else_)
open import Data.Empty
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat 
open import Data.Nat.Properties.Simple
open import Data.Vec 
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit hiding (_≤?_)
open import Data.Product
open import Data.Maybe
import Level as L

open import Basic.AST
open import Utils.Decidable
open import Utils.NatOrdLemmas

{-
Small-step semantics for While; see chapter 2.2 of the book. 

The book uses the notational convenience of omitting the state on the right hand side
of the transition if there is no such state. We must define the same shorthand explicitly.

Since the book seems to do it, I also decided to index derivation sequences by their length.
This means also more cases for notatitonal shorthands. Otherwise, the definitions follow the book
faithfully.

Here I omit some commentary, since most of the things follow the same pattern as with big-step
semantics. However, I also include some lemmas specific to small-step semantics, which are
also included in the book.
-}


infixr 5 _∷_
mutual

  -- Notational shorthands for derivation sequences:

  -- Sequences with specified number of steps:
  ⟨_,_⟩_⟶_ : ∀ {n} → St n → State n → ℕ → State n → Set
  ⟨_,_⟩_⟶_ S s k s' = ⟨ S , s ⟩ k ⟶[ nothing , s' ]

  ⟨_,_⟩_⟶⟨_,_⟩ : ∀ {n} → St n → State n → ℕ → St n → State n → Set
  ⟨_,_⟩_⟶⟨_,_⟩ S s k S' s' = ⟨ S , s ⟩ k ⟶[ just S' , s' ]

  -- Sequences with unspecified number of steps:
  ⟨_,_⟩⟶*⟨_,_⟩ : ∀ {n} → St n → State n → St n → State n → Set
  ⟨_,_⟩⟶*⟨_,_⟩ S s S' s' = ∃ λ n → ⟨ S , s ⟩ n ⟶[ just S' , s' ]

  ⟨_,_⟩⟶*_ : ∀ {n} → St n → State n → State n → Set
  ⟨_,_⟩⟶*_ S s s' = ∃ λ n → ⟨ S , s ⟩ n ⟶[ nothing , s' ]

  -- Single-step transitions:
  ⟨_,_⟩⟶_ : ∀ {n} → St n → State n → State n → Set
  ⟨_,_⟩⟶_ S s s' = ⟨ S , s ⟩⟶[ nothing , s' ]
  
  ⟨_,_⟩⟶⟨_,_⟩ : ∀ {n} → St n → State n → St n → State n → Set
  ⟨_,_⟩⟶⟨_,_⟩ S s S' s' = ⟨ S , s ⟩⟶[ just S' , s' ]


  data ⟨_,_⟩⟶[_,_] {n : ℕ} : St n → State n → Maybe (St n) → State n → Set where
    
    ass :
                    ∀ {x a s}      
      → --------------------------------------
        ⟨ x := a , s ⟩⟶ ( s [ x ]≔ ⟦ a ⟧ᵉ s )
  
    skip :
             ∀ {s}
      → ----------------
        ⟨ skip , s ⟩⟶ s
  
    _◄ :
                 ∀ {s s' S₁ S₂ S₁'} →
              ⟨ S₁ , s ⟩⟶⟨ S₁' , s' ⟩
      → --------------------------------------
        ⟨ (S₁ , S₂) , s ⟩⟶⟨ (S₁' , S₂) , s' ⟩
          
    _∙ :
              ∀ {s s' S₁ S₂} → 
               ⟨ S₁ , s ⟩⟶ s'
      → ------------------------------
        ⟨ (S₁ , S₂) , s ⟩⟶⟨ S₂ , s' ⟩
  
    if-true :
             ∀ {b s S₁ S₂}  →  T (⟦ b ⟧ᵉ s)       
      → ---------------------------------------
        ⟨ if b then S₁ else S₂ , s ⟩⟶⟨ S₁ , s ⟩  
  
    if-false :
             ∀ {b s S₁ S₂}  →  F (⟦ b ⟧ᵉ s)       
      → ---------------------------------------
        ⟨ if b then S₁ else S₂ , s ⟩⟶⟨ S₂ , s ⟩  
  
    while :
                                   ∀ {b s S}
      → ----------------------------------------------------------------------
        ⟨ while b do S , s ⟩⟶⟨ (if b then (S , while b do S) else skip) , s ⟩
  

  -- Derivation sequences  
  data ⟨_,_⟩_⟶[_,_] {n : ℕ} : St n → State n → ℕ → Maybe (St n) → State n → Set where
  
    pause  : 
               ∀ {s S}
      → -----------------------
        ⟨ S , s ⟩ 0 ⟶⟨ S , s ⟩
  
    _stop :
          ∀ {s s' S} → 
         ⟨ S , s ⟩⟶ s'
      → -----------------
        ⟨ S , s ⟩ 1 ⟶ s' 
  
    _∷_ : 
                       ∀ {k s₁ s₂ s₃ S₁ S₂ S₃} → 
        ⟨ S₁ , s₁ ⟩⟶⟨ S₂ , s₂ ⟩  →  ⟨ S₂ , s₂ ⟩ k ⟶[ S₃ , s₃ ]  
      → --------------------------------------------------------
                    ⟨ S₁ , s₁ ⟩ suc k ⟶[ S₃ , s₃ ]
  

-- Example program derivation (very slow to check!)
private
  prog : St 3
  prog =
    # 2 := lit 0 ,
    while lte (var (# 1)) (var (# 0)) do
      ( # 2 := add (var (# 2)) (lit 1) ,
        # 0 := sub (var (# 0)) (var (# 1)) )

  -- -- Uncomment if you dare
  -- prog-deriv : 
  --   ∀ {z} → ⟨ prog , 17 ∷ 5 ∷ z ∷ [] ⟩ _ ⟶ (2 ∷ 5 ∷ 3 ∷ [])
  -- prog-deriv =
  --   ass ∙ ∷ 
  --     while ∷ if-true tt ∷ ass ∙ ◄ ∷ ass ∙ ∷ 
  --     while ∷ if-true tt ∷ ass ∙ ◄ ∷ ass ∙ ∷ 
  --     while ∷ if-true tt ∷ ass ∙ ◄ ∷ ass ∙ ∷
  --     while ∷ if-false tt ∷ skip stop
 
-- Divergence

_divergesOnₛ_ : ∀ {n} → St n → State n → Set
prog divergesOnₛ s = ∀ {n s'} → ¬ ⟨ prog , s ⟩ n ⟶ s'

Divergentₛ : ∀ {n} → St n → Set
Divergentₛ prog = ∀ {s} → prog divergesOnₛ s

private  
  inf-loopₛ : ∀ {n} → Divergentₛ {n} (while tt do skip)
  inf-loopₛ (() stop)
  inf-loopₛ (while ∷ (() stop))
  inf-loopₛ (while ∷ (if-true tt ∷ (() stop)))
  inf-loopₛ (while ∷ (if-true tt ∷ ((() ◄) ∷ p)))
  inf-loopₛ (while ∷ (if-true tt ∷ ((skip ∙) ∷ p))) = inf-loopₛ p
  inf-loopₛ (while ∷ (if-false () ∷ p))


deterministicₛ :
  ∀ {n}{S : St n}{S' S'' s s' s''} 
  → ⟨ S , s ⟩⟶[ S' , s' ] → ⟨ S , s ⟩⟶[ S'' , s'' ]
  → S' ≡ S'' × s' ≡ s''
deterministicₛ {n} = go where
  go : ∀ {S : St n}{S' S'' s s' s''} 
      → ⟨ S , s ⟩⟶[ S' , s' ] → ⟨ S , s ⟩⟶[ S'' , s'' ]
      → S' ≡ S'' × s' ≡ s''
  go ass ass = refl , refl
  go skip skip = refl , refl
  go (p1 ◄) (p2 ◄) with go p1 p2
  ... | refl , refl = refl , refl
  go (p1 ◄) (p2 ∙) with go p1 p2
  ... | () , _
  go (p1 ∙) (p2 ◄) with go p1 p2
  ... | () , _
  go (p1 ∙) (p2 ∙) with go p1 p2
  ... | refl , refl = refl , refl
  go (if-true x) (if-true x₁) = refl , refl
  go (if-true x) (if-false x₁) rewrite T→≡true x = ⊥-elim x₁
  go (if-false x) (if-true x₁) rewrite T→≡true x₁ = ⊥-elim x
  go (if-false x) (if-false x₁) = refl , refl
  go while while = refl , refl  


{-
Lemma 2.19 of the book: if we have a derivation over the composition of statements,
then there exists two derivations over the substatements, such that their lenghts
add up to the length of the original derivation.
-}

seq-split : 
  ∀ {n k S₁ S₂}{s₁ s₃ : State n}
  → ⟨ (S₁ , S₂) , s₁ ⟩ k ⟶ s₃
  → Σ (State n × ℕ × ℕ) λ {(s₂ , k₁ , k₂) 
  → ⟨ S₁ , s₁ ⟩ k₁ ⟶ s₂
  × ⟨ S₂ , s₂ ⟩ k₂ ⟶ s₃
  × k₁ + k₂ ≡ k}
seq-split (() stop)
seq-split (x ◄ ∷ p) with seq-split p
... | _ , p1 , p2 , prf = _ , x ∷ p1 , p2 , cong suc prf
seq-split (x ∙ ∷ p) = _ , x stop , p , refl

{-
Exercise 2.20.
-}
ex2-20 :
  ∃ λ n → ∃₂ λ (s s' : State n) → ∃₂ λ A B →
  ⟨ (A , B) , s ⟩⟶*⟨ B , s' ⟩ × ¬ ⟨ A , s ⟩⟶* s'
ex2-20 = 1 , (0 ∷ []) , (2 ∷ []) , A , (while b do A) , Deriv , ¬Deriv
  where
  A = zero := add (lit 1) (var zero)
  b = lt (var zero) (lit 2)
  Deriv = , ass ∙ ∷ while ∷ if-true tt ∷ ass ∙ ∷ pause
  ¬Deriv : ¬ ⟨ A , 0 ∷ [] ⟩⟶* (2 ∷ [])
  ¬Deriv (._ , () stop)
  ¬Deriv (._ , () ∷ proj₂)

{-
The converse of seq-split: two derivations can be appended to a single derivation
over the composition of the programs.
-}
append :
  ∀ {n k₁ k₂}{s s' s'' : State n}{A B}
  → ⟨ A , s ⟩ k₁ ⟶ s'
  → ⟨ B , s' ⟩ k₂ ⟶ s''
  → ⟨ (A , B) , s ⟩ (k₁ + k₂) ⟶ s''
append (x stop) p2 = (x ∙) ∷ p2
append (x ∷ p1) p2 = (x ◄) ∷ append p1 p2


-- Correctness of factorial (exactly the same proof as with big-step semantics)
private

  ⟦fac⟧ : ℕ → ℕ
  ⟦fac⟧ zero    = 1
  ⟦fac⟧ (suc n) = suc n * ⟦fac⟧ n
  
  fac-loop : St 3
  fac-loop =
    while lt (var (# 1)) (var (# 0)) do
      ( # 1 := add (lit 1) (var (# 1)) ,
        # 2 := mul (var (# 1)) (var (# 2)) )
  
  fac : St 3
  fac =
    # 1 := lit 0 ,
    # 2 := lit 1 ,
    fac-loop 

  fac-loop-ok :
    ∀ d i → ⟨ fac-loop , d + i ∷ i ∷ ⟦fac⟧ i ∷ [] ⟩⟶* (d + i ∷ d + i ∷ ⟦fac⟧ (d + i) ∷ [])
  fac-loop-ok zero i = 
    , while ∷ if-false (¬A→FalseA $ a≮a i) ∷ skip stop
  fac-loop-ok (suc d) i with fac-loop-ok d (suc i)
  ... | _ , next rewrite +-suc d i = 
    , while ∷ if-true (A→TrueA $ a<sb+a i d) ∷ ass ∙ ◄ ∷ ass ∙ ∷ next
  
  fac-ok :
    ∀ n {i lim} → ⟨ fac , n ∷ i ∷ lim ∷ [] ⟩⟶* (n ∷ n ∷ ⟦fac⟧ n ∷ [])
  fac-ok n with fac-loop-ok n 0
  ... | _ , loop-ok rewrite +-comm n 0 = , ass ∙ ∷ ass ∙ ∷ loop-ok
