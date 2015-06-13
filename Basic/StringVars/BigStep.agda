 
module Basic.StringVars.BigStep where


-- Note: this has an additional "decl" stamenent
-- that is not present in the "Basic" folder

open import Function
open import Data.Nat renaming (_≟_ to _n≟_)
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality
open import Data.String renaming (_≟_ to _s≟_)
open import Data.Product
open import Data.Bool renaming (not to bnot) hiding (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.List hiding (and)
open import Data.Empty
open import Data.Unit hiding (_≤?_)
import Level as L

open import Utils.Decidable
open import Utils.NatOrdLemmas


-- AST + Types
------------------------------------------------------------

data Ty : Set where
  bool nat : Ty

⟦_⟧ᵗ : Ty → Set
⟦ nat  ⟧ᵗ = ℕ
⟦ bool ⟧ᵗ = Bool

State : Set
State = List (String × ℕ)

data Exp : Ty → Set where
  lit       : ℕ → Exp nat
  add mul   : Exp nat → Exp nat → Exp nat
  var       : String → Exp nat
  tt ff     : Exp bool
  eq lt lte : Exp nat → Exp nat → Exp bool
  and       : Exp bool → Exp bool → Exp bool
  not       : Exp bool → Exp bool

infixr 4 _,_
infixr 5 _:=_
data St : Set where
  decl          : String → Exp nat → St → St
  _:=_          : String → Exp nat → St
  skip          : St
  _,_           : St → St → St
  if_then_else_ : Exp bool → St → St → St
  while_do_     : Exp bool → St → St

_⇔_ : ∀ {a b} → Set a → Set b → Set (a L.⊔ b)
A ⇔ B = (A → B) × (B → A)


-- Well-scopedness
------------------------------------------------------------

InScope : ∀ {a}{A : Set a} → String → List (String × A) → Set
InScope s [] = ⊥
InScope s ((s' , _) ∷ xs) with s ≡⁇ s'
... | yes _ = ⊤
... | no  _ = InScope s xs

WellScoped : ∀ {a}{A : Set a}{ty} → Exp ty → List (String × A) → Set
WellScoped e s = go e where
  go : ∀ {ty} → Exp ty → Set  
  go (var x)   = InScope x s
  go tt        = ⊤
  go ff        = ⊤
  go (lit x)   = ⊤
  go (eq a b)  = go a × go b
  go (lt a b)  = go a × go b
  go (lte a b) = go a × go b
  go (and a b) = go a × go b
  go (mul a b) = go a × go b
  go (add a b) = go a × go b
  go (not a)   = go a

lookup : ∀ {a A} v s ⦃ _ : InScope {a}{A} v s ⦄ → A
lookup v [] ⦃ ⦄
lookup v ((v' , n) ∷ s) with v ≡⁇ v'
... | yes _ = n
... | no  _ = lookup v s

_[_]≔_ : ∀ Γ s ⦃ p : InScope s Γ ⦄ → ℕ → State
_[_]≔_ [] s ⦃ ⦄ n
((s' , v) ∷ Γ) [ s ]≔ n with s ≡⁇ s'
... | yes p = (s' , n) ∷ Γ
... | no ¬p = (s' , v) ∷ Γ [ s ]≔ n

-- Only well-scoped expressions may be evaluated
⟦_⟧ᵉ : ∀ {ty} (e : Exp ty) (s : State)⦃ _ : WellScoped e s ⦄ → ⟦ ty ⟧ᵗ
⟦ lit n   ⟧ᵉ s = n
⟦ var v   ⟧ᵉ s = lookup v s 
⟦ tt      ⟧ᵉ s = true
⟦ ff      ⟧ᵉ s = false
⟦ not e   ⟧ᵉ s = bnot (⟦ e ⟧ᵉ s)
⟦ add a b ⟧ᵉ s ⦃ _ , _ ⦄ =   ⟦ a ⟧ᵉ s +  ⟦ b ⟧ᵉ s
⟦ mul a b ⟧ᵉ s ⦃ _ , _ ⦄ =   ⟦ a ⟧ᵉ s *  ⟦ b ⟧ᵉ s
⟦ eq a b  ⟧ᵉ s ⦃ _ , _ ⦄ = ⌊ ⟦ a ⟧ᵉ s ≡⁇ ⟦ b ⟧ᵉ s ⌋
⟦ lte a b ⟧ᵉ s ⦃ _ , _ ⦄ = ⌊ ⟦ a ⟧ᵉ s ≤⁇ ⟦ b ⟧ᵉ s ⌋
⟦ and a b ⟧ᵉ s ⦃ _ , _ ⦄ =   ⟦ a ⟧ᵉ s ∧  ⟦ b ⟧ᵉ s
⟦ lt a b  ⟧ᵉ s ⦃ _ , _ ⦄ = ⌊ suc (⟦ a ⟧ᵉ s) ≤⁇ ⟦ b ⟧ᵉ s ⌋


-- Semantics
------------------------------------------------------------

data ⟨_,_⟩⟱_ : St → State → State → Set where

  decl :
            ∀ {s s' S x e e' well-scoped} → 
     ⟨ S , (x , ⟦ e ⟧ᵉ s) ∷ s ⟩⟱ ((x , e') ∷ s')
    → ------------------------------------------
             ⟨ decl x e S , s ⟩⟱ s'

  ass : 
      ∀ {s a x well-scoped}{in-scope : InScope x s}
    → ---------------------------------------------
          ⟨ x := a , s ⟩⟱ (s [ x ]≔ ⟦ a ⟧ᵉ s)

  skip : 
           ∀ {s} 
    → -----------------
      ⟨ skip , s ⟩⟱ s

  _,_ :
              ∀ {s₁ s₂ s₃ S₁ S₂} → 
      ⟨ S₁ , s₁ ⟩⟱ s₂  →  ⟨ S₂ , s₂ ⟩⟱ s₃  
    → ---------------------------------------
             ⟨ (S₁ , S₂ ) , s₁ ⟩⟱ s₃           

  if-true :
        ∀ {s s' S₁ S₂ b}⦃ well-scoped ⦄ →
        T (⟦ b ⟧ᵉ s)  →  ⟨ S₁ , s ⟩⟱ s'
    → -----------------------------------
       ⟨ if b then S₁ else S₂ , s ⟩⟱ s' 

  if-false :
       ∀ {s s' S₁ S₂ b}⦃ well-scoped ⦄ →
       F (⟦ b ⟧ᵉ s)  →  ⟨ S₂ , s ⟩⟱ s'
    → ----------------------------------
       ⟨ if b then S₁ else S₂ , s ⟩⟱ s' 

  while-true :
                   ∀ {s s' s'' S b}⦃ well-scoped ⦄ → 
     T (⟦ b ⟧ᵉ s)  →  ⟨ S , s ⟩⟱ s'  →  ⟨ while b do S , s' ⟩⟱ s''
    → --------------------------------------------------------------
                     ⟨ while b do S , s ⟩⟱ s''

  while-false :
       ∀ {s S b well-scoped} → 
           F (⟦ b ⟧ᵉ s)
    → ------------------------
      ⟨ while b do S , s ⟩⟱ s


-- State transition is deterministic

deterministicₙ : 
  ∀ {p s s' s''} → ⟨ p , s ⟩⟱ s' → ⟨ p , s ⟩⟱ s'' → s' ≡ s''
deterministicₙ = go where
  go : ∀ {p s s' s''} → ⟨ p , s ⟩⟱ s' → ⟨ p , s ⟩⟱ s'' → s' ≡ s''
  go (decl p1) (decl p2) with go p1 p2
  go (decl p1) (decl p2) | refl = refl
  go ass ass = refl
  go skip skip = refl
  go (p1 , p2) (p3 , p4) rewrite go p1 p3 | go p2 p4 = refl
  go (if-true x p1) (if-true x₁ p2) rewrite go p1 p2 = refl
  go (if-true x p1) (if-false x₁ p2) with trans (sym $ T→≡true x) (F→≡false x₁)
  ... | ()
  go (if-false x p1) (if-true x₁ p2) with trans (sym $ F→≡false x) (T→≡true x₁)
  ... | ()
  go (if-false x p1) (if-false x₁ p2) rewrite go p1 p2 = refl
  go (while-true x p1 p2) (while-true x₁ p3 p4) rewrite go p1 p3 | go p2 p4 = refl
  go (while-true x p1 p2) (while-false x₁) with trans (sym $ T→≡true x) (F→≡false x₁)
  ... | () 
  go (while-false x) (while-true x₁ p2 p3) with trans (sym $ F→≡false x) (T→≡true x₁)
  ... | () 
  go (while-false x) (while-false x₁) = refl



-- Divergence 
_divergesOn_ : St → State → Set
prog divergesOn s = ∀ {s'} → ¬ ⟨ prog , s ⟩⟱ s'

Divergent : St → Set
Divergent prog = ∀ {s} → prog divergesOn s

private
  inf-loop : Divergent (while tt do skip)
  inf-loop (while-true tt p p₁) = inf-loop p₁
  inf-loop (while-false ())  


-- Semantic equivalence
SemanticEq : St → St → Set
SemanticEq pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' ⇔ ⟨ pb , s ⟩⟱ s'

Semantic⇒ : St → St → Set
Semantic⇒ pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' → ⟨ pb , s ⟩⟱ s'

private
  prog1 : Exp bool → St → St
  prog1 b S = while b do S
  
  prog2 : Exp bool → St → St
  prog2 b S = if b then (S , while b do S) else skip
  
  progeq : ∀ {b S} → SemanticEq (prog1 b S) (prog2 b S)
  progeq {b}{S} = to , from
    where
    to : Semantic⇒ (prog1 b S) (prog2 b S)
    to (while-true x p p₁) = if-true  x (p , p₁)
    to (while-false x) = if-false  x skip
  
    from : Semantic⇒ (prog2 b S) (prog1 b S)
    from (if-true x (p1 , p2)) = while-true x p1 p2
    from (if-false {{well-scoped = ws}} x skip) = while-false {well-scoped = ws} x


private

  ⟦fac⟧ : ℕ → ℕ
  ⟦fac⟧ zero    = 1
  ⟦fac⟧ (suc n) = suc n * ⟦fac⟧ n
  
  fac-loop : St
  fac-loop =
    while lt (var "i") (var "n") do (  
      "i"   := add (lit 1) (var "i") ,
      "acc" := mul (var "i") (var "acc")
    )
  
  fac : St
  fac =
    decl "i" (lit 0) (
    decl "acc" (lit 1) (
    fac-loop ,
    "n" := var "acc"))

  fac-loop-ok :
    ∀ d i 
    → ⟨ fac-loop , 
         ("acc" , ⟦fac⟧ i      ) ∷ ("i", i    ) ∷ ("n", d + i) ∷ [] ⟩⟱ 
        (("acc" , ⟦fac⟧ (d + i)) ∷ ("i", d + i) ∷ ("n", d + i) ∷ [])

  fac-loop-ok zero i = while-false (¬A→FalseA (a≮a i))
  fac-loop-ok (suc d) i with fac-loop-ok d (suc i)
  ... | next rewrite +-suc d i = while-true  {{well-scoped = _ }}(A→TrueA $ a<sb+a i d) (ass , ass) next

  fac-ok :
    ∀ n → ⟨ fac , ("n", n) ∷ [] ⟩⟱ (("n", ⟦fac⟧ n) ∷ [])
  fac-ok n with fac-loop-ok n 0
  ... | loop-ok rewrite +-comm n 0 = decl (decl (loop-ok , ass))

