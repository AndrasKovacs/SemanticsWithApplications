
module Basic.BigStep where
 
import Data.Bool as Bool using (not)
open import Data.Bool hiding (not; if_then_else_)
open import Data.Empty
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat 
open import Data.Nat.Properties.Simple
open import Data.Vec 
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Product
import Level as L

open import Utils.Decidable
open import Utils.NatOrdLemmas
open import Basic.AST


{-
The big-step semantics of the while language. It's chapter 2.1 in the book. 

Note that we use a {n : ℕ} parameter to fix the size of the program state over
our derivations. This is fine since we don't have and derivation rule that
changes the size of the state.

The definitions themselves should come as no surprise to readers of the book.

I employ some syntactic shenanigans to make the definitions visually similar to the familiar
sequent/natural calculus notation (I stole the formatting style from Conor McBride). 
-}

infixr 4 _,_
data ⟨_,_⟩⟱_ {n : ℕ} : St n → State n → State n → Set where

  {- "[ x ]≔ value" is just the standard library definition of vector update -}
  ass : 
                   ∀ {s x a}
    → ------------------------------------
      ⟨ x := a , s ⟩⟱ (s [ x ]≔ ⟦ a ⟧ᵉ s)

  skip : 
           ∀ {s}
    → -----------------
      ⟨ skip , s ⟩⟱ s

  _,_ :
              ∀ {s₁ s₂ s₃ S₁ S₂} → 
      ⟨ S₁ , s₁ ⟩⟱ s₂  →  ⟨ S₂ , s₂ ⟩⟱ s₃  
    → -------------------------------------
             ⟨ (S₁ , S₂ ) , s₁ ⟩⟱ s₃           

  {- The "T" in "T (⟦ b ⟧ᵉ s)" can be found in Data.Bool.Base. It's ⊤ on a true argument
     and ⊥ on a false argument, so it just lifts boolean values to irrelevant proofs.
     "F" works the same way, except it's provable on a false argument -}
  
  if-true :
             ∀ {s s' S₁ S₂ b} → 
       T (⟦ b ⟧ᵉ s)  →  ⟨ S₁ , s ⟩⟱ s'
    → -----------------------------------
       ⟨ if b then S₁ else S₂ , s ⟩⟱ s' 

  if-false :
              ∀ {s s' S₁ S₂ b} → 
       F (⟦ b ⟧ᵉ s)  →  ⟨ S₂ , s ⟩⟱ s'
    → -----------------------------------
       ⟨ if b then S₁ else S₂ , s ⟩⟱ s' 

  while-true :
                          ∀ {s s' s'' S b} → 
       T (⟦ b ⟧ᵉ s)  →  ⟨ S , s ⟩⟱ s'  →  ⟨ while b do S , s' ⟩⟱ s''
    → ----------------------------------------------------------------
                       ⟨ while b do S , s ⟩⟱ s''

  while-false :
            ∀ {s S b} → 
            F (⟦ b ⟧ᵉ s)
    → ------------------------
      ⟨ while b do S , s ⟩⟱ s


{-
Example program and program derivation below.
Note the magnificient de Bruijn variables.

Program derivations are really slow to typecheck.
Daring souls may want to uncomment it and give it a try.
But other than that, we may should that the derivations look pretty clean and concise;
there's a lot of details that Agda's inference can fill in for us. 

-}
private
  prog : St 3
  prog =
    # 2 := lit 0 ,
    while lte (var (# 1)) (var (# 0)) do
      ( # 2 := add (var (# 2)) (lit 1) ,
        # 0 := sub (var (# 0)) (var (# 1)) )

  -- -- uncomment if you dare
  -- prog-deriv :
  --   ∀ {z} → ⟨ prog , 17 ∷ 5 ∷ z ∷ [] ⟩⟱ (2 ∷ 5 ∷ 3 ∷ [])
  -- prog-deriv = 
  --   ass , 
  --   while-true tt (ass , ass) 
  --     (while-true tt (ass , ass) 
  --       (while-true tt (ass , ass) 
  --         (while-false tt)))
 


{- A program diverges on a state if there is no derivation starting from it
   Since this is big-step semantics, we can't distinguish this from being stuck -}
_divergesOnₙ_ : ∀ {n} → St n → State n → Set
prog divergesOnₙ s = ∀ {s'} → ¬ ⟨ prog , s ⟩⟱ s'

{- A program is divergent if it diverges on all states -}
Divergentₙ : ∀ {n} → St n → Set
Divergentₙ prog = ∀ {s} → prog divergesOnₙ s

{-
The fun thing about the following proof of divergence is that we implicitly
rely on the finiteness of Agda data. Since we have apparent infinite recursion
in the proof, but all inductive Agda data are finite, this implies that no such
derivation may exist in the first place.
-}

private
  inf-loopₙ : ∀ {n} → Divergentₙ {n} (while tt do skip)
  inf-loopₙ (while-true x skip p₁) = inf-loopₙ p₁
  inf-loopₙ (while-false x) = x


-- Semantic equivalence
_⇔_ : ∀ {a b} → Set a → Set b → Set (a L.⊔ b)
A ⇔ B = (A → B) × (B → A)

SemanticEq : ∀ {n} → St n → St n → Set
SemanticEq pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' ⇔ ⟨ pb , s ⟩⟱ s'

Semantic⇒ : ∀ {n} → St n → St n → Set
Semantic⇒ pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' → ⟨ pb , s ⟩⟱ s'

private  
  -- "while b do S" is equivalent to "if b then (S , while b do S) else skip"
  prog1 : ∀ {n} _ _ → St n
  prog1 b S = while b do S
  
  prog2 : ∀ {n} _ _ → St n
  prog2 b S = if b then (S , while b do S) else skip
  
  progeq : ∀ {n b S} → SemanticEq {n} (prog1 b S) (prog2 b S)
  progeq {n}{b}{S} = to , from
    where
    to : Semantic⇒ (prog1 b S) (prog2 b S)
    to (while-true x p1 p2) = if-true x (p1 , p2)
    to (while-false x) = if-false x skip 
  
    from : Semantic⇒ (prog2 b S) (prog1 b S)
    from (if-true x (p1 , p2)) = while-true x p1 p2
    from (if-false x skip) = while-false x
  
-- The semantics is deterministic. Not much to comment on. 
deterministic : 
  ∀ {n}{p : St n}{s s' s''} → ⟨ p , s ⟩⟱ s' → ⟨ p , s ⟩⟱ s'' → s' ≡ s''
deterministic = go where
  go : ∀ {p s s' s''} → ⟨ p , s ⟩⟱ s' → ⟨ p , s ⟩⟱ s'' → s' ≡ s''
  go ass ass = refl
  go skip skip = refl
  go (p1 , p2) (p3 , p4) rewrite go p1 p3 | go p2 p4 = refl
  go (if-true x p1) (if-true x₁ p2) rewrite go p1 p2 = refl
  go (if-true x p1) (if-false x₁ p2) rewrite T→≡true x = ⊥-elim x₁
  go (if-false x p1) (if-true x₁ p2) rewrite T→≡true x₁ = ⊥-elim x
  go (if-false x p1) (if-false x₁ p2) rewrite go p1 p2 = refl
  go (while-true x p1 p2) (while-true x₁ p3 p4) rewrite go p1 p3 | go p2 p4 = refl
  go (while-true x p1 p2) (while-false x₁) rewrite T→≡true x = ⊥-elim x₁
  go (while-false x) (while-true x₁ p2 p3) rewrite T→≡true x₁ = ⊥-elim x
  go (while-false x) (while-false x₁) = refl


{-
Below is a proof that is not contained in the book. I did it to familiarize myself
with style of proving in this semantics.

It proves that if we have a derivation for a loop, then we can construct a
derivation for a loop that goes on for one more iteration, because it has
a higher bound in the condition.

However, if we start out with a loop index that is already greater then the
loop bound, we get divergence. But just having a loop derivation as hypothesis
rules out divergence! We can show this to Agda by proving the divergence in that
case and getting a contradiction.
-}

private 
  loop : St 2
  loop = 
    while not (eq (var (# 0)) (var (# 1))) do 
      (# 0 := add (lit 1) (var (# 0)))
  
  once-more : 
    ∀ { i₀ lim₀ i₁} →
      ⟨ loop , i₀ ∷ lim₀     ∷ [] ⟩⟱ (i₁     ∷ lim₀     ∷ [])
    → ⟨ loop , i₀ ∷ suc lim₀ ∷ [] ⟩⟱ (1 + i₁ ∷ suc lim₀ ∷ [])
  
  once-more {i₀}{lim₀} p with cmp i₀ lim₀
  once-more (while-true x₁ ass p₁) | LT x = 
    while-true (¬A→FalseA $ a<b⟶a≢sb _ _ x) ass (once-more p₁)
  
  once-more (while-false x₁) | LT x 
    rewrite TrueA→A $ F-not-elim x₁ 
    = ⊥-elim (a≮a _ x)
  
  once-more (while-true x p p₁) | EQ refl = 
    ⊥-elim (FalseA→¬A x refl)
  
  once-more (while-false x) | EQ refl = 
    while-true (¬A→FalseA $ a≢sa _) ass (while-false (F-not-add $ A→TrueA refl))
  
  once-more p | GT x = 
    ⊥-elim (diverges x p) 
    where
    diverges : ∀ {i₀ lim₀} → lim₀ < i₀ → loop divergesOnₙ (i₀ ∷ lim₀ ∷ [])
    diverges p1 (while-true x ass p3) = diverges (<-weakenr1 _ _ p1) p3
    diverges p1 (while-false x) rewrite TrueA→A $ F-not-elim x = a≮a _ p1


{-
Correctness of a factorial program.

This task made me ponder the nature of meta- and object languages a bit.

Our job here is to prove that the factorial program computes a factorial. But in order to
be able to state this property, we had to define the notion of factorial in Agda. But this
Agda ⟦fac⟧ function is already executable! Luckily for us, Agda and Coq and co. already
have computational meaning. So if our goal is to simply have a correct factorial program,
then we should just write in in Agda or Coq.

Some languages are just better as metalanguages, but if those metalanguages are also
satisfactory as object languages then we might make do with just a single
language, instead of multiple languages and multiple semantics.

Turning back to the actual proof, note that unlike the manual factorial proof in
Chapter 6.1 of the book, this one looks pretty neat and it's also concise.
It's also structurally similar to the program itself. 
-}

module Fac where
  
  ⟦fac⟧ : ℕ → ℕ
  ⟦fac⟧ zero    = 1
  ⟦fac⟧ (suc n) = suc n * ⟦fac⟧ n
  
  fac-loop : St 3
  fac-loop =
    while lt (var (# 1)) (var (# 0)) do
        (# 1 := add (lit 1) (var (# 1)) ,
         # 2 := mul (var (# 1)) (var (# 2)) )
  
  fac : St 3
  fac =
    # 1 := lit 0 ,
    # 2 := lit 1 ,
    fac-loop 
  
  fac-loop-ok :
    ∀ d i 
    → ⟨ fac-loop , d + i ∷ i ∷ ⟦fac⟧ i ∷ [] ⟩⟱ (d + i ∷ d + i ∷ ⟦fac⟧ (d + i) ∷ [])
  fac-loop-ok zero i = while-false (¬A→FalseA $ a≮a i )
  fac-loop-ok (suc d) i with fac-loop-ok d (suc i)
  ... | next rewrite +-suc d i = while-true (A→TrueA $ a<sb+a i d) (ass , ass) next
  
  fac-ok :
    ∀ n {i acc} → ⟨ fac , n ∷ i ∷ acc ∷ [] ⟩⟱ (n ∷ n ∷ ⟦fac⟧ n ∷ [])
  fac-ok n with fac-loop-ok n 0
  ... | loop-ok rewrite +-comm n 0 = ass , ass , loop-ok


