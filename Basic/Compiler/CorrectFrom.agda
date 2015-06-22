
module Basic.Compiler.CorrectFrom where

open import Basic.AST
open import Basic.BigStep
open import Basic.Compiler.Code
open import Basic.Compiler.SplitCode
open import Utils.NatOrdLemmas
open import Utils.Decidable
open import Utils.Monoid

open import Data.Fin using (Fin; #_)
open import Data.Vec hiding (_∷ʳ_; _++_; [_]; _∈_; foldr)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties
open import Data.Empty
open import Data.Bool renaming (not to notBool; if_then_else_ to ifBool_then_else)
open import Data.List hiding ([_])
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
import Level as L

open import Algebra
private
  module LM {a A} = Algebra.Monoid (Data.List.monoid {a} A)

open import Relation.Unary
open import Induction.Nat
open import Induction.WellFounded


-- Well-foundedness lemmas
------------------------------------------------------------

∷ʳ-nonempty : ∀ {a}{A : Set a}(xs : List A) x → xs ∷ʳ x ≢ []
∷ʳ-nonempty [] x ()
∷ʳ-nonempty (x ∷ xs) x₁ ()

++-xs-empty : ∀ {a}{A : Set a}(xs : List A) {ys} → xs <> ys ≡ [] → xs ≡ []
++-xs-empty [] p = refl
++-xs-empty (x ∷ xs)  ()

𝓒ˢ-nonempty : ∀ {n}(S : St n) → 𝓒⟦ S ⟧ˢ ≢ []
𝓒ˢ-nonempty (x := x₁)             = ∷ʳ-nonempty 𝓒⟦ x₁ ⟧ᵉ (STORE x) 
𝓒ˢ-nonempty (S , S₁)              = 𝓒ˢ-nonempty S ∘ ++-xs-empty 𝓒⟦ S ⟧ˢ
𝓒ˢ-nonempty (if x then S else S₁) = ∷ʳ-nonempty 𝓒⟦ x ⟧ᵉ (BRANCH 𝓒⟦ S ⟧ˢ 𝓒⟦ S₁ ⟧ˢ)
𝓒ˢ-nonempty (while x do S) ()
𝓒ˢ-nonempty skip ()

𝓒-Exp-nonempty : ∀ {n t} (e : Exp n t) → 𝓒⟦ e ⟧ᵉ ≢ []
𝓒-Exp-nonempty (add e e₁)     = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) ADD
𝓒-Exp-nonempty (mul e e₁)     = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) MUL
𝓒-Exp-nonempty (sub e e₁)     = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) SUB
𝓒-Exp-nonempty (eq e e₁)      = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) EQ
𝓒-Exp-nonempty (lte e e₁)     = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) LTE
𝓒-Exp-nonempty (lt e e₁)      = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) LT
𝓒-Exp-nonempty (Exp.and e e₁) = ∷ʳ-nonempty (𝓒⟦ e₁ ⟧ᵉ <> 𝓒⟦ e ⟧ᵉ) AND
𝓒-Exp-nonempty (not e)        = ∷ʳ-nonempty 𝓒⟦ e ⟧ᵉ NOT
𝓒-Exp-nonempty (lit x) ()
𝓒-Exp-nonempty (var x) ()
𝓒-Exp-nonempty tt ()
𝓒-Exp-nonempty ff ()

▷*-S-nonempty : 
  ∀ {n S}{s s' : State n}{e e'} (p : ⟨ 𝓒⟦ S ⟧ˢ , e , s ⟩▷*⟨ [] , e' , s' ⟩)
  → ▷*-length p ≢ 0
▷*-S-nonempty{_}{S} p x with 𝓒ˢ-nonempty S | 𝓒⟦ S ⟧ˢ | inspect 𝓒⟦_⟧ˢ S
▷*-S-nonempty done x      | ¬empty | []     | [ remember ] = ¬empty remember
▷*-S-nonempty (() ∷ p) x₁ | ¬empty | []     | [ remember ]
▷*-S-nonempty (x₁ ∷ p) () | ¬empty | x ∷ cs | [ remember ]

a<′a+sb : ∀ a b → b ≢ 0 → a <′ a + b
a<′a+sb a zero x = ⊥-elim (x refl)
a<′a+sb a (suc b) x rewrite +-comm a (suc b) = ≤⇒≤′ $ a<sb+a a b

a<′b+sa : ∀ a b → a <′ b + suc a
a<′b+sa a zero    = ≤′-refl
a<′b+sa a (suc b) = ≤′-step (a<′b+sa a b)

≤′-weaken-l : ∀ {a b} c → a ≤′ b → a ≤′ c + b
≤′-weaken-l zero p = p
≤′-weaken-l (suc c) p = ≤′-step (≤′-weaken-l c p)


-- Correctness
------------------------------------------------------------

𝓒-correct-from-Ty : {_ : ℕ} → ℕ → Set
𝓒-correct-from-Ty {n} size =
    ∀ {S : St n} {e s s'}
    → (p : ⟨ 𝓒⟦ S ⟧ˢ , [] , s ⟩▷*⟨ [] , e , s' ⟩)
    → size ≡ ▷*-length p
    → ⟨ S , s ⟩⟱ s' × e ≡ []

𝓒-correct-from : ∀ {n} size → 𝓒-correct-from-Ty {n} size
𝓒-correct-from {n} = <-rec _ go where

  -- -- Assignment
  go : ∀ size → (∀ y → y <′ size → 𝓒-correct-from-Ty {n} y) → 𝓒-correct-from-Ty {n} size
  go size recurse {x := exp}{e}{s} p sizeEq 
    with ▷*-split 𝓒⟦ exp ⟧ᵉ p | 𝓒-Exp-nat {e = []}{s = s} exp
  go size recurse {.x := exp} p sizeEq | s₁ , ._ , p1 , STORE x ∷ () ∷ p2 , eqn | exp'
  go size recurse {.x := exp} p sizeEq | s₁ , ._ , p1 , STORE x ∷ done , eqn | exp' 
    with ▷*-deterministic p1 exp'
  ... | _ , eqe , eqs 
    rewrite eqs 
    with ∷-injective eqe
  ... | eq-cond , e≡[] 
    rewrite nat-inj eq-cond 
    = ass , e≡[]
  
  -- Skip 
  go size recurse {skip} (NOOP ∷ done) sizeEq = skip , refl
  go size recurse {skip} (NOOP ∷ () ∷ p) sizeEq

  -- Sequencing
  go size recurse {S , S₁} p sizeEq 
    with ▷*-split 𝓒⟦ S ⟧ˢ p
  ... | s'' , e'' , p1 , p2 , size+eq
    rewrite sizeEq | sym size+eq
    with recurse _ (a<′a+sb _ _ (▷*-S-nonempty {S = S₁} p2)) {S} p1 refl
  ... | p1' , e''≡[] 
    rewrite e''≡[] | +-comm (▷*-length p1) (▷*-length p2) 
    with recurse _ (a<′a+sb _ _ (▷*-S-nonempty {S = S} p1)) {S₁} p2 refl
  ... | p2' , e≡[] = (p1' , p2') , e≡[]

  -- If then else
  go size recurse {if b then S else S₁} {e}{s}{s'} p sizeEq 
    with ▷*-split 𝓒⟦ b ⟧ᵉ p | 𝓒-Exp-bool {e = []}{s = s} b
  ... | s'' , ._ , p1 , BRANCH ∷ p2 , size+eq | b' 
    with ▷*-deterministic p1 b' 
  ... | _ , eqe , eqs 
    rewrite eqs 
    with ∷-injective eqe
  ... | eq-cond , e'≡[] 
    rewrite bool-inj eq-cond | e'≡[] | 
           proj₂ LM.identity (ifBool ⟦ b ⟧ᵉ s then 𝓒⟦ S ⟧ˢ else 𝓒⟦ S₁ ⟧ˢ) 
           | sizeEq | sym size+eq 
    with ⟦ b ⟧ᵉ s | inspect ⟦ b ⟧ᵉ s

  ... | true  | [ condTrue  ] 
    = (if-true (≡true→T condTrue) (proj₁ rest)) , proj₂ rest
    where rest : ⟨ S , s ⟩⟱ s' × e ≡ []
          rest = recurse (▷*-length p2) (a<′b+sa (▷*-length p2) (▷*-length p1)) p2 refl

  ... | false | [ condFalse ] 
    = (if-false (≡false→F condFalse) (proj₁ rest)) , proj₂ rest
    where rest : ⟨ S₁ , s ⟩⟱ s' × e ≡ []
          rest = recurse (▷*-length p2) (a<′b+sa (▷*-length p2) (▷*-length p1)) p2 refl    
        
  -- While
  go size recurse {while b do S}{e}{s}{s'} (LOOP ∷ p) sizeEq
    with 𝓒-Exp-bool {e = []}{s = s} b | ▷*-split 𝓒⟦ b ⟧ᵉ p
  ... | b' | s'' , ._ , p1 , BRANCH ∷ p2 , size+eq 
    with ▷*-deterministic p1 b'
  ... | _ , eqe , eqs
    rewrite eqs 
    with ∷-injective eqe
  ... | eq-cond , e'≡[] 
    rewrite bool-inj eq-cond | e'≡[] |
       proj₂ LM.identity (ifBool ⟦ b ⟧ᵉ s then 𝓒⟦ S ⟧ˢ ++ LOOP 𝓒⟦ b ⟧ᵉ 𝓒⟦ S ⟧ˢ ∷ [] else (NOOP ∷ []))
       | sym size+eq | sizeEq
    with ⟦ b ⟧ᵉ s | inspect ⟦ b ⟧ᵉ s

  -- while-true (damnit, I want an arithmetic inequality solver)
  ... | true  | [ condTrue  ] = 𝓒-while-true condTrue p2 refl
    where
      𝓒-while-true :
        ∀ {s s' : State n}{b e S}
        → ⟦ b ⟧ᵉ s ≡ true
        → (p3 : ⟨ 𝓒⟦ S ⟧ˢ ++ LOOP 𝓒⟦ b ⟧ᵉ 𝓒⟦ S ⟧ˢ ∷ [] , [] , s ⟩▷*⟨ [] , e , s' ⟩)
        → (▷*-length p3 ≡ ▷*-length p2)
        → (⟨ while b do S , s ⟩⟱ s') × e ≡ []
      𝓒-while-true {s}{s'}{b}{e}{S} condTrue p3 ≡len
        with ▷*-split 𝓒⟦ S ⟧ˢ p3
      ... | s'' , e'' , p1_new , p2_new , size+eq 
        rewrite sym size+eq 
        with recurse (▷*-length p1_new) 
          (≤′-step 
            (subst (λ x → suc (▷*-length p1_new) ≤′ ▷*-length p1 + suc x) ≡len
               (≤′-weaken-l (▷*-length p1)
                  (≤′-step (a<′a+sb (▷*-length p1_new) (▷*-length p2_new) 
                    (▷*-S-nonempty {S = while b do S} p2_new)))))) 
          {S} p1_new refl

      ... | p1' , e''≡[]
        rewrite e''≡[] 
        with recurse (▷*-length p2_new) 
          (≤′-step (subst (λ x → suc (▷*-length p2_new) ≤′ ▷*-length p1 + suc x) ≡len
               (≤′-weaken-l (▷*-length p1) 
                 (≤′-step (
                   subst 
                     (λ x → ▷*-length p2_new <′ x) 
                     (+-comm (▷*-length p2_new) (▷*-length p1_new)) 
                     (a<′a+sb 
                         (▷*-length p2_new) (▷*-length p1_new) 
                         (▷*-S-nonempty {S = S} p1_new)))))))                                   
          {while b do S} p2_new refl
      ... | p2' , e≡[] = (while-true (≡true→T condTrue) p1' p2') , e≡[]
   
  -- while-false
  ... | false | [ condFalse ] = 𝓒-while-false condFalse p2
    where
      𝓒-while-false : 
        ∀ {n}{s s' : State n}{e b S}
        → ⟦ b ⟧ᵉ s ≡ false
        → ⟨ NOOP ∷ [] , [] , s ⟩▷*⟨ [] , e , s' ⟩ 
        → (⟨ while b do S , s ⟩⟱ s' × e ≡ [])
      𝓒-while-false f (NOOP ∷ done) = (while-false (≡false→F f)) , refl
      𝓒-while-false f (NOOP ∷ () ∷ p)
