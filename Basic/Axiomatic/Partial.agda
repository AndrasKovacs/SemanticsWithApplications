
module Basic.Axiomatic.Partial where
 
open import Data.Bool hiding (not; if_then_else_; _∧_)
open import Data.Vec hiding ([_]; _++_; split)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
import Level as L

open import Utils.Decidable
open import Basic.AST     
open import Basic.BigStep

-- Predicate combinators
_∧_ : 
  ∀ {α β γ}{A : Set α}
  → (A → Set β)
  → (A → Set γ)
  → (A → Set _)
_∧_ f g x = f x × g x

_==>_ : 
  ∀ {α β γ}{A : Set α}
  → (A → Set β)
  → (A → Set γ)
  → Set _
_==>_ f g = ∀ {x} → f x → g x     
 


infixr 4 _,_
data 〈_〉_〈_〉 {n} : (State n → Set) → St n → (State n → Set) → Set₁ where


  skip : 
           ∀ {P}
    → -----------------
      〈 P 〉 skip 〈 P 〉 

  ass :
                        ∀ {x a P}
    → ----------------------------------------------
      〈 (λ s → P (s [ x ]≔ ⟦ a ⟧ᵉ s)) 〉 x := a 〈 P 〉

  _,_ : 
             ∀ {P Q R S₁ S₂} → 
      〈 P 〉 S₁ 〈 Q 〉 → 〈 Q 〉 S₂ 〈 R 〉 
    → --------------------------------
            〈 P 〉 S₁ , S₂ 〈 R 〉 

  if : 
                          ∀ {P Q b S₁ S₂} →
      〈 (T ∘ ⟦ b ⟧ᵉ) ∧ P 〉 S₁ 〈 Q 〉 → 〈 (F ∘ ⟦ b ⟧ᵉ) ∧ P 〉 S₂ 〈 Q 〉
    → --------------------------------------------------------------
                  〈 P 〉 if b then S₁ else S₂ 〈 Q 〉 

  while : 
                   ∀ {P b S} → 
          〈 (T ∘ ⟦ b ⟧ᵉ) ∧ P 〉 S 〈 P 〉 
    → ----------------------------------------
      〈 P 〉 while b do S 〈 (F ∘ ⟦ b ⟧ᵉ) ∧ P 〉 

  cons : 
                ∀ {P' Q' P Q S} → 
      P ==> P' → 〈 P' 〉 S 〈 Q' 〉 → Q' ==> Q 
    → -----------------------------------------
                 〈 P 〉 S 〈 Q 〉 


-- Annotate current 



-- Exercise equivalence proof
------------------------------------------------------------

split :
  ∀ {n P R}{S₁ S₂ : St n}
  → 〈 P 〉 S₁ , S₂ 〈 R 〉
  → ∃ λ Q
  → (〈 P 〉 S₁ 〈 Q 〉) × (〈 Q 〉 S₂ 〈 R 〉)
split (p , p₁) = _ , (p , p₁)
split (cons x p y) with split p
... | Q , (p1 , p2)  = Q , (cons x p1 id , cons id p2 y)
    
ex-613a : 
  ∀ {n P Q}{S₁ S₂ S₃ : St n}
  → 〈 P 〉 S₁ , (S₂ , S₃) 〈 Q 〉
  → 〈 P 〉 (S₁ , S₂) , S₃ 〈 Q 〉
ex-613a (p , p₁) with split p₁
... | _ , (p₁₁ , p₁₂) = (p , p₁₁) , p₁₂
ex-613a (cons x p x₁) = cons x (ex-613a p) x₁

ex-613b :
  ∀ {n P Q}{S₁ S₂ S₃ : St n}
  → 〈 P 〉 (S₁ , S₂) , S₃ 〈 Q 〉
  → 〈 P 〉 S₁ , (S₂ , S₃) 〈 Q 〉
ex-613b (p₁ , p₂) with split p₁
... | _ , (p₁₁ , p₁₂) = p₁₁ , (p₁₂ , p₂)
ex-613b (cons x p x₁) = cons x (ex-613b p) x₁


-- Weakest liberal precondition
------------------------------------------------------------

wlp : ∀ {n} → St n → (State n → Set) → State n → Set
wlp S Q s = ∀ {s'} → ⟨ S , s ⟩⟱ s' → Q s'


-- Soundness
------------------------------------------------------------

sound : ∀ {n}{S : St n}{P Q} → 〈 P 〉 S 〈 Q 〉 → (P ==> wlp S Q)
sound skip ps skip                         = ps
sound ass ps ass                           = ps
sound (p , p₁) ps (run , run₁)             = sound p₁ (sound p ps run) run₁
sound (if p p₁) ps (if-true x run)         = sound p (x , ps) run
sound (if p p₁) ps (if-false x run)        = sound p₁ (x , ps) run
sound (while p) ps (while-true x run run₁) = sound (while p) (sound p (x , ps) run) run₁
sound (while p) ps (while-false x)         = x , ps
sound (cons x p x₁) ps run                 = x₁ (sound p (x ps) run)


-- Completeness
------------------------------------------------------------

complete : ∀ {n}(S : St n){P Q} → (P ==> wlp S Q) → 〈 P 〉 S 〈 Q 〉
complete (x := a) f = cons (λ z → f z ass) ass id
complete skip     f = cons (λ z → f z skip) skip id
complete (S , S₁){P}{Q} f = 
    complete S {P} {wlp S₁ Q} (λ ps runS runS₁ → f ps (runS , runS₁))
  , complete S₁ id
complete (if b then S else S₁){P}{Q} f = 
  if (complete S {(T ∘ ⟦ b ⟧ᵉ) ∧ P} {Q}  (λ {(pb , pP) → λ runS → f pP (if-true pb runS)}))
     (complete S₁ {(F ∘ ⟦ b ⟧ᵉ) ∧ P} {Q} (λ {(pb , pP) → λ runS₁ → f pP (if-false pb runS₁)}))

complete (while b do S){P}{Q} f = 
  cons f (while (cons lemma (complete S {wlp S W} {W} id) id)) (λ {(pb , pQ') → pQ' (while-false pb)})
  where
    W = wlp (while b do S) Q
    lemma : ((T ∘ ⟦ b ⟧ᵉ) ∧ W) ==> wlp S W
    lemma (pb , pw) runS runW = pw (while-true pb runS runW)


