
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

{-

Here we define a Hoare logic for partial correctness of While programs (chapter 6.2). 

The most important point here is the choice of representation for predicates.

The book mention intensional and extensional approaches. In the intensional approach,
we define a separate assertion language. However, the assertion language has to be powerful
enough to be able to express useful properties of the program state, and it takes quite a bit
of work to define such a language. An advatange of the intensional approach is that we could reuse
the same assertion language to extend the object language in other ways.

The book uses the extensional approach, and so do we. We go a bit further than the book though:
the book has boolean predicates over the program state, while we have type theoretic
"(State n → Set)" predicates. This means that our predicates can be proof-relevant and contain data,
so predicates can express computations and transformations on states, not just the truth or falsity
of a property.

However, the higher-order nature of the "(State n → Set)" representation of predicates also makes
type inference quite hard. I attepmeted to do some correctness proofs with the Hoare logics, and
it's certainly feasible, but we would need a lot more machinery and lots of helper functions to
make it convenient enough.

It's interesting to note that manual proof-writing is generally easier with Hoare logics than with
raw semantics, but here in Agda it's the opposite: the proofs in raw semantics (see e. g. the
factorial proofs in Basic.SmallStep, Basic.BigStep and Extended.FunRetRec) are pretty neat, and it's
pretty convenient, since Agda keeps track of the program state for us and hides lots of unnecessary
details.

Side note: we could have made our definition universe polymorphic. It would be a trivial extension;
the reason we don't have it is that we don't need that much power of expression for any of our proofs.
Just using "Set" suffices. 

-}


{-
Predicate combinators: these just lift conjunction and implication into the State environment.
-}
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


{-
A part of exercise 6.13 (associativity of statement composition with respect to our logic).
-}

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


{-
Now we set out to prove soundess and completeness of our Hoare logic (see chapter 6.3). 

Note that we express validity of a Hoare triple in terms of the weakest liberal precondition:

  ⊨ₚ { P } S { Q }  :=   (P ==> wlp S Q)

This is just a notational conveneince, but for some reason I also find it pleasing to the eye.

-}


-- Weakest liberal precondition
------------------------------------------------------------

wlp : ∀ {n} → St n → (State n → Set) → State n → Set
wlp S Q s = ∀ {s'} → ⟨ S , s ⟩⟱ s' → Q s'


-- Soundness
------------------------------------------------------------

{-
This proof is the same as in the book, because it's rather simple and there's not
much choice
-}

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

{-
This one differs from the book proof.

The book proves the following:

  ∀ S Q → 〈 wlp S Q 〉 S 〈 Q 〉

then uses "cons" and the definition of "wlp" to infer 〈 P 〉 S 〈 Q 〉 from (P ==> wlp S Q).

We instead prove completeness directly. Our job here is essentially to recurse on sub-statements,
while making the postcondition of that statement equal to the weakest precondition of the following
statement.

As a result, the proofs for the "if_then_else_" , composition and "while" cases are all
a bit simpler than the book proofs.

In the case of "while", the book makes an unnecessary twist. It uses the law of excluded middle
on "〈 while b do S , s' 〉⟶ s''" derivations, but there's actually no need for that. It would be
indeed ugly in Agda, where we would have to assume classical logic and destroy constructivity
in order to be able to write that proof. 

-}

complete : ∀ {n}(S : St n){P Q} → (P ==> wlp S Q) → 〈 P 〉 S 〈 Q 〉
complete (x := a) f = cons (λ z → f z ass) ass id
complete skip     f = cons (λ z → f z skip) skip id

complete (S , S₁){P}{Q} f = 
    complete S {P} {wlp S₁ Q} (λ ps runS runS₁ → f ps (runS , runS₁))
  , complete S₁ id
  
complete (if b then S else S₁){P}{Q} f = 
  if (complete S  {(T ∘ ⟦ b ⟧ᵉ) ∧ P} {Q} (λ {(pb , pP) → λ runS → f pP (if-true pb runS)}))
     (complete S₁ {(F ∘ ⟦ b ⟧ᵉ) ∧ P} {Q} (λ {(pb , pP) → λ runS₁ → f pP (if-false pb runS₁)}))
     
complete (while b do S){P}{Q} f =
  cons f
    (while
      (complete S {(T ∘ ⟦ b ⟧ᵉ) ∧ W} {W}
        (λ {(pb , pw) → λ runS runW → pw (while-true pb runS runW)})))
    (λ {(pb , pw) → pw (while-false pb)})
  where W = wlp (while b do S) Q  
