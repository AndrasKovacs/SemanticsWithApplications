
module Basic.Axiomatic.Total where
 
open import Data.Bool hiding (not; if_then_else_; _∧_)
open import Data.Vec hiding ([_]; _++_; split)
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to prodMap)
open import Data.Nat
open import Relation.Nullary
open import Data.Empty
import Level as L

open import Utils.Decidable
open import Basic.AST     
open import Basic.BigStep

{-
Total axiomatic correctness (The first part of chapter 6.4). 
For general notes on axiomatic correctness see Partial.agda
The most interesting part is here is the proof of completeness (exercise 6.33).
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

  {-
  This is the only difference between the partial and total system.
  The definition is exactly the same as in the book.
  -} 
  while : 
       ∀ {b S}
     → (P : ℕ → State n → Set) 
     → (∀ n → P (suc n) ==> (T ∘ ⟦ b ⟧ᵉ))
     → (P 0 ==> (F ∘ ⟦ b ⟧ᵉ))
     → (∀ n → 〈 P (suc n) 〉 S 〈 P n 〉)
    → ---------------------------------
      〈 (λ s → ∃ λ n → P n s) 〉 while b do S 〈 P 0 〉 

  cons : 
                ∀ {P' Q' P Q S} → 
      P ==> P' → 〈 P' 〉 S 〈 Q' 〉 → Q' ==> Q 
    → -----------------------------------------
                 〈 P 〉 S 〈 Q 〉 


-- Weakest precondition
------------------------------------------------------------
wp : ∀ {n} → St n → (State n → Set) → State n → Set
wp S Q s = ∃ λ s' → ⟨ S , s ⟩⟱ s' × Q s'


-- Soundness
------------------------------------------------------------

{-
This is more complicated than the soundess proof for the partial system,
because we have to construct an actual big-step derivation.

In the "if" case we have to evaluate the branch condition to
see whether we should return an "if-true" or an "if-false"  derivation.

In the "while" case we recurse on the natural number "measure" of the loop,
building an appropriately sized derivation for the loop
-}

sound : ∀ {n}{S : St n}{P Q} → 〈 P 〉 S 〈 Q 〉 → (P ==> wp S Q)
sound skip ps = _ , skip , ps

sound ass ps =  _ , ass , ps
sound (p , p₁) ps with sound p ps
... | s'  , runp  , qs' with sound p₁ qs'
... | s'' , runp₁ , qs'' = s'' , (runp , runp₁) , qs''

sound (if {b = b} p p₁) {s} ps with ⟦ b ⟧ᵉ s | inspect ⟦ b ⟧ᵉ s
... | true  | [ b≡true  ] = 
  let Tb = ≡true→T b≡true
  in prodMap id 
       (λ x₁ → (if-true Tb (proj₁ x₁)) , (proj₂ x₁))
       (sound p {s} (Tb , ps))

... | false | [ b≡false ] = 
  let Fb = ≡false→F b≡false
  in prodMap id 
       (λ x₁ → (if-false Fb (proj₁ x₁)) , (proj₂ x₁)) 
       (sound p₁ {s} (Fb , ps))

sound (while{b = b}{S = S} P pre post decr) {s} (start , ps) = go s start ps
  where
    go : ∀ s n → P n s → wp (while b do S) (P 0) s
    go s zero    ps = s , while-false (post ps) , ps
    go s (suc n) ps with sound (decr n) ps
    ... | s' , runS , ps' with go s' n ps'
    ... | s'' , runW , ps'' = s'' , while-true (pre n ps) runS runW , ps''

sound (cons x p x₁) ps with sound p (x ps)
... | s' , runp , qs' = s' , runp , x₁ qs'


-- Completeness
------------------------------------------------------------


complete : ∀ {n}(S : St n){P Q} → (P ==> wp S Q) → 〈 P 〉 S 〈 Q 〉

complete (x := exp) {P}{Q} f = cons go ass id
  where go : P ==> (λ s → Q (s [ x ]≔ ⟦ exp ⟧ᵉ s))
        go {s} ps with f ps
        go ps | ._ , ass , qs' = qs'

complete skip {P}{Q} f = cons go skip id
  where go : P ==> Q
        go {s} ps with f ps
        go ps | x , skip , qs' = qs'

complete (S , S₁){P}{Q} f  = complete S {P} {wp S₁ Q} go , complete S₁ id
  where go : P ==> wp S (wp S₁ Q)
        go {s} ps with f ps
        go {s} ps | s' , (run , run₂) , qs' = _ , run , s' , run₂ , qs'

complete (if b then S else S₁){P}{Q} f = 
  if (complete S {(T ∘ ⟦ b ⟧ᵉ) ∧ P} {Q} go1) (complete S₁ {(F ∘ ⟦ b ⟧ᵉ) ∧ P} {Q} go2)
  where go1 : ((T ∘ ⟦ b ⟧ᵉ) ∧ P) ==> wp S Q
        go1 {s} (pb , ps) with f ps
        go1 (pb , ps) | s' , if-true pb' run , qs' = s' , run , qs'
        go1 (pb , ps) | s' , if-false pb' run , qs' with trans (sym (F→≡false pb')) (T→≡true pb)
        ... | ()

        go2 : ((F ∘ ⟦ b ⟧ᵉ) ∧ P) ==> wp S₁ Q
        go2 {s} (pb , ps) with f ps
        go2 (pb , ps) | s' , if-true pb' run , qs' with trans (sym $ F→≡false pb) (T→≡true pb')
        ... | ()
        go2 (pb , ps) | s' , if-false pb' run , qs' = s' , run , qs'
        
{-
This is the interesting part. I needed to do quite a bit of thinking to get this right.

So, we'd like to construct a proof of total corectness given the validity of a Hoare triple.

We're much less constrained here than in pretty much all of the other proofs, because our objective
is to construct a suitable P *predicate* for the loop body. Recall the axiom for "while"

  while : 
       ∀ {b S}
     → (P : ℕ → State n → Set) 
     → (∀ n → P (suc n) ==> (T ∘ ⟦ b ⟧ᵉ))
     → (P 0 ==> (F ∘ ⟦ b ⟧ᵉ))
     → (∀ n → 〈 P (suc n) 〉 S 〈 P n 〉)
    → ---------------------------------
      〈 (λ s → ∃ λ n → P n s) 〉 while b do S 〈 P 0 〉
-}
complete {n}(while b do S){P}{Q} f = cons pre-loop loop post-loop
  where
  
    {-
    P must decrease on each iteration, and P 0 must imply that the loop has finished, and
    P (suc n) must imply that the loop's still running.
    
    The only sensible choice for the decreasing loop variant is the length of the derivation
    of the loop:
    -}
    
    loop-size : ∀ {n b s s'}{S : St n} → ⟨ while b do S , s ⟩⟱ s' → ℕ
    loop-size (while-true x runS runW) = suc (loop-size runW)
    loop-size (while-false x)          = zero

    {- And now the loop predicate can be defined as: -}

    P' : ℕ → State n → Set
    P' n s = ∃₂ λ s' (runW : ⟨ while b do S , s ⟩⟱ s') → (loop-size runW ≡ n) × Q s'

    
    {- The construction of the loop body proof is slightly complicated by the fact that if we want
       to recurse on the measure "n" argument, then we have to unfold the loop derivation two layers
       deep (because the successor case for indction on "n" implies "(suc (suc n))" value for the
       derivation length -}
       
    body : ∀ n → 〈 P' (suc n) 〉 S 〈 P' n 〉
    body n = complete S (go n) 
      where
        go : ∀ n → P' (suc n) ==> wp S (P' n)
        go zero (x , while-false x₁ , () , qs')
        go zero (s''' , while-true x₁ runW (while-true x₂ runW₁ runW₂) , () , qs')
        go (suc n₂) (x , while-false x₁ , () , qs')
        go (suc n₂) (s' , while-true x₁ runW (while-false x₂) , () , qs')
        
        go zero (s' , while-true x₁ runW (while-false x₂) , psize , qs') = 
          s' , runW , s' , while-false x₂ , refl , qs'
        
        go (suc n) {s1} (slast , while-true pb1 runS1 (while-true pb2 runS2 runW2) , psize1 , qslast)
          with go n (slast , while-true pb2 runS2 runW2 , cong pred psize1 , qslast)
        ... | s2 , runS3 , s3 , runW3 , psize3 , q3 = 
          _ , runS1 , s3 , (while-true pb2 runS3 runW3) , cong suc psize3 , q3

    pre-loop : P ==> (λ s → ∃ λ n → P' n s)
    pre-loop {s} ps with f ps
    ... | s' , runW , qs' = loop-size runW , s' , runW , refl , qs'

    post-loop : P' 0 ==> Q
    post-loop (s' , while-false pb , psize , qs') = qs'
    post-loop (s' , while-true pb x₁ x₂ , () , qs')          

    loop : 〈 (λ s → ∃ λ n → P' n s) 〉 while b do S 〈 P' 0 〉
    loop = while P' pre post body 
      where
        pre : ∀ n → P' (suc n) ==> (T ∘ ⟦ b ⟧ᵉ)
        pre n (s' , while-true pb _ _ , _) = pb
        pre n (s' , while-false _ , () , qs')
    
        post : P' 0 ==> (F ∘ ⟦ b ⟧ᵉ)
        post (s' , while-true pb runS runW , () , qs')
        post (s' , while-false pb , refl , qs') = pb

