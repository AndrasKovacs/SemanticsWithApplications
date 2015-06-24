
module Utils.NatOrdLemmas where

open import Data.Nat.Properties.Simple 
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

{- Just a bunch of lemmas about the standard ordering on naturals -}

data Cmp (a b : ℕ) : Set where
  LT : a Data.Nat.< b → Cmp a b
  EQ : a ≡ b → Cmp a b
  GT : a > b → Cmp a b

cmp : ∀ a b → Cmp a b
cmp zero zero = EQ refl
cmp zero (suc b) = LT (s≤s z≤n)
cmp (suc a) zero = GT (s≤s z≤n)
cmp (suc a) (suc b) with cmp a b
cmp (suc a) (suc b) | LT x = LT (s≤s x)
cmp (suc a) (suc .a) | EQ refl = EQ refl
cmp (suc a) (suc b) | GT x = GT (s≤s x)

a≮a : ∀ a → ¬ (a < a)
a≮a zero ()
a≮a (suc a) (s≤s p) = a≮a a p

<-weakenr1 : ∀ a b → a < b → a < suc b
<-weakenr1 zero b p = s≤s z≤n
<-weakenr1 (suc a) zero ()
<-weakenr1 (suc a) (suc b) (s≤s p) = s≤s (<-weakenr1 a b p)

<-weakenr : ∀ c a b → a < b → a < c + b
<-weakenr zero a b p = p
<-weakenr (suc c) a b p = <-weakenr1 a (c + b) (<-weakenr c a b p)

<-weakenl1 : ∀ a b → suc a < b → a < b
<-weakenl1 zero ._ (s≤s p) = s≤s z≤n
<-weakenl1 (suc a) zero ()
<-weakenl1 (suc a) (suc b) (s≤s p) = s≤s (<-weakenl1 a b p)

<-weakenl : ∀ c a b → c + a < b → a < b
<-weakenl zero a b p = p
<-weakenl (suc c) a b p = <-weakenl c a b (<-weakenl1 (c + a) b p)

a≢sa : (a : ℕ) → a ≢ suc a
a≢sa a ()

a<b⟶a≢sb : ∀ a b → a < b → a ≢ suc b
a<b⟶a≢sb zero b p1 ()
a<b⟶a≢sb (suc ._) ._ (s≤s p1) refl = a<b⟶a≢sb _ _ p1 refl

a<v⟶a≢c+b : ∀ c a b → a < b → a ≢ c + b
a<v⟶a≢c+b zero a .a p1 refl = a≮a a p1
a<v⟶a≢c+b (suc c) a b p1 p2 = a<b⟶a≢sb a (c + b) (<-weakenr c a b p1) p2

a<sb+a : ∀ a b → a < suc b + a
a<sb+a zero b = s≤s z≤n
a<sb+a (suc a) b rewrite +-suc b a = s≤s (a<sb+a a b)

a<b+sa : ∀ a b → a < b + suc a
a<b+sa a b rewrite +-suc b a = a<sb+a a b

≤-strict : ∀ a b → a ≤ b → a ≢ b → a < b
≤-strict zero zero z≤n p2 = ⊥-elim (p2 refl)
≤-strict zero (suc b) z≤n p2 = s≤s z≤n
≤-strict (suc a) zero () p2
≤-strict (suc a) (suc b) (s≤s p1) p2 = s≤s (≤-strict a b p1 (p2 ∘ cong suc))

a≢sa+b : ∀ a b → a ≢ suc a + b
a≢sa+b zero b ()
a≢sa+b (suc a) b p = a≢sa+b a b $ cong pred p

a≢sb+a : ∀ a b → a ≢ suc b + a
a≢sb+a a b p rewrite +-comm b a = a≢sa+b a b p
