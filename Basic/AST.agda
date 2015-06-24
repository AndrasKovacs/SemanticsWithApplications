
module Basic.AST where

import Data.Bool as Bool using (not)
open import Data.Bool hiding (not; if_then_else_)
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat 
open import Data.Vec 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Utils.Decidable

{-
This module covers the first chapter of the book.

We omitted a couple of proofs that are present in the chapter. 

In particular, determinism and totality of the evaluation of expressions
is a trivial consequence of Agda's totality, so there's no need to bother
with it here. Also, the notion of "composionality" as mentioned in book corresponds
simply to structural recursion in Agda. 

Also, we skipped the proofs about the evaluation of expression with substitutions
(exercise 1.14) and contexts with substitutions (exercise 1.13), since we make
no use of these in other proofs. 
-} 

-- Our type universe (it's not a large one). 
data Ty : Set where
  bool nat : Ty

{-
Interpretation of types into Agda sets.
Note that we use natural numbers instead of integers; since naturals are
much simpler to handle in formal contexts (also, there's not enough Agda library
support for integers).
-}

⟦_⟧ᵗ : Ty → Set
⟦ nat  ⟧ᵗ = ℕ
⟦ bool ⟧ᵗ = Bool

{-
This is a point where we make a departure from the book. The book defines states as:

State = String → ℕ

This is supposed to be a total funuction, and he book doesn't concern itself with scope
errors or shadowing. But we certainly have to concern ourselves in Agda.

So we opt for de Bruijn indices as variables and a finite vector as State. These are as
simple to handle as it can get, and we also get alpha equality of programs for free.

On the flip side, we have much less readable programs.
-}

State : ℕ → Set
State = Vec ℕ 


{-
In the book there's a mutual definition of boolean and numeric expressions.
We instead have a single universe-indexed type family. It's more convenient, and
it's also actually equivalent to the mutual definition (it's a standard Agda/Haskell trick
to encode multiple types data as a single indexed type). 
-}
data Exp (n : ℕ) : Ty → Set where
  lit         : ℕ → Exp n nat
  add mul sub : Exp n nat → Exp n nat → Exp n nat
  var         : Fin n → Exp n nat
  tt ff       : Exp n bool
  eq lte lt   : Exp n nat → Exp n nat → Exp n bool
  and         : Exp n bool → Exp n bool → Exp n bool
  not         : Exp n bool → Exp n bool

  
{-
Statements are parameterized by the size of the State they operate on. Since the
vanilla "While" language has no declarations or other features that might change change
the size of the state, we are fine with this. It also allows us to use finite numbers
as de Bruijn indices.
-}

infixr 5 _:=_
infixr 4 _,_
data St (n : ℕ) : Set where
  _:=_          : Fin n → Exp n nat → St n
  skip          : St n
  _,_           : St n → St n → St n
  if_then_else_ : Exp n bool → St n → St n → St n
  while_do_     : Exp n bool → St n → St n

{-
The semantics of expressions follows the book exactly.
-}

⟦_⟧ᵉ : ∀ {n t} → Exp n t → State n → ⟦ t ⟧ᵗ
⟦ lit x   ⟧ᵉ s = x
⟦ add a b ⟧ᵉ s = ⟦ a ⟧ᵉ s + ⟦ b ⟧ᵉ s
⟦ mul a b ⟧ᵉ s = ⟦ a ⟧ᵉ s * ⟦ b ⟧ᵉ s
⟦ sub a b ⟧ᵉ s = ⟦ a ⟧ᵉ s ∸ ⟦ b ⟧ᵉ s
⟦ var x   ⟧ᵉ s = lookup x s
⟦ tt      ⟧ᵉ s = true
⟦ ff      ⟧ᵉ s = false
⟦ eq  a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s ≡⁇ ⟦ b ⟧ᵉ s ⌋
⟦ lte a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s ≤⁇ ⟦ b ⟧ᵉ s ⌋
⟦ lt  a b ⟧ᵉ s = ⌊ ⟦ a ⟧ᵉ s <⁇ ⟦ b ⟧ᵉ s ⌋
⟦ and a b ⟧ᵉ s =   ⟦ a ⟧ᵉ s ∧  ⟦ b ⟧ᵉ s 
⟦ not e   ⟧ᵉ s = Bool.not (⟦ e ⟧ᵉ s)

  
