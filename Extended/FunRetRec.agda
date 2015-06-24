 
module Extended.FunRetRec where

open import Function
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String
open import Data.Product
open import Data.Bool renaming (not to bnot) hiding (if_then_else_)
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.List hiding (and; or)
open import Data.List.Properties using (∷-injective)
open import Data.Empty
open import Data.Unit
import Level as L

open import Utils.Decidable
open import Utils.Monoid
open import Utils.NatOrdLemmas

{-
This module contains an extension of the While language and assorted semantics.
It incorporates some  of the suggested extra features in the book.

The extra features in short:

  - Function calls and recursive local function declarations
  - Local variable declarations
  - String-based bindings with name shadowing
  - Return statements with the usual jump in control flow
-}


-- Data definitions
--------------------------------------------------

data Ty : Set where
  bool nat : Ty

⟦_⟧ᵗ : Ty → Set
⟦ nat  ⟧ᵗ = ℕ
⟦ bool ⟧ᵗ = Bool

data Exp : Ty → Set where
  lit         : ℕ → Exp nat
  add mul sub : Exp nat → Exp nat → Exp nat
  var         : String → Exp nat

  {-
  Function calls. Note that we have calls as a proper *expression* that
  evaluate to a value, if they terminate. This also implies that the evaluation
  of expressions has a partial semantics just like statements.

  We apply a function to a list of arguments. The number of args must be correct.
  -}
  _$:_        : String → List (Exp nat) → Exp nat
  
  tt ff       : Exp bool
  eq lt lte   : Exp nat → Exp nat → Exp bool
  and         : Exp bool → Exp bool → Exp bool
  not         : Exp bool → Exp bool
  or          : Exp bool → Exp bool → Exp bool

infixr 4 _,_
infixr 5 _:=_
data St : Set where

  {- Function declarations. We specify the arguments as a list of bindings.
  They are recursive. -}
  fun           : String → List String → St → St → St

  {- variable declarations -}  
  decl          : String → Exp nat → St → St
  
  _:=_          : String → Exp nat → St
  skip          : St
  _,_           : St → St → St
  if_then_else_ : Exp bool → St → St → St
  while_do_     : Exp bool → St → St
  ret           : Exp nat → St


{- The environment contains numbers and functions -}
data Entry : Set where
  nat : ℕ → Entry
  fun : List String → St → Entry

{- The environment is now keyed by string (rather than de Bruijn indices) -}
Env : Set
Env = List (String × Entry)

_,ₙ_ : String → ℕ → (String × Entry)
v ,ₙ n = v , nat n
infixr 5 _,ₙ_

{-
A note on the return statement:

The book recommends two way for dealing with exceptions and jumps.

One way is to use small-step semantics. The other way is to introduce new program
states in big-step semantics. With more complicated derivation rules and many
types of non-local effects (and of course non-determinism), small-step semantics
seems to be more manageable.

But here we have just the return statement, so we are fine with an extra state
and big-step semantics.
-}

data State : Set where
  ok  : Env → State
  ret : ℕ → State

ret-inj : ∀ {a b} → (State ∋ ret a) ≡ ret b → a ≡ b
ret-inj refl = refl

ok-inj : ∀ {s s'} → ok s ≡ ok s' → s ≡ s'
ok-inj refl = refl


-- Well-scopedness
--------------------------------------------------


{-
Scoping rules are nontrivial, but we don't want to clutter our derivations
with explicit proofs for them.

A standard Agda solution for this is to use so-called irrelevant proofs. Such
types have at most a single value up to definitional equality, therefore they
cannot influence actual computation. Agda is willing to automatically fill in
the value for these types once it becomes apparent that the value exists.

The simplest example of a irrelevant type is the unit type.

  record ⊤ : Set where constructor tt. 

Agda has eta-extensionality for records, so Agda thinks that any value of
type ⊤ is definitionally equal to "tt".

The well-scopedness predicates below all compute to ⊤ or ⊥ (the unprovable type),
and both are irrelevant, so we get all the scoping proofs nicely inferred
and hidden.

We also augment our inference system with judicious use of instance arguments.
Agda tries to search for suitable values for these arguments from the current scope.
-}

------------------------------------------------------------

{-
A note on static semantics:

Arguably, well-scopedness should belong to static semantics. After all,
it can be checked without running the program, and in real compilers
scope checking also tends to be done statically.

Here, we don't *have* static semantics at all. The static semantic rules are baked into
the dynamic semantic rules. Adding proper static semantics would be one of the many potential
extensions and improvements to this library.

Ideally, we would have a completely raw AST, and an AST for code that is correct
with respect to static semantics (so it's annotated with proofs of static correctness).

We would also have a type checker function that would decide if a raw AST can be converted
to the correct AST. It would also nice to have a type erasure function that goes in the opposite
direction (erases proofs and returns a raw AST), and we could establish correctness of type
checking with respect to erasure, for example by proving that checking is the left inverse
of erasure.

It may be also the case, although I haven't tested it, that type checking would be faster
with a separate checked AST.
-}


-- variable is in scope
InScopeVar : String → Env → Set
InScopeVar v [] = ⊥
InScopeVar v ((_ , fun _ _) ∷ s) = InScopeVar v s
InScopeVar v ((v' , nat n)  ∷ s) with v ≡⁇ v'
... | yes _ = ⊤
... | no  _ = InScopeVar v s

-- function is in scope
InScopeFun : String → Env → Set
InScopeFun v [] = ⊥
InScopeFun v ((_ , nat _) ∷ s) = InScopeFun v s
InScopeFun v ((v' , fun _ _) ∷ s) with v ≡⁇ v'
... | yes _ = ⊤
... | no  _ = InScopeFun v s

lookupVar : ∀ v s ⦃ _ : InScopeVar v s ⦄ → ℕ
lookupVar v [] ⦃ ⦄
lookupVar v ((_ , fun _ _) ∷ s) = lookupVar v s 
lookupVar v ((v' , nat n) ∷ s) with v ≡⁇ v'
... | yes _ = n
... | no  _ = lookupVar v s

lookupFun : ∀ f s ⦃ _ : InScopeFun f s ⦄ → List String × St
lookupFun v [] ⦃ ⦄
lookupFun v ((_ , nat _) ∷ s) = lookupFun v s
lookupFun v ((v' , fun args body) ∷ s) with v ≡⁇ v'
... | yes _ = args , body
... | no  _ = lookupFun v s

-- perform a substitution on the environment at a name that is in scope
_[_]≔_ : ∀ s v ⦃ _ : InScopeVar v s ⦄ → ℕ → Env
_[_]≔_ [] _ ⦃ ⦄ _
_[_]≔_ ((v' , fun args body) ∷ s) v n = (v' , fun args body) ∷ (s [ v ]≔ n)
((v' , nat n) ∷ Γ) [ v ]≔ n' with v ≡⁇ v'
... | yes p = (v' , nat n') ∷ Γ
... | no ¬p = (v' , nat n ) ∷ Γ [ v ]≔ n'

-- Match the length of two lists
ArgLenMatch : List String → List ℕ → Set
ArgLenMatch []          []         = ⊤
ArgLenMatch []          (_ ∷ _)    = ⊥
ArgLenMatch (_ ∷ names) []         = ⊥
ArgLenMatch (_ ∷ names) (_ ∷ vals) = ArgLenMatch names vals

-- Create a new environment with the function arguments pushed to the front
callWith : ∀ args vals ⦃ _ : ArgLenMatch args vals ⦄ → Env
callWith []          []         = []
callWith []          (_ ∷ _) ⦃ ⦄
callWith (_ ∷ _)     []      ⦃ ⦄
callWith (n ∷ names) (v ∷ vals) = (n , nat v) ∷ callWith names vals


-- Semantics
--------------------------------------------------

mutual
  -- Evaluation of argument lists
  infixr 5 _∷_
  data _⟨_⟩ᵃ⟱_ (s : Env) : List (Exp nat) → List ℕ → Set where

    []  : 
      ----------------
       s ⟨ [] ⟩ᵃ⟱ []

    _∷_ : 
              ∀ {a args v vals} → 
        s ⟨ a ⟩ᵉ⟱ v  →  s ⟨ args ⟩ᵃ⟱ vals 
      → ---------------------------------
          s ⟨ a ∷ args ⟩ᵃ⟱ (v ∷ vals)

  
  -- Shorthand for the evaluation of binary expressions
  BinExp : ∀ {s t r} → (Exp t → Exp t → Exp r) → (⟦ t ⟧ᵗ → ⟦ t ⟧ᵗ → ⟦ r ⟧ᵗ) → Set
  BinExp {s} cons op = 
         ∀ {a b va vb} → 
    s ⟨ a ⟩ᵉ⟱ va → s ⟨ b ⟩ᵉ⟱ vb 
    -----------------------------
    → s ⟨ cons a b ⟩ᵉ⟱ (op va vb)


  -- Evaluation of expressions
  data _⟨_⟩ᵉ⟱_ (s : Env) : ∀ {t} → Exp t → ⟦ t ⟧ᵗ → Set where

    add : BinExp add _+_
    eq  : BinExp eq (λ a b → ⌊ a ≡⁇ b ⌋)
    lt  : BinExp lt (λ a b → ⌊ suc a ≤⁇ b ⌋)
    lte : BinExp lte (λ a b → ⌊ a ≤⁇ b ⌋)
    and : BinExp and _∧_
    or  : BinExp or  _∨_ 
    mul : BinExp mul _*_
    sub : BinExp sub _∸_
    tt  : s ⟨ tt ⟩ᵉ⟱ true
    ff  : s ⟨ ff ⟩ᵉ⟱ false
    lit : ∀ {n} → s ⟨ lit n ⟩ᵉ⟱ n
    not : ∀ {e b} → s ⟨ e ⟩ᵉ⟱ b → s ⟨ not e ⟩ᵉ⟱ bnot b            

    var : 
              ∀ {v in-scope}
      → ----------------------------
        s ⟨ var v ⟩ᵉ⟱ lookupVar v s

    {- Evaluation of function calls -}
    _$:_ : 
        {retVal       : ℕ}               
        {argVals      : List ℕ}
        {f            : String}          -- if we have a function
        {args         : List (Exp nat)}  -- and a list of arguments
        ⦃ in-scope-f  : InScopeFun f s ⦄ -- and the function is in scope

        → let func     = lookupFun f s   
              argNames = proj₁ func       
              body     = proj₂ func in 

           s ⟨ args ⟩ᵃ⟱ argVals -- we can evaluate the arguments
        →  ⦃ arg-len-match : ArgLenMatch argNames argVals ⦄ -- and the number of arguments is correct

       -- note the recursive occurence in the call environement ⇓ 
        → let callEnv = callWith argNames argVals <> [ (f , fun argNames body) ] in

         ⟨ body , ok callEnv ⟩⟱ ret retVal
      → -----------------------------------   -- then a function call evaluates to the return value
           s ⟨ f $: args ⟩ᵉ⟱ retVal           -- of the function body evaluated in the call environment
  
  -- Evaluation of statements
  data ⟨_,_⟩⟱_ : St → State → State → Set where

    fun : 
                           ∀ {x s s' S args body} → 
        ⟨ S , ok ((x , fun args body) ∷ s) ⟩⟱ ok ((x , fun args body) ∷ s')
      → -------------------------------------------------------------------
                      ⟨ fun x args body S , ok s ⟩⟱ ok s'

    {-- This rule propagates ("rethrows") the return statement's effect if it happens inside the
        scope of the function declaration --}
    fun-ret : 
                 ∀ {x s r S args body} → 
        ⟨ S , ok ((x , fun args body) ∷ s) ⟩⟱ ret r
      → --------------------------------------------
           ⟨ fun x args body S , ok s ⟩⟱ ret r

    {- variable declarations -}
    decl :
                  ∀ {s s' S x e eVal e'} → 
                     s ⟨ e ⟩ᵉ⟱ eVal → 
       ⟨ S , ok ((x , nat eVal) ∷ s) ⟩⟱ (ok ((x , e') ∷ s'))
      → ----------------------------------------------------
                  ⟨ decl x e S , ok s ⟩⟱ ok s'

    {- variable declarations propagating the return statement -}
    decl-ret :
               ∀ {r s S x e eVal} → 
                 s ⟨ e ⟩ᵉ⟱ eVal → 
        ⟨ S , ok ((x , nat eVal) ∷ s) ⟩⟱ ret r
      → ---------------------------------------
           ⟨ decl x e S , ok s ⟩⟱ ret r
       
    ret :
              ∀ {e eVal s}
            → s ⟨ e ⟩ᵉ⟱ eVal
      → ---------------------------
        ⟨ ret e , ok s ⟩⟱ ret eVal
       
    ass : 
              ∀ {s e eVal x in-scope} → 
                  s ⟨ e ⟩ᵉ⟱ eVal 
      → --------------------------------------
        ⟨ x := e , ok s ⟩⟱ ok (s [ x ]≔ eVal)
       
    skip : 
             ∀ {s} 
      → -----------------
        ⟨ skip , s ⟩⟱ s    
       
    _,_ :
                ∀ {s₁ s₂ s₃ S₁ S₂} → 
        ⟨ S₁ , s₁ ⟩⟱ ok s₂  →  ⟨ S₂ , ok s₂ ⟩⟱ s₃  
      → --------------------------------------
               ⟨ (S₁ , S₂ ) , s₁ ⟩⟱ s₃

    {-- If we return in the left statement of a composite statement,
        then we ignore the right statement and just return -}        
    _ret,_ :
                 ∀ {x s₁ s₂ S₁ S₂} → 
        ⟨ S₁ , s₁ ⟩⟱ ret x  →  ⟨ S₂ , ret x ⟩⟱ s₂
      → ---------------------------------------
            ⟨ (S₁ , S₂ ) , s₁ ⟩⟱ ret x
       
    if-true :
                ∀ {s s' S₁ S₂ b} →
        s ⟨ b ⟩ᵉ⟱ true  →  ⟨ S₁ , ok s ⟩⟱ s'
      → ------------------------------------
        ⟨ if b then S₁ else S₂ , ok s ⟩⟱ s' 

    if-false :
                 ∀ {s s' S₁ S₂ b} → 
        s ⟨ b ⟩ᵉ⟱ false  →  ⟨ S₂ , ok s ⟩⟱ s'
      → -------------------------------------
        ⟨ if b then S₁ else S₂ , ok s ⟩⟱ s' 
 
    while-true :
                           ∀ {s s' s'' S b} → 
       s ⟨ b ⟩ᵉ⟱ true  →  ⟨ S , ok s ⟩⟱ s'  →  ⟨ while b do S , s' ⟩⟱ s''
      → ------------------------------------------------------------------
                       ⟨ while b do S , ok s ⟩⟱ s''
       
    while-false :
                 ∀ {s S b} → 
              s ⟨ b ⟩ᵉ⟱ false 
      → ------------------------------
        ⟨ while b do S , ok s ⟩⟱ ok s


        
substExp : ∀ {t s}{e : Exp t}{v v'} → v ≡ v' → s ⟨ e ⟩ᵉ⟱ v → s ⟨ e ⟩ᵉ⟱ v'
substExp refl p2 = p2



-- State transition is deterministic
--------------------------------------------------

deterministic : ∀ {S s s' s''} → ⟨ S , s ⟩⟱ s' → ⟨ S , s ⟩⟱ s'' → s' ≡ s''
deterministic = st where 
  mutual
    args : ∀ {s as vs vs'} → s ⟨ as ⟩ᵃ⟱ vs → s ⟨ as ⟩ᵃ⟱ vs' → vs ≡ vs'
    args [] [] = refl
    args (x ∷ p1) (x₁ ∷ p2) rewrite exp x x₁ | args p1 p2 = refl

    exp : ∀ {t s}{e : Exp t}{v v'} → s ⟨ e ⟩ᵉ⟱ v → s ⟨ e ⟩ᵉ⟱ v' → v ≡ v'
    exp (add p1 p2) (add p3 p4) rewrite exp p1 p3 | exp p2 p4 = refl
    exp (sub p1 p2) (sub p3 p4) rewrite exp p1 p3 | exp p2 p4 = refl    
    exp (eq p1 p2)  (eq p3 p4)  rewrite exp p1 p3 | exp p2 p4 = refl
    exp (lt p1 p2)  (lt p3 p4)  rewrite exp p1 p3 | exp p2 p4 = refl
    exp (lte p1 p2) (lte p3 p4) rewrite exp p1 p3 | exp p2 p4 = refl
    exp (and p1 p2) (and p3 p4) rewrite exp p1 p3 | exp p2 p4 = refl
    exp (or p1 p2)  (or p3 p4)  rewrite exp p1 p3 | exp p2 p4 = refl
    exp (mul p1 p2) (mul p3 p4) rewrite exp p1 p3 | exp p2 p4 = refl
    exp tt tt = refl
    exp ff ff = refl
    exp lit lit = refl
    exp (not p1) (not p2) rewrite exp p1 p2 = refl
    exp var var = refl
    exp (_$:_ ae be) (_$:_ ae' be') rewrite args ae ae' = ret-inj (st be be')
    
    st : ∀ {S s s' s''} → ⟨ S , s ⟩⟱ s' → ⟨ S , s ⟩⟱ s'' → s' ≡ s''
    st (fun p1) (fun p2) = cong ok $ proj₂ $ ∷-injective $ ok-inj $ st p1 p2
    st (fun p1) (fun-ret p2) with st p1 p2
    ... | ()
    st (fun-ret p1) (fun p2) with st p1 p2
    ... | ()
    st (fun-ret p1) (fun-ret p2) = st p1 p2
    st (decl x₁ p1) (decl x₂ p2) rewrite 
      exp x₁ x₂ = cong ok $ proj₂ $ ∷-injective $ ok-inj $ st p1 p2
    st (decl x₁ p1) (decl-ret x₂ p2) rewrite exp x₁ x₂ with st p1 p2
    ... | ()
    st (decl-ret x₁ p1) (decl x₂ p2) rewrite exp x₁ x₂ with st p1 p2
    ... | () 
    st (decl-ret x₁ p1) (decl-ret x₂ p2) rewrite exp x₁ x₂ = st p1 p2
    st (ret x) (ret x₁) rewrite exp x x₁ = refl
    st (ass x₁) (ass x₂) rewrite exp x₁ x₂ = refl
    st skip skip = refl
    st (p1 , p2) (p3 , p4) rewrite st p1 p3 = st p2 p4
    st (p1 , p2) (p3 ret, p4) with st p1 p3
    ... | () 
    st (p1 ret, p2) (p3 , p4) with st p1 p3
    ... | ()
    st (p1 ret, p2) (p3 ret, p4) = st p1 p3
    st (if-true x p1) (if-true x₁ p2) rewrite st p1 p2 = refl
    st (if-true x p1) (if-false x₁ p2) with exp x₁ x
    ... | ()
    st (if-false x p1) (if-true x₁ p2) with exp x x₁
    ... | ()
    st (if-false x p1) (if-false x₁ p2) rewrite st p1 p2 = refl
    st (while-true x p1 p2) (while-true x₁ p3 p4) rewrite st p1 p3 | st p2 p4 = refl
    st (while-true x p1 p2) (while-false x₁) with exp x x₁
    ... | ()
    st (while-false x) (while-true x₁ p2 p3) with exp x x₁
    ... | ()
    st (while-false x) (while-false x₁) = refl


-- Divergence 
--------------------------------------------------

_divergesOn_ : St → State → Set
prog divergesOn s = ∀ {s'} → ¬ ⟨ prog , s ⟩⟱ s'

Divergent : St → Set
Divergent prog = ∀ {s} → prog divergesOn s

private
  inf-loop : Divergent (while tt do skip)
  inf-loop (while-true tt p p₁) = inf-loop p₁
  inf-loop (while-false ())  


-- Semantic equivalence
--------------------------------------------------

_⇔_ : ∀ {a b} → Set a → Set b → Set (a L.⊔ b)
A ⇔ B = (A → B) × (B → A)

SemanticEq : St → St → Set
SemanticEq pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' ⇔ ⟨ pb , s ⟩⟱ s'

Semantic⇒ : St → St → Set
Semantic⇒ pa pb = ∀ {s s'} → ⟨ pa , s ⟩⟱ s' → ⟨ pb , s ⟩⟱ s'



-- -- Correctness of factorial programs
-- --------------------------------------------------

private

  --- Semantics in meta-langauge
  ⟦fac⟧ : ℕ → ℕ
  ⟦fac⟧ zero    = 1
  ⟦fac⟧ (suc n) = suc n * ⟦fac⟧ n


  -- 1.  Correctness of recursive definition
  fac-rec-body : St
  fac-rec-body = 
      if lte (var "n") (lit 0) then
         (ret (lit 1))
      else
         (ret (mul (var "n") ("fac" $: [ sub (var "n") (lit 1) ] )))

  fac-rec : St
  fac-rec =
    fun "fac" [ "n" ] fac-rec-body
    (ret ("fac" $: [ var "n" ]))

  fac-rec-body-ok :
    ∀ n
    → ⟨ fac-rec-body , 
      ok (("n" ,ₙ n) ∷ ("fac" , fun [ "n" ] fac-rec-body) ∷ []) ⟩⟱ 
      ret (⟦fac⟧ n)     
  fac-rec-body-ok zero = if-true (lte var lit) (ret lit)
  fac-rec-body-ok (suc n) = 
    if-false (lte var lit) 
      (ret (mul var ((sub var lit ∷ []) $: (fac-rec-body-ok n))))

  fac-rec-ok :
    ∀ n → ⟨ fac-rec , ok [ ("n" ,ₙ n) ] ⟩⟱ ret (⟦fac⟧ n)
  fac-rec-ok n = fun-ret (ret ((var ∷ []) $: (fac-rec-body-ok n)))


  -- 2. Correctness of procedural definition
  fac-loop : St
  fac-loop =
    while lt (var "i") (var "n") do (  
      "i"   := add (lit 1) (var "i") ,
      "acc" := mul (var "i") (var "acc")
    )

  fac-proc : St
  fac-proc =
    fun "fac" ( "n" ∷ []) (
      decl "i" (lit 0) (
      decl "acc" (lit 1) (
      fac-loop ,
      ret (var "acc") )))
    (ret ("fac" $: [ var "n" ]))

  fac-loop-ok :
    ∀ {s} d i 
    → ⟨ fac-loop ,
        ok (("acc",ₙ ⟦fac⟧ i)       ∷ ("i",ₙ i    ) ∷ ("n",ₙ d + i) ∷ s) ⟩⟱ 
        ok (("acc",ₙ ⟦fac⟧ (d + i)) ∷ ("i",ₙ d + i) ∷ ("n",ₙ d + i) ∷ s)

  fac-loop-ok zero i = while-false (substExp (¬A→≡false (a≮a i)) (lt var var))
  fac-loop-ok (suc d) i with fac-loop-ok d (suc i)
  ... | next rewrite +-suc d i = 
    while-true (substExp (A→≡true (a<sb+a i d)) (lt var var)) 
       ( ass (add lit var) , 
         ass (mul var var)) 
       next

  fac-proc-ok :
    ∀ n → ⟨ fac-proc , ok (("n",ₙ n) ∷ []) ⟩⟱ ret (⟦fac⟧ n)
  fac-proc-ok n with fac-loop-ok n 0
  ... | loop-ok rewrite +-comm n 0 = 
    fun-ret (ret ((var ∷ []) $: 
      decl-ret lit (
      decl-ret lit 
      (loop-ok , 
      ret var))))  
    
