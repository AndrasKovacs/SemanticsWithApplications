
Agda formalization and proofs of various parts of Nielson and Nielson's [Semantics with Applications: A Formal Introduction](http://www.amazon.com/Semantics-With-Applications-Introduction-Professional/dp/0471929808).

The repository currently covers chapters 1, 2, 3 and 6.

The code was checked with [Agda 2.4.2.3](https://hackage.haskell.org/package/Agda) and version 0.9 of the [standard library](https://github.com/agda/agda-stdlib/releases).

--

## Short guide to directories and source files

### Basic

This directory contains material pertaining to all the mentioned book chapters. Here we use a basic version of the "while" programming language, one without any extras or extensions (e. g. the extensions that are sometimes mentioned in book, to be implemented as exercise).

The book doesn't have Agda level of rigor when it comes to variable bindings and scopes, so there's a bit of elbow room for implementation details. I used de Bruijn indices here; in short, variables are indices pointing into the program state, which is represented as a fixed-length Agda vector.

`AST.agda`: contains syntax for statements and expressions, and evaluation of expressions. Chapter 1 in the book. 

`BigStep.agda`: big step, or natural semantics. Also has a proof of determinism, a correctness proof for a factorial program and a bit of misc. stuff based on book exercises. Chapter 2.1 in the book. 

`SmallStep.agda`: axioms for structural semantics and computation sequences, plus again a proof of determinism, a proof for factorial and misc stuff. Chapter 2.2 in the book. 

`EqvSemantics.agda`: proof of equivalence of big and small step semantics. Chapter 2.3 in the book. 

#### Basic/Axiomatic

Covers chapters 6.1, 6.2 and 6.3. `Total.agda` defines total axiomatic correctness, while `Partial.agda` defines partial correctness. Both files contain proofs of soundess and completeness for the respective systems. I didn't include actual proofs about programs using the systems, because it turned out to be rather cumbersome in Agda, because the higher-order `State -> Set` representation of pre- and postconditions makes type inference rather wobbly. (The axiomatic systems seem to be more suited to manual proofs, while in Agda proofs using raw semantics are surprisingly convenient). 

In particular, the completeness proof in `Total.agda` may be of interest, since the book leaves it as an exercise for the reader. It also has some non-trivial parts in the `while` case. 

`TotalImpliesPartial.agda` proves what's in the source name. 

#### Basic/Compiler

Covers chapter 3. We use big step semantics for all the proofs in the directory (of course, the proofs also apply to small step semantics because of the equivalence of the two). 

`Code.agda` contains the syntax and semantics for the virtual machine code, the compiler functions and some correctness lemmas. 

`SplitCode.agda`: a rather verbose lemma factored out to a module of its own, so that it doesn't slow down type checking in other modules.

`CorrectTo.agda` : the first part of the proof of semantic equivalence of compiled code and original code. By "to", I mean "derivation for original code -> derivation for compiled code" here. 

`CorrectFrom.agda` : the second part of the equivalence proof, and the harder one by a fair margin. This proof was complicated by the fact that it's not actually structurally inductive, so we have to prove that we recurse on chunks of derivations that are smaller in size than the one we're proving things about. So I had to use [well-founded induction](https://github.com/agda/agda-stdlib/blob/master/src/Induction/Nat.agda), which is not the most convenient thing. 

`Machine.agda` : a simple interpreter for the virtual code. Since every reduction step of the virtual machine code is decidable, we can compute from a starting configuration as far as we like. 

`Test.agda` : some notes and example output for `Machine.agda`. 

### Extended

This is just a single file, `FunRetRec.agda`. It has similar content to that of `Basic/BigStep.agda`, but for a language with significantly extended semantics. On top of the old "while" semantics, we have:

- Variable declarations. Can be used anywhere, so also inside loops. Their scope extends to what is usual in imperative languages.
- Function declarations. They can be also used anywhere, and they can be recursive. The syntax and semantics for expressions is also extended with function calls (so evaluation of expresssions is not total anymore!). Functions may have multiple arguments. 
- Return statements. Since we use big step semantics, the nonlocal effect of returning is expressed in the program state, so we have an `ok` state for normal control flow, and a `ret` state for returning values. Returning works as usual. All function calls in expressions must return a value. 
- String names for variable bindings. We use them instead of de Bruijn indices. This means that we also have variable shadowing, which works as usual. We bake the rules for well-scopedness into the dynamic semantics (although it would be ultimately better to factor all static-ey properties out into a checked AST and a separate type checker pass). 

There's also a proof of determinism here, and two factorial proofs: one for the corretness of a procedural implementation with loops, and another for a recursive implementation. 
