---
layout: post
title:  "Simply Typed Lambda-Calculus"
categories: [Software-Foundations]
description: A small yet powerful language
tags: [Coq, PLT]
---

This article is a study note of [Programming Language Foundation](https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html)

## Overview

The simply typed lambda calculus (STLC) is a wonderful study target which represents many intriguing language features among modern programming language.

Lambda calculus (also written as λ-calculus) is a formal system in mathematical logic for expressing computation based on function abstraction and application using variable binding and substitution (From Wikipedia). 

Consider a lambda-calculus system that only contains Boolean values, which can be expressed by following BNF notation:

```
t ::= x                      (variable)
 | \x:T,t                    (abstraction)
 | t t                       (application)
 | true                      (constant true)
 | false                     (constant false)
 | if t then t else t        (conditional)
```

Examples:

```c
\x: Bool, x // identity function
(\x: Bool, x) true // apply the identity function to value true
\x:Bool, if x then false else true // function 'not'
\f:Bool→Bool, f (f true) // a higher order function
```

Although it only contains Boolean values, it processes the computation ability that equivalent any modern programming languages. It even supports higher order function that some “modern” languages don’t support well, like C and C++.  

Note that there are variables involved in the definition. A *complete* program is a program that never refer to any undefined variables. In most time, we want the program to be complete and we can simply fail there are free variables (which doesn’t bind to any terms and types).  
## Operational Semantics

### Values

To decide what are the *values* of STLC, a little discussion is needed on the case of abstraction. An abstraction (similar to a “function” in imperative programming language) is of such form

```
\x:T, t
```

There are two choices:
1. An abstraction is always a value
2. An abstraction is a value if `t` is a value

I would say I prefer option 1, and that is the choice in the textbook, because it makes things a lot easier. But option 2 is also the choice for some language, for some reasons like compile-time optimization.

### Substitution

The heart of lambda calculus is substitution. For example, we reduce

```
 (\x:Bool, if x then true else x) false
```

to 

```
if false then true else false
```

The application works by substitute `\x` into the bind value `false`. We mark the substitution as `[x:=s]t`, which literally says “substitute all occurrences of `x` into `s` in the term `t`”.

More example:
- `[x:=true] (if x then x else y)` yields `if true then true else y`
- `[x:=true](\y:Bool,x)` yields `\y:Bool,true`

Substitution is a deterministic and easy problem (i.e. not a NP-hard one). So the textbook simply encoded substitution into a fixpoint function `subst`. It’s very interesting to think how a powerful computation model is just such a small substitution machine.

Exercise: 3 stars, standard (substi_correct)
This Exercise asks us to define substitution as a inductive relation `substi` , and prove the relation is equivalent to the fixpoint version.  

```coq
Inductive substi (s : tm) (x : string) : tm -> tm -> Prop

Theorem substi_correct : forall s x t t',
  <{ [x:=s]t }> = t' <-> substi s x t t'.
```

- For direction `->`, it can be proved by induction on term `t`
- For direction `<-`, it can be proved by induction on relation `substi`  

### Reduction

Based on substitution, we can define how an expression is *reduced* to value. The core of reduction is the application rule, which says 

```
(\x:T,t) v --> [x:=v] t
```

To make the process of reduction to be deterministic, we made a design: 
**Apply reduction of application expression only if both the left-hand side (the abstraction) and the right-hand side (the argument) is a value.**

## Typing

The STLC has a powerful feature – typing, which becomes more and more important in programming language design. For some reasons, computer scientists write typing relation as following form:

```
|-- t \in T
```

which says that “term t has type T”. 

An obvious problem is typing abstractions. Consider such abstraction:

```
\x:T1, t2
```

which has type `T1 -> T2`. If we want to typecheck it, we need to make sure term `t2` has type `T2` **under the context that `x` has type `T1`.**

Context can be represented as a single global information, which adds to the typing relation. A map (partial-map) is capable of representing such information, which we name it *Gamma*. The new typing judgment is written `Gamma |-- t \in T` and informally read as "term t has type T, given the types of free variables in t as specified by Gamma". 

Examples:

```coq
Example typing_example_1 :
  empty |-- \x:Bool, x \in (Bool → Bool).
```

Finally, we present the typing rule of abstraction:

$$
\frac{x \mapsto T2 ; \Gamma \vdash t1 \in T1}{
\Gamma \vdash \backslash x:T2,t1 \in T2\to T1
}
$$
Other rules can be found in the textbook as well.

Talking about variables, a term is *closed* if all variables in it are well typed (contain no free variables).

## Properties of STLC

We discuss what makes the language to be “well and sound”. 

### Canonical Form

We can establish the relation between well-typed values (canonical form)  and their type. For example, if a value has type `Bool`, it must be a `false` or `true`. 
### Progress

The progress theorem tells us that closed, well-typed terms are not stuck: either a well-typed term is a value, or it can take a reduction step.

```coq
Theorem progress : ∀ t T,
  empty |-- t \in T →
  value t \/ ∃ t', t --> t'.
```

Exercise: 3 stars, advanced (progress_from_term_ind). 

It asks us to prove theorem `progess` by induction on terms. The proof is a bit long but not complicated. Just follow the reduction rules to see if it can make a step, or it is a value, or there is a contradiction in hypothesis. 

### Preservation

The preservation theorem says reduction doesn’t change the type of a term (so it *preserves* the type). This property shows our typing is indeed sound and well-fitted into the operational semantics. 

To establish the preservation property on STLC, we take a few steps:
1. The Weakening Lemma, which says if `t` has type `T` in some context `Gamma`and  `Gamma` is included in a bigger context `Gamma'`, t also has type `T` in `Gamma'`.
	To prove this, one need to consider what “a context is included in other context” means. But it’s fairly straightforward.
2. The Substitution Lemma, which says substitution preserves the type. 
3. The main theorem. With the help of substitution lemma, it can be proved with ease.

Exercise: 3 stars, advanced (substitution_preserves_typing_from_typing_ind)
It asks us to prove the substitution lemma, which lies at the heart of this proof chain. A few tips:
- Read carefully about the informal proof provided by the author. 
- When encounter `(x =? y)%string` (string equality), use `destruct eqb_spec` to perform case analysis.
- When the goal is the form `Gamma |-- t \in T`, you can use the weakening lemma to transform it to `empty |-- t \in t`.

Exercise: 2 stars, standard, especially useful (subject_expansion_stlc)
Show that the reverse to preservation theorem does not hold. That is, if `t --> t'` and `t' \in T`, we can not make sure `t \in T`.
I exploit the fact that reduction doesn’t type check.
```
(* t *) exists <{ (\x: Bool -> Bool, x) true }>.
(* t'*) exists <{ true }>.
(* T *) exists <{ Bool }>.
```
It’s a little bit cheating, I admit. But I can’t find a better one. 
### Type Soundness

Put progress and preservation together, we can show that a well-typed term can _never_ reach a stuck state.

Exercise: 2 stars, standard, optional (type_soundness)
Type soundness can be proved by induction on Hmulti (`t -->* t'`).

### Uniqueness of Types

Another nice property of the STLC is that types are unique: a given term (in a given context) has at most one type.

Exercise: 3 stars, standard (unique_types)
This exercise can be solved by induction on term `e`. The whole proof heavily use inversion to do case analysis. 

## Extension to STLC

One might argue that the current STLC is still too simple and cannot match a real modern programming language. Well, there are a lot of extensions to STLC in the textbook to show the possibility of the language.

- Numbers. 
- Let bindings, which adds the let expression like those in Haskell.
- Pairs, which are popular in many languages. For example, I can have a pair of `(1, false)` of type `(Nat, Bool)` 
- Unit. A unit type is a type that only has one value. It can be quite helpful to express things like `null`, `nullptr`
- Sums. A sum is like the `Either` monads In Haskell. 
- Lists. 
- Recursion (Recursive Abstraction)
- Records. Like dictionary in python.

The exercises in this chapter is to formalize these features, including the substitution, reduction and typing. I would say it is quite straightforward to follow the informal definition given by the author, and satisfying to see how it works.
