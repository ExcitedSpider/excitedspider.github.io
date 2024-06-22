---
layout: post
title:  "Small-Step Operational Semantics"
categories: [Software-Foundations]
description: Finding the meaning of a program
tags: [Coq, PLT]
---


Even if I have walked through all the content and practices in the [textbook](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html), it still confuses me about what “Small-Step Operational Semantics” is. It is partly because the study of the chapter is segmented into pieces because I have to only use my free time to do it. It also because this chapter is way too long such that one can’t get to the important points immediately.

## Small-step Semantics

*Small-step* means the evaluation of the semantics from the program can be carried out step-by-step. Some would also describe it as “structural operational semantics” because the the method usually follows the structure of programs. It might takes multiple steps to get the final semantics of a statement. Conversely, *natural semantics* directly evaluate a statement to the final state, which can be steadily implemented in a evaluation function.

For example, given the statement

```
(1 + 3) + (2 + 4)
```

It might takes multiple steps to get the semantics:

```
(4) + (2 + 4)
(4) + (6)
10 <-- final semantics
```

There are two reasons (the textbook gives) to recommend small-step semantics instead of natural semantics.
- We includes the intermediate states that it passes through along the way. Observable execution is critical in many situation. 
- By only define one-step evaluation, we allow *undefined behaviours* in the program. 

## Implementation Comparison

Compared to natural semantics, the implementation of small-step would be more complicated – a single function can’t suffice. Fortunately we are doing this in Coq, which has a very power tool  – Inductive type. 

In the most naïve language where there are only constant (denotes by C) and addition (denotes by P), the informal semantics are: 

$$\frac{}{C~n \to n}$$

$$\frac{t_1 \to n_1,~t_2\to n_2}{P~t_1~t_2 \to n_1 + n_2}$$

The formal semantics can be encoded in Coq:

```coq
Inductive tm : Type :=
  | C : nat → tm (* Constant *)
  | P : tm → tm → tm. (* Plus *)
```

The natural semantics is a function defined in a very straightforward way

```coq
Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n ⇒ n
  | P t1 t2 ⇒ evalF t1 + evalF t2
  end.
```

This evaluation function can easily handle statement such as:
- `C 3`
- `P (C 3) (C 5)`
- `P (C 3) (P (C 2) (C 3))`

Conversely, the small step semantics involves a inductive relation describing how to take a step forward:

```coq
Inductive step : tm → tm → Prop :=
  | ST_PlusConstConst : ∀ n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_Plus1 : ∀ t1 t1' t2,
      t1 --> t1' →
      P t1 t2 --> P t1' t2
  | ST_Plus2 : ∀ n1 t2 t2',
      t2 --> t2' →
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').
```

And another inductive relation which defines a multi step evaluation as multiple consecutive single-step evaluations:

```coq
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi R y z →
                    multi R x z.
```

This example shows the difference. You can clearly see that small-step semantics is quite complicated compared to natural semantics, which is only a function. 

## Properties of Small-step Semantics

### Deterministic

Firstly, given two same programs, the semantics that we found should be identical. In other word, there should be no randomness get in the way for this tiny toy language. This property is called *deterministic*.  

**Deterministic Property**: “for each t, there is at most one t' such that t steps to t' (t --> t' is provable).”

It sounds intuitive but the proof is not so straightforward. Readers can check the textbook `Theorem step_deterministic` if interested. 
### Values

There is a slight problem. When dealing with expressions such as

```
P (P (C 1) (C 3)) (P (C 2) (C 4))
```

There are actually two directions to step forward: – either handle 1 + 3 or 2 + 4, which results in different intermediate states. This is not we typically want and sometimes causes trouble. 

```haskell
P (P (C 1) (C 3)) (P (C 2) (C 4))
P (C 4) (P (C 2) (C 4))
P (C 4) (C 6)
C 10
-- or
P (P (C 1) (C 3)) (P (C 2) (C 4))
P (P (C 1) (C 3)) (C 6)
P (C 4) (C 6)
C 10
```

This problem can be solved by defining *values*. We always want the final term to be some special forms, which we called *values*. In this language, we expect the final semantics to some constant terms.

```coq
Inductive value : tm → Prop :=
  | v_const : ∀ n, value (C n).
```

With the concepts of value, we revise the definition of steps:

$$\frac{t_1 \to t_1',}{P~t_1~t_2 \to P~t_1'~t_2}$$

$$\frac{\text{value}~t_1,~t_2\to t_2'}{P~t_1~t_2 \to P~t_1~t_2'}$$

The second one is crucial. It says we take the step of $t_2$ only when t1 is a value. This definition ensures we always evaluate the first argument (t1) until it reaches the form of value. 

The usage of values doesn’t limit to this. In fact, they are very important and critical in small-step semantics. 

### Progress and Normal Forms

In a large language, sometimes people can easily forget one or more rules, which results in a incomplete definition. One should prove its semantics to be *strong progress* to show there is nothing left. 

**Theorem Strong Progress**: If t is a term, then either t is a value or else there exists a term t' such that t-->t'.

When there are statement that doesn’t make sense, we don’t want to define every possible combination of terms. For example, if there are lists in the language, how could `1 + []` proceeds? The solution is called *typed progress*, which involves defining type systems to distinguish what statement doesn’t make sense, and only well-typed terms are progress. We don’t discuss more about types in this article.

Terms that cannot make progress are called *normal forms*. In this language, only values cannot make a further step. This is quite something that suggests our definition tend to be correct. Why? Because value is a syntactic concept – it is defined by looking at the way a term is written – while normal form is a semantic one – it is defined by looking at how the term steps. 

## Multi-Step Reduction

Recall how multi-step evaluation relation is defined:

```coq
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi R y z →
                    multi R x z.
```

This relation has a few properties
 - It is obviously _reflexive_ (from the rule `multi_refl`).
 - In the second rule, it takes a step relation $R$ to define what is multi-step evaluation of $R$. This is called *closure* of *R*. 
 - Third, it is *transitive*. i.e. If `multi t1 t2` and `multi t2 t3`, we have `multi t1 t3`

### Normal Forms in Multi-Steps

If t reduces to t' in zero or more steps and t' is a normal form, we say that "t' is a normal form of t."

```coq
Definition normal_form_of (t t' : tm) :=
  (t -->* t' ∧ step_normal_form t').
```

This definition is important because it define what is typically the end of the evaluation. 

We have seen single-step evaluation is deterministic. Following that, we also want to ensure that if t can reach a normal form, then this normal form is unique.

## Conclusion

This article explains what is small-step operational semantics and what are the properties that developers should be aware of. 