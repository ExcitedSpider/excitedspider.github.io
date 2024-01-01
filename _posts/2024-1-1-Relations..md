---
layout: post
title:  "Relation Properties"
categories: [Software-Foundations]
description: Abstract Interface and Data Structure
tags: [Coq, "Discrete Math"]
---

* TOC
{:toc}

## Overview

This post studies the classic concept in set theory: *relations*. It's not hard though, but this it demonstrates the how mathematical ideas can be translated into Coq. 

A relations is a set contains pairs of ordered elements. A generic relation is expressed by the symbol $R$. Formally, for some two elements $a$, $b$ we have:
$$
(a,b) \in R
$$
In Coq, the identifier `relation` is defined as a proposition parameterized by two parameters in the same set. It's more narrow than the mathematical term, but this "narrow down" make the program relatively simple and reasonable. 

```coq
Definition relation (X: Type) := X -> X -> Prop.
```
## Basic Properties
Let's talk about some common properties mathematicians like to work on relations.
### Partial Functions
A partial function is a binary relation over two sets that associates every element of the first set to at most one element of the second set [^1]. More formally: for every `x`, there is at most one `y` such that `R x y`.

>[!note]
>A partial function, or a function, can be viewed as a special case of relation. In contrast, a total function is a special case of partial function, which requires for for every `x`, there is exactly one `y` such that `R x y`. i.e.
>$$
>\text{Total Function} \subset \text{Partial Function} \subset  \text{Relation} 
>$$

Some relations are not functions. For example, a relation that works on any input (total relation).

```coq
(* Exercise (total_relation_not_partial_function) *)

Inductive total_relation : nat -> nat -> Prop :=
| total_n (n m: nat): total_relation n m.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not.
  unfold partial_function.
  intros.
  assert (0=1) as Nonsense. 
  {
    apply H with (x:=2).
    apply total_n. apply total_n. 
  }
  discriminate Nonsense.
Qed.
```

As this example shows, to prove a "not" proposition, it is common to construct a nonsense by a false hypothesis. This trick is similar to the "proof by contradiction" technique in those informal proofs in math or CS courses. 

### Reflexive Relation
A relation is reflexive if for every element $a$, $R(a,a) \in R$. 

```coq
Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.
```

For example, the relation "less than or equal to" `<=` is reflexive, simply because each number equals itself. 
### Transitive Relation
A relation is transitive if $(a,b) \in R$ and $(b,c) \in R$, we always have $(a,c) \in R$.

```coq
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
```

We can prove than the relation "less than" `<` is transitive.

```coq
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - inversion Hmo.
    + apply le_S. rewrite <- H0. apply Hnm.
    + apply le_S. apply IHo'. apply H0.
Qed.  
```

There are many ways to prove this transitive property. Say, you can also try induction on hypothesis `Hnm` or `Hmo`.   
### Symmetric Relation
A relation $R$ is symmetric if $(a,b) \in R$ then it must have $(b,a) \in R$.

```coq
Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).
```

We shows that the relation "less than or equal to" `<=` is not symmetric by the "contradiction" trick.

```coq
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intros.
  assert (1<=0). {
    apply H. apply le_S. apply le_n.
  }
  apply le_Sn_n in H0. apply H0.
Qed.
```

We can say a relation is *anti-symmetric* if $(a,b) \in R$ and $(b,a) \in R$, it must be $a=b$. A good example is also the relation `<=`.

```coq
Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** Exercise (le_antisymmetric) *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a.
  induction a.
  - intros b H0 H1. destruct b.
    + reflexivity.
    + inversion H1.
  - intros b H0 H1. destruct b.
    + inversion H0.
    + assert ((a = b) -> (S a = S b)). 
      {
        intros.
        rewrite H.
        reflexivity.
      }
      apply H.
      apply IHa.
      * apply le_S_n in H0. apply H0.
      * apply le_S_n in H1. apply H1.
Qed.
```

The reason why proof is relatively harder is maybe I need to keep another variable `b` in the goal.

### Other Properties
- A relation is an *equivalence* if it's reflexive, symmetric and transitive
- A relation is a *partial order* when it's reflexive, anti-symmetric and transitive.

## Reflexive, Transitive Closure

A reflexive, transitive closure for a relation $R$ is another relation $R^\prime$ that contains $R$ and is both reflexive and transitive[^2]. 

According to the definition, the most straightforward definition is 

```coq
Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
  | rt_step x y (H : R x y) : clos_refl_trans R x y
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z
        (Hxy : clos_refl_trans R x y)
        (Hyz : clos_refl_trans R y z) :
        clos_refl_trans R x z.
```

An equivalent definition follows. This definition generates more convenient inductions compared to what the previous one does.

```coq
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.
```

Exercises involve proof of the equivalence of two definition

```coq
Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
  R x y -> (clos_refl_trans_1n R) x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl.   Qed.

(** Exercise: (rsc_trans) *)
Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y  ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy.
  - apply Hyz.
  - apply rt1n_trans with y.
    + apply Hxy.
    + apply IHHxy in Hyz. exact Hyz.
Qed.  

(** Exercise: (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  split.
  {
    intros H. induction H.
    - apply rt1n_trans with y. apply H. apply rt1n_refl.
    - apply rt1n_refl.
    - apply rsc_trans with y. exact IHclos_refl_trans1. exact IHclos_refl_trans2.
  }
  {
    intros H. induction H.
    - apply rt_refl.
    - apply rt_trans with y.
      + apply (rt_step R x y Hxy).
      + apply IHclos_refl_trans_1n.  
  }
Qed. 
```

## Reference

[^1]: Partial function. (2023). Retrieved from https://en.wikipedia.org/wiki/Partial_function
[^2]: RelProperties of Relations. (2023). Retrieved from https://softwarefoundations.cis.upenn.edu/lf-current/Rel.html