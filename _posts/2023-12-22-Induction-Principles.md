---
layout: post
title:  "Induction Principles"
categories: [Software-Foundations]
description: the underlying mechanism of the tactic `induction`.
tags: [Coq]
---
The tactic `induction` can be applied to each `inductive` defined data type or propositions. The underlying mechanism for the correctness are the *induction principles*.

## Induction principles
Induction principles are the propositions which are depend on the inductive types. For examples, the natural number `nat` has following induction principle:

```coq
Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
```

It states that, suppose P is a property of natural numbers. To show P holds for all instances of natural numbers, it suffices to show that
- P holds for 0
- P holds for `S n` if P holds for `n`

{:.note}
>As `nat_ind`, the names of induction principles are the names of inductive type appending  `_ind` by default. Just mention, this implementation detail is not important at all.

By applying `nat_ind`, we can principally achieve the effect of the tactic `induction`, that is, the goal `P n` is partitioned to two goals: prove `P 0` and `P (S n)` by giving hypothesis `P n`.

```coq
(* Exercise (plus_one_r') *)
Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.  
```

In fact, Coq generates induction principles for every inductively defined data type, even including those that are not recursive. These generated principles follows a similar pattern:

For every constructors c1, ... , cn, Coq generates a theorem with this shape:

```plain
t_ind: forall P: t -> Prop, 
	<case for c1> ->
	<case for c2> -> ... ->
	<case for cn> -> 
	forall n:t, P n 
```

First, an example where the constructor take no arguments:

```coq
Inductive rgb : Type :=
  | red
  | green
  | blue.
  
Check rgb_ind: forall P: rgb -> Prop,
  P red ->
  P green ->
  P blue ->
  forall r: rgb, P r.
```

If any of the constructors are recursive, one or more induction hypotheses are made according to the number of recursive parameter:

```coq
(* Exercise  (booltree_ind) *)
Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop
  := P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop
  := forall b: bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop
  (* Note the order of paramters need to match how it is defined *)
  := forall (b: bool) (b1: booltree), P b1 -> 
	 forall b2: booltree, P b2 -> 
	 P (bt_branch b b1 b2). 

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.

(* Check it matches the auto-generated theorem *)
Theorem booltree_ind_type_correct : booltree_ind_type.
Proof. exact booltree_ind. Qed.
```

For case `bt_branch`, two induction hypotheses are made because the constructor  `bt_branch` takes two `booltree`s.
## Polymorphism
To deal polymorphism, Coq generates *parameterized* induction principles. i.e. The rule is rather similar to the basic case, but with a polymorphic arguments on the front. 

```coq
Inductive list (X:Type) : Type :=
	| nil : list X
	| cons : X -> list X -> list X.

(* generated by Coq *)
list_ind :
	forall (X : Type) (P : list X -> Prop),
	   P [] ->
	   (forall (x : X) (l : list X), P l -> P (x :: l)) ->
	   forall l : list X, P l
```

The whole induction principle is parameterized by `X` as well.
## More on the tactic `induction`

The tactic `induction` is a wrapper for the induction principles. Thus, it is not a built-in mechanism of Coq.  It does a lot of bookkeeping making the induction principles more easy to use:
- First, we don't need to figure out the names of induction principles.
- It "re-generalize" the variable which we perform induction on.
	- To show that, we can try to apply `induction` directly to a variable in the goal.
- It allows us to rename the induction hypotheses.

## Inductive Propositions

With all the explanation of the tactic  `induction`, it is more easy to understand why the tactic `induction` works on inductive propositions. The rule is just the similar as inductive types - Coq examines each constructor and then generate hypotheses and subgoals correspondingly. 

```coq
Inductive ev : nat -> Prop :=
	| ev_0 : ev 0
	| ev_SS : forall n : nat, ev n -> ev (S (S n)))

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.
```

Note that the second case has two hypotheses: `ev n` and `P n`. This is exactly what would happen if we use the tactic `induction`. 

## Summary
- Induction principles are the underlying mechanism of the tactic `induction`
- Induction principles work both on each inductively defined type and proposition