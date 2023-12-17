---
layout: post
title:  "Proof Objects"
categories: [Software-Foundations]
description: The Curry-Howard Correspondence.
---

* TOC
{:toc}


## Curry-Howard Correspondence
> A proof is a program, and the formula it proves is the type for the program.

Coq is a canonical example of the isomorphism of proofs and programs, which is established by mathematicians Haskell Curry and William A. Howard[^1]. In fact, programs and proofs in Coq are the same thing.

A fundamental idea of Coq is that provability is represented by concrete *evidence*, which we can regard it as a data structure - **proof objects**.

{:.note}
>An evidence, roughly speaking, is a construction of proof. Typically, it refers to the mathematical objects which lie in the core of a constructive proof[^2].

For example, if a proposition is an implication like $A\to B$, then its proof will be an evidence *transformer* function that can be viewed as a function(program) to convert the evidence of A to the evidence of B.

```plain
function transform(evA): evB; 
```

Naturally, if evidences are data, then propositions themselves are types. In fact, the famous *Curry-Howard correspondence* proposes a deep connection between logic and computation:
- propositions ~ types
- proofs ~ data values

To be more specific, notice the definition of `ev`

```coq
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

The proposition `ev_SS` can be read as an "evidence constructor", taking 2 parameters - a number `n` and an evidence `H` which states the evenness of `n`, to return an evidence of `S(S(n))`. That is to say, the type constructor `ev_SS` can be expressed as:

$$
\forall n, ev~n \to ev~(S(S ~n))
$$

The functionality is why the grammar for inductive data types and inductive propositions are almost the same. 

## Proof Scripts
By default, we are building proofs by writing *proof scripts*, in which we use tactics and theorems to build the proofs. In fact, what are built in the proof scripts are proof objects. 

The following example shows the correspondence between proof script. The instruction `Show Proof` prints the proof objects. We can also build the proof objects *directly*.

```coq
(** Exercise: (eight_is_even) *)

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS, ev_SS, ev_SS, ev_SS, ev_0.
  Show Proof.
Qed.

Definition ev_8' : ev 8 := (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).
```

In my opinion, the difference between building proof objects through a proof script and given the definition directly is that proof scripts allow the programmer to build proof objects interactively. For a large proof object, it's extremely hard to give the construction of the proof object directly.

## Logical Connectives
The following sections examine how propositions can be translated to types in detail.
### Universal Quantifiers and Implications
A simple example is that for proposition 
```coq
Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
```

The corresponding type is 
```plain
Definition ev_plus4' : (n : nat) (H : ev n) : ev (4 + n).
```

The parameter `n` appears in the first and second parameters is called *dependent type*. It restrains the second parameter by the first parameter.
### Conjunction
To prove conjunctions like $P \land Q$, we must show both propositions P and Q holds. That is:

```coq
Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.
```

The mechanism of tactic `split` is, in fact, analyzing inductively defined type with exact one constructor[^3], as there is only one way to construct the goal. To achieve the same effect in functions, we can use the constructor directly.

```coq
(* Exercise (conj_fact) *)
Theorem conj_fact' : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
Proof.
  intros P Q R [HP _] [_ HR].
  split.
  - apply HP.
  - apply HR.
  Show Proof.
Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R:=
  fun (P Q R: Prop) (hpq: P /\ Q) (hqr: Q /\ R) =>
    match hpq, hqr with
      | conj p q, conj q' r => conj p r
    end.
```

### Disjunctive
The disjunctive term $P\lor Q$ has two ways to prove: either show that P or Q holds.

Equivalently, we can write disjunctions in inductive definitions.

```coq
Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.
```

The definition of `Inductive or` explains why tactic `destruct` can work with disjunctions, as the tactic performs case analysis by generating a subgoal for each constructor of the inductive. We can use `match` to perform case analysis in programs to achieve the same effects.

```coq
(** Exercise (or_commut') *)

Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ => 
    match HPQ with
      | or_introl P => or_intror P
      | or_intror Q => or_introl Q
    end.

Lemma or_commut: forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H.
  - apply (or_intror H).
  - apply (or_introl H).
  Show Proof.
Qed. 
```

### Existential Quantification
The definition of existential quantification $\exists$ is similar to universal quantifiers, but with exchanged parameter positions.

```coq
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.
```

Notice that we put proposition `P` in front of data type `x`, which means it is `x` who depends on `P`. It is exactly the inverse definition of universal quantifiers.

An example given:

```coq
(** Exercise (ex_ev_Sn) *)

Lemma ex_ev_Sn':  ex (fun n => ev (S n)).
Proof.
  exists 3.
  apply ev_SS, ev_SS, ev_0.
  Show Proof.
  Qed.

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3 (ev_SS 2 (ev_SS 0 ev_0)).
```

### Truth and False
Truth is given by a constructor with no parameter.

```coq
Inductive True : Prop :=
  | I : True.
```

Since it has no parameter, being given a hypothesis of `True` is not informative.

```coq
(** Exercise (p_implies_true)
    Construct a proof object for the following proposition. *)

Definition p_implies_true : forall P, P -> True :=
  (fun _ _ => I).
```

False is defined as a inductive type with no constructor, which means if we apply `destruct` on a `False`, what happens is that Coq replace current goal with **0** subgoals. The tactic `discriminate` also works on `False` because it is justified to say there is no way to construct a `False`. 

```coq
Inductive False : Prop := .
```
(Weird though, this is actually the correct grammar)

```coq
Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P contra => match contra with end.  
```
(Again, the grammar is correct since no branch to analyze)

### Equality
Coq has a set of built-in computation rules to identify what is "the same". I have no idea if we can overwrite that. But we can always make our own "equality" relation.

A way to think about equality relation is that we say two terms are the same. That is,

```coq
Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(* a naive example *)
Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.
```

As a proof system by construction, we need to show what is equal in the proof objects. For example:

```coq
(** Exercise: (eq_cons) *)

Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
fun X h1 h2 t1 t2 Hh Ht =>
  match Hh, Ht with
    | eq_refl h, eq_refl t => eq_refl (h::t)
  end. 
```

The inductive definition of quality implies Leibniz Equality[^4]:

```coq
(** Exercise (equality__leibniz_equality_term) *)

Definition equality__leibniz_equality_term : forall (X : Type) (x y: X),
    x == y -> forall P : (X -> Prop), P x -> P y :=
fun (X:Type) (x y: X) (H: x==y) =>
  fun (P:X->Prop) =>
    match H with
    | eq_refl a => fun z => z
end.
```

## Trusted Computing Base
One question arising with any proof assistant is "why should we trust it?". To be more specific, there are also bugs in Coq itself, so why do we trust the outcomes of Coq?

There is no way to allay such concerns completely. But there are reasons why we can trust  Coq more than we trust regular general purpose programming languages:
- The core of proof system of Coq is rather small compared to general purpose programming languages. As we see that even conjunctions, disjunctions, quantifiers are not built-in features of Coq.
- Coq is based on the Curry-Howard correspondence, which gives it a strong math foundation. Because propositions are just type and proofs are just terms (data structures), it is able to use ***type checkers*** to check the correctness of proofs. 

Type checkers are relatively small and straightforward programs. Therefore, the part of the code we have to believe is correct is minimal. 

There are many things a type checker can do. For example, it makes sure a `match` expression in the proof object is indeed *exhaustive*.

```coq
Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.
```

Another important thing a type checker does is that it makes sure each recursive function terminates.

```coq
Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.
```

It is worth mentioning that the correctness of Coq does not depend on the tactic machinery. As we see that, a proof script is only a way to construct the proof object. When you type `Qed`, Coq build the term for validity from scratch and runs the type checker on that term, so it has nothing to do with the correctness of implementations of tactics. 
## References
[^1]: Curry–Howard correspondence. (2023). Retrieved from [wikipedia](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
[^2]: Constructive proof. (2023). Retrieved from https://en.wikipedia.org/wiki/Constructive_proof
[^3]: Reasoning with inductive types¶. (2023). Retrieved from https://coq.inria.fr/refman/proofs/writing-proofs/reasoning-inductives.html#coq:tacn.split
[^4]: Maths - Leibniz Equality. (2023). Retrieved from https://www.euclideanspace.com/maths/discrete/types/equality/leibniz/index.htm