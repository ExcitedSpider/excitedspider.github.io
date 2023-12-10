---
layout: post
title:  "Inductive Propositions"
categories: [Software-Foundations]
description: Apart from normal "declarative" style, propositions can also be defined *inductively*.
---

* TOC
{:toc}

## Inductive Propositions
Apart from normal "declarative" style, propositions can also be defined *inductively*. *Inductively defined propositions* is analogue to recursive functions, but more powerful as Coq has strict restrictions on functions that make them always decidable[^2]. To be more specific, functions in Coq are required to be total. On the other hand, there is no rule applied to inductive propositions, which is a fine line between decidable and undecidable.

The example given in the software foundation[^1] that illustrates this analogue is the *Collatz Conjecture*, which states that repeating two simple arithmetic operations will eventually transform every positive integer into 1[^3]. 
This example is so brilliant that I can't devise a better one to replace it. 

To be more specific, these two operations are
- If the number is even, divide it by two.
- If the number is odd, triple it and add one.

```coq
Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.
```

To examine this conjecture, we can try to define a function that perform the calculation, but only find coq rejects it:

```coq
Fail Fixpoint reaches_1_in (n : nat): nat :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).
```

Coq rejects it because there is no guarantee that this calculation would eventually halt, thus it's not a decidable problem  (It is proved to be undecidable formally[^3]). But we can express the concept as an *inductively defined property* of numbers:

```coq
Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.
```

The inductive proposition `Collatz_holds_for` is informally read as: 
"On input n, the property holds true when $n=1$, or when $f(n)$ holds." 

{:.note}
> Conventionally, a proposition with one parameter is called a *property*, and a proposition with two or more parameters is called a *relation*.

Unlike functions, propositions cannot always be calculated automatically. For a particular number, we should guild the "calculation" for Coq. 

```coq
Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done.  Qed.
```

Finally, the proposition `Collatz_holds_for` can be viewed as a subset of `nat`, which contains all provable elements. The Collatz Conjectures ask whether the size of the subset is actually as large as `nat` itself. 

```coq
Conjecture collatz : forall n, Collatz_holds_for n.
```

So far (2023), mathematicians haven't find a way to prove or disprove this Conjecture.
### Example: Permutations
A permutation of a ordered set is a rearrangement into a new order by some rules. For example, the proposition `Perm3` defines a set of permutation rules on 3-elements set. 

```coq
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.
```

Informally, we call an ordered set to be a permutation of another set if we can achieve it by:
- swap the first and the second element; or
- swap the second and the third element; or
- combine any number of permutation operations

```coq
(* Exercise: 1 star, standard, optional (perm) *)

Example exercise_perm_1 : Perm3 [1;2;3] [3;2;1].
Proof.
  apply perm3_trans with [3;1;2].
  - apply perm3_trans with [1;3;2].
    + apply perm3_swap23.
    + apply perm3_swap12.  
  - apply perm3_swap23.
Qed.

Example exercise_perm_2 : Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with [1;3;2].
  - apply perm3_swap23.
  - apply perm3_swap23.
Qed. 
```

## Inductive Properties
The property "the set of even numbers" can also be expressed in a inductive style:

```coq
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

{:.note}
> Note that the hypothesis H is written to the left side of colon instead of on the left of implication symbol $H \to P$. It is nothing but a notation.

The definition of `ev` can be thought as "primitive ***evidences*** of evenness", which is again, an analogue to "constructors" of  inductive types. In other words, if we know beforehand a number $n$ is an even number, it must be one of two things:
- $n$ is `ev_0`, that is, $n = 0$
- $n$ is `ev_SS`, that is, $n-2$ is an even number.
Thus, we can reasoning about how the n is built. It is possible to use it by *case analysis*, or *by induction*.   

### Inversion on Evidence
When the tactic `inversion` is applied on evidence, it looks at each of the constructor of an evidence, performs case analysis and generates subgoals. It tries to throws apparent self-contradictory subgoals as well.  

```coq
(* Exercise: 1 star, standard (inversion_practice) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.
```

### Induction on Evidence
The tactic `induction` is also applicable on evidence. It causes Coq to generates "basic" subgoals for "basic" constructors and induction subgoals for recursive occurrence of the property, together with an induction hypothesis with each.

```coq
(** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m EV EM.
  induction EV as [| x y IHEV].
  - (* ev_0: n = 0 *) simpl. apply EM.
  - (* ev_SS: ev (n - 2) -> ev n *) simpl. apply ev_SS. apply IHEV.
Qed.

(** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m ENM EN.
  induction EN.
  - simpl in ENM. apply ENM.
  - simpl in ENM. apply ev_SS in ENM.
    assert(H: forall n, ev (S (S n)) -> ev n ).
    {
      intros n0 H. 
      apply ev_inversion in H. destruct H.
      - discriminate H.
      - destruct H as [n' [H1 H2]]. injection H1 as H1I.
        rewrite H1I. apply H2. 
    }
    apply H, H in ENM.
    apply IHEN in ENM.
    apply ENM.
Qed.
```
## Inductive Relations
A naive example is a *total* relation, which holds for every pair of inputs:
```coq
(* Exercise: 2 stars, standard, optional (total_relation) *)
Inductive total_relation : nat -> nat -> Prop :=
  | total_n (n m: nat): total_relation n m.

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof. intros n m. apply total_n.
Qed.
```

As a more nontrivial case, the "less than or equal" relation is a good entrance to study how to reason about inductive relations.
```coq
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).
```

There are many facts we can play with `le`. For example, we are going to show that for any two number $n,m$, it's always $n<m$ or $n >= m$.
```coq
(** Exercise: le_and_lt_facts *)

Lemma n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm as [| n' IH IE].
  - apply le_n.
  - apply le_S. apply IE.
Qed.   

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  induction n.
  destruct m. 
  { right. apply le_n. }
  {
    left. unfold lt. induction m.
    - apply le_n.
    - apply le_S. apply IHm.      
  }
  {
    destruct IHn.
    - unfold lt in H. unfold lt. inversion H.
      + right. apply le_n.
      + left. apply n_le_m__Sn_le_Sm. apply H0.
    - right. apply le_S. apply H.
  }
Qed. 
```

We can also define 3-place relations as well, just the same way as binary relations. 

```coq
(** Exercise: 3 stars, standard, especially useful (R_provability) *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** If we dropped constructor [c5] from the definition of [R],
	would the set of provable propositions change? *)
Inductive R' : nat -> nat -> nat -> Prop :=
  | c1'                                     : R' 0     0     0
  | c2' m n o (H : R m     n     o        ) : R' (S m) n     (S o)
  | c3' m n o (H : R m     n     o        ) : R' m     (S n) (S o)
  | c4' m n o (H : R (S m) (S n) (S (S o))) : R' m     n     o
.

(* Proof that removing c5 does not change the relation *)
Theorem R_R'_equality: forall a b c, R a b c <-> R' a b c.
Proof.
  intros. split.
  {
    intros H. inversion H.
    - apply c1'.
    - apply c2', H0.
    - apply c3', H0.
    - apply c4', H0.
    - apply c4', c2, c3, H.     
  }
  {
    intros H. inversion H.
    - apply c1.
    - apply c2, H0.
    - apply c3, H0.
    - apply c4, H0.
  }
Qed.
```

## Case Study - Regular Expressions
A more exciting example for inductive propositions are [regular expressions](https://en.wikipedia.org/wiki/Regular_expression). We can reveal many facts about regular expressions in Coq. The full inductive definition of regular expressions in Coq is somehow too long to exist in this article. Thus, please refer to the original books of Software Foundations[^1]. Here I post my solutions to the exercises:

As a first example, these lemmas examines the definitions of regular expressions:
- The expression `EmptySet` does not match any string.
- If at lease one of expressions `re1` and `re2` matches string `s`, then `Union re1 re2` matches `s`.
- If there is a list `l` of strings, in which `re` matches every string in `l` , then `Star re` matches the concatenation of `l`. 
```
(* Exercise: 3 stars, standard (exp_match_ex1) *)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s. unfold not. destruct s.
  - intros H. inversion H.
  - intros H. inversion H.
Qed.   

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros. destruct H.
  - apply MUnionL, H.
  - apply MUnionR, H.
Qed. 

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  { simpl. apply MStar0. }
  { 
    simpl. apply MStarApp.
    - apply H. simpl. left. reflexivity.
    - apply IHss. intros. apply H. simpl. right. apply H0.
  }
Qed.
```

Write a recursive function `re_not_empty` that tests whether a regular expression matches some string. Prove that your function is correct.

```coq
(** Exercise: 4 stars, standard (re_not_empty)*)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char x => true
    | App r1 r2 => (re_not_empty r1) && (re_not_empty r2)
    | Union r1 r2 => (re_not_empty r1) || (re_not_empty r2)
    | Star r => true (* note that `Star` always matches empty string [] *)
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
	(exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re.
  split.
  { 
    (* exists -> not empty *)
    intros Hexists.
    destruct Hexists as [x H].
    induction H.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    - simpl. rewrite IHexp_match. apply orb_true_iff. left. reflexivity.
    - simpl. rewrite IHexp_match. apply orb_true_iff. right. reflexivity.
    - reflexivity.
    - reflexivity.
  }
  {
    (* not empty -> exists *)
    intros H.
    induction re.
    - discriminate H.
    - exists []. apply MEmpty.
    - exists [t]. apply MChar.
    - simpl in H. apply andb_true_iff in H. destruct H.
      apply IHre1 in H. destruct H. apply IHre2 in H0. destruct H0.
      exists (x ++ x0).
      apply MApp. apply H. apply H0.
    - simpl in H. apply orb_true_iff in H. destruct H.
      + apply IHre1 in H. destruct H.
        exists x. apply MUnionL, H.
      + apply IHre2 in H. destruct H.
        exists x. apply MUnionR, H.
    - exists []. apply MStar0.
  }
Qed.
```

## Case Study: Reflection
A *reflection* is a corresponding boolean expression to a proposition. Having a reflection implies the proposition is decidable as a boolean expression can be calculated in a deterministic process within finite steps. A naive reminder:
```coq
(n =? m) = true <-> m=n
```

There are many propositions that have reflections. As an abstraction, the "reflection principle" can be defined as:
```coq
Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.
```
The relation `reflect` takes two arguments, a proposition P and a boolean b. It states that P reflects the boolean b, that is, P holds if and only if b is true. An advantage of having such abstraction is that we can perform case analysis while at the same time generate appropriate hypothesis.

First we show a reflection relation between `=?` and `=`
```
Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.   
```

Then we can use it in case analysis. When we go into the branch that `n=?m` is true, we get the hypothesis `n=m` automatically. This is a small gain in convenience.

```coq
(** Exercise: 3 stars, standard, especially useful (eqbP_practice) *)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - unfold not. trivial.
  - simpl in *. destruct (eqbP n m) as [H0 | H0].
    + discriminate Hcount. 
    + simpl in *. intros [H | H].
      * unfold not in H0. apply H0. rewrite H. reflexivity. 
      * apply IHl' in Hcount. exfalso. apply Hcount. apply H.
Qed.   
```

## Reference

[^1]: IndPropInductively Defined Propositions. (n.d.). Retrieved from https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html
[^2]: Decidability (logic). (2023). Retrieved from https://en.wikipedia.org/wiki/Decidability_(logic)
[^3]: Collatz conjecture. (2023). Retrieved from https://en.wikipedia.org/wiki/Collatz_conjecture