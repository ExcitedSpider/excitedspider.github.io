---
layout: post
title:  "Program Equivalence"
categories: [Software-Foundations]
description: Formalize equivalence relations.
tags: [Coq, PLT]
---

* TOC
{:toc}

This is a summary for the programming language theory for chapter "Program Equivalence"  [^1]. 

## Behavioral Equivalence
The concept of ***equivalence*** is crucial to understand what is a correct program. For an example, if  program $A$ is correct and $B$ is equivalent to $A$, then it is guaranteed that $B$ is correct. 

Generally, an equivalence is a relation that is *reflective*, *symmetric* and *transitive*. So there are many ways to define equivalence. I could define an equivalence relation as two programs are identical as two strings after remove whitespaces. But this definition is not so interesting because it is not helpful for us to improve current programs. Instead, a more useful definition is *behavioral equivalence*. 

Two programs are said to be *behaviorally equivalent* if they evaluate to the same result from every state.

```coq
Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').
```

(The language we are working on is called "imp", which is a simple language that has the most basic and representative features as general purpose imperative languages. see [imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)  .)

We can prove that adding a `skip` results in an equivalent program.

```coq
Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros. 
  split; intros H.
  - inversion H. subst. inversion H5. subst. assumption.
  - apply E_Seq with (st':=st').
    + assumption.
    + apply E_Skip.
Qed.  
```

This definition implies an important concerns: if the program would terminate. 

Programmers also often say that program c1 *refines* c2. It is an asymmetric variant of equivalence - c1 produces the same final states when it terminates - and perhaps c1 is better in readability or  efficiency. But it is not guaranteed that c1 terminates on some initial states if c2 does.

```coq
Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').
```

### Conditions

if the predicate is always false, it's safe remove the truth branch.

```coq
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros.
  split; intros H1.
  - inversion H1; subst.
    + unfold bequiv in H. simpl in H.
      rewrite H in H6. discriminate H6.
    + assumption.
  - apply E_IfFalse; try (assumption). 
    unfold bequiv in H. simpl in H. rewrite H. trivial.
Qed.
```

### Loops

In a loop, if a predicate is always true, the program would never terminate.

```coq
Lemma while_true_nonterm : ∀ b c st st',
  bequiv b <{true}> →
  ~( st =[ while b do c end ]=> st' ).
```

(This is not halting problem if you are thinking about that because it doesn't decide every input.)

Thus, two programs are equivalent if the are both infinite loops, regardless their body. 

```coq
Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros. 
  split; intros H0.
  - inversion H0; subst.
    + unfold bequiv in H. rewrite H in H5. discriminate.
    + apply (while_true_nonterm b c st st') in H. contradiction.
  - exfalso. 
    apply (while_true_nonterm <{true}> <{skip}> st st'); 
    try (unfold bequiv);
    try (auto).
Qed.
```

Conversely, if the predicate is always false, it's safe to optimize the program by removing the surrounding while.

```coq
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros.
  split; intros H1.
  - inversion H1; subst.
    + unfold bequiv in H. simpl in H.
      rewrite H in H6. discriminate H6.
    + assumption.
  - apply E_IfFalse; try (assumption). 
    unfold bequiv in H. simpl in H. rewrite H. trivial.
Qed.
```

### Assignments

An assignment is redundant is assign to the same value that the variable currently holds.

```coq
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
  unfold aequiv.
  intros. split; intros H0.
  - inversion H0; subst.
    assert (Hx: st' =[ X:=a ]=> ( X !-> st' X; st')).
      { apply E_Asgn. rewrite <- H. reflexivity. }
    rewrite t_update_same in Hx. assumption.
  - inversion H0; subst.
    assert (Hxa: (X !-> aeval st a; st) = (X !-> aeval st X; st)).
      { rewrite H. reflexivity. }
    rewrite Hxa. rewrite t_update_same. auto using (E_Skip).
Qed.
```

## Behavioral Equivalence is Congruence

The behavior equivalence is also a *congruence*. Informally, it is a congruence in the sense that two subprograms implies the equivalence of the larger programs. For example:

$$c_1 = c_1' \implies c2 = c2' \implies (c_1;c_2) = (c_1';c_2')$$

This fact is important in the sense that it allows us to replace a small part of a large program by an equivalent subprogram without proving those parts that didn't change.   

Formalize the idea of congruence into Coq needs some work. The most basic one is the sequence commands.

```coq
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
    intros. unfold cequiv in *. split; intros Hequiv.
    + inversion Hequiv; subst.
      rewrite H in *. rewrite H0 in *.
      apply E_Seq with (st'0); assumption.
    + inversion Hequiv; subst.
      rewrite <- H in *. rewrite <- H0 in *.
      apply E_Seq with (st'0); assumption.
Qed.
```

There are some equivalence relations that are not congruence.

Define equivalence: two programs are said to be equivalent if after applying to an empty state (that is, no variables in record), the numbers of variables are the same. It is easy to see this relation is reflective, symmetric and transitive. But the relation is not congruence. Proof:

Consider two programs: (x:=0) = (y:=1)

It is not a congruence because

1. (x:=0) = (y:=1)
2. (x:=1) = (x:=1)

but 

3. (x:=0;x:=1) != (y:=1;x:=1)

QED.

## Program Transformation

A program transformation is a function that takes one program as input and produces a modified program. Compilers are the most popular kind of transformation. [Minifiers](https://en.wikipedia.org/wiki/Minification_(programming))and [obfuscator](https://en.wikipedia.org/wiki/Obfuscation_(software)) are also useful in many areas. 

A practical application for equivalence relation is to show that ana transformation is *sound*, that is, the input and output program are equivalent. It is important to do so if some optimization are applied to the transformation. 

Soundness is formalize as a property on a transformation:

```coq
Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).
```

For instance, there is a common optimization in compilers called [constant-folding](https://en.wikipedia.org/wiki/Constant_folding). (the implementation of constant-folding can be found in the programming language foundation book, see reference [^1]).

```coq
Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - assert (bequiv b (fold_constants_bexp b)).
    { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b);
    try (apply CWhile_congruence; assumption).
    + apply while_true. assumption.
    + apply while_false. assumption.
Qed.
```


## References
[^1]: “Program Equivalence.” 2024. _Equiv: Program Equivalence_. Accessed January 25. https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html.