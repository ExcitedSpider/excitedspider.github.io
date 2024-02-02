---
layout: post
title:  "Hoare Logic Basic"
categories: [Software-Foundations]
description: Assertions, Hoare Triples and Proof Rules. 
tags: [Coq, PLT]
---

* TOC
{:toc}
The _Floyd-Hoare Logic_, or _Hoare Logic_, is a formal logic system which is able to reason about the correctness of computer programs **rigorously** and **compositionally**. It is rigorous in the sense that it bases on formal logics. It is compositional because it allows researchers to look at the syntactic constructs of a imperative program. 

There are two main ideas of Hoare Logics:
1. writing down formal specifications of programs
2. proof technique of programs which mirrors the structure of program

## Assertions

Assertions are logical claims about the state of programs. Intuitively, programmers want the programs to satisfy some constrains at a certain point.  For example, if I wrote such code

```java
File myObj = new File("filename.txt");
Scanner myReader = new Scanner(myObj);
String data = myReader.nextLine(); // <-
```

Before execution of the last line, I certainly want there are lines to read. In other words, it should be in a state that  `myReader` is valid:

```java
() -> this.myReader.hasNextLine()
```

Formally, an assertion is a property of states, which states the correctness of a program.

```coq
Definition Assertion := state → Prop.
```

## Hoare Triple
The central of Hoare Logic is the *Hoare Triple*. A triple describes how the execution of a piece of code changes the state ([program state](https://en.wikipedia.org/wiki/State_(computer_science))). The formal notation of a triple is:

$$
\{P\}~c~\{Q\}
$$

where P and Q are assertions, c is the piece of code (commands) that being executed. P is named the _precondition_ and Q the _postcondition_. This triple asserts that if the state satisfy $P$, after code $c$ was executed, the state should satisfy $Q$. 

Reasoning about the program is (partially) equivalent to see if a triple is _valid_. For example, the triple

```coq
{ X = 0 } X := X + 1 {X = 1}
```

is apparently valid. (Here I adopt the annotation of assertions from [^1])

We can formalize the validity of triples as a proposition

```coq
Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.
```

## Structured Proof Rules

A wonderful idea of Hoare Logic is that the proof mirrors the structure of the program itself. Let's look at some fundamental ones based on the language imp (which defined in [^1]). 

### Sequencing

A sequence of commands can be "torn down" by look at each command.  The rule is:

$$
{\displaystyle {\dfrac {\{P\}S\{Q\}\quad ,\quad \{Q\}T\{R\}}{\{P\}S;T\{R\}}}}
$$

which can be easily translated to Coq:

```coq
Theorem hoare_seq : ∀ P Q R c1 c2,
     {{Q}} c2 {{R}} →
     {{P}} c1 {{Q}} →
     {{P}} c1; c2 {{R}}.
```

Although it is intuitive, but one should see that it shows how Hoare Logic can **compositionally** reason a program - by the transitivity of triples - without taking the program as a whole. 
### Assignment

For imperative programs, the typical command that changes the program state is assignment. Thus, it is the most fundamental of the Hoare logic.

$$
{\dfrac {}{\{P[E/x]\}x:=E\{P\}}}
$$

where $P[E/x]$ means the assertion $P$ in which every free occurrence of x as been replaced by E.    

For example, what the precondition could be in this triple?

$$\{ ??? \}~X:= X + Y~\{X=1\}$$

If we replace $X$ with $X+Y$ in the postcondition, a valid precondition is acquired. 

$$\{ X+Y = 1 \}~X:= X + Y~\{X=1\}$$

This trick works because it exploits the definition of assignment. Besides, this trick is so mechanical that it could be implemented in Coq trivially.

The implementation of $P[E/x]$:

```coq
Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
```

This function takes a variable `X`, an expression `a` and an assertion P, returns an assertion that replaces the evaluation of `st X` to `st a`.

It is also known as "backwards reasoning" because we take postconditions and commands as inputs, outputing the preconditions. Actually it is a good way to think because the postconditions are usually the most important. But it is not to say that it's impossible to do forward reasoning - see [^2] for more examples.

To translate this rule into Coq:

```coq
Theorem hoare_asgn : ∀ Q X a,
  {{Q [X ⊢> a]}} X := a {{Q}}.

Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  exists ((X <= 10) [X |-> 2 * X]).
  apply hoare_asgn.
Qed.
```

A common error is to use this rule in a "forward" way. In other words, this is incorrect: ${\displaystyle \{P\}x:=E\{P[E/x]\}}$

We give a counterexample of it to show that it is indeed incorrect:

$${\displaystyle \{\text{True}\}~x:=a~\{X = a\}}$$

```coq
Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof.
  exists (APlus (AId X) (ANum 1)). (* X := X + 1 *)
  unfold not.
  unfold valid_hoare_triple.
  intros.
  remember (X !-> 0) as st.
  remember (X !-> 1; st) as st'.
  unfold Aexp_of_aexp in H.
  assert (aeval st' X = aeval st' <{ X + 1 }>).
  {
    apply H with st.
    - subst.
      apply E_Asgn.
      reflexivity.
    - unfold assert_of_Prop. trivial.
  }
  subst. inversion H0.
Qed.
```

### Consequence

$${\displaystyle {\dfrac {P_{1}\rightarrow P_{2}\quad ,\quad \{P_{2}\}S\{Q_{2}\}\quad ,\quad Q_{2}\rightarrow Q_{1}}{\{P_{1}\}S\{Q_{1}\}}}}$$

This rule allows strengthening the precondition or(and) weaken the postconditions.

For example, if my precondition is $\{ X > 10 \}$ , I can strengthen it to $\{X > 20\}$. For most of the time, this rule is used to adjust the assertions to what we need.

### Conditions
A conditional command `if b then s else t end` naturally has this form in logic: 

$${\displaystyle {\dfrac {\{B\wedge P\}S\{Q\}\quad ,\quad \{\neg B\wedge P\}T\{Q\}}{\{P\}{\texttt {if}}\ B\ {\texttt {then}}\ S\ {\texttt {else}}\ T\ {\texttt {end}}\{Q\}}}}$$

That is, in the `then` branch, we know $B$ is evaluated to $\text{True}$; and in the `else` branch, $B$ is evaluated to $\text{False}$.  We could use this information in reasoning. Moreover, if $B$ (or $\lnot B$) contradicts $P$, we could rule out that branch because its hypothesis contains a contradiction. 

Formalization in coq:

```coq
Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.

(* example *)
Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
  try (apply hoare_asgn); simpl; assertion_auto''.
Qed.
```

### Loops

$${\displaystyle {\dfrac {\{P\wedge B\}S\{P\}}{\{P\}{\texttt {while}}\ B\ {\texttt {do}}\ S\ {\texttt {end}}\{\neg B\wedge P\}}}}$$

This rule captures the most important behaviors of loops:
- The loop body will be executed only if $B$ is true
- The loop terminates when $B$ becomes false.
- We call $P$ a loop invariant to $S$ if $\\{P \wedge B\\}S\\{P\\}$. This means P will be true at the end of the loop body if $B$ is true in the beginning. Otherwise, (if P contradicts B), it still holds because the precondition becomes trivial.

Note that Hoare Logic only cares about loops that terminates. In other word, only partial correctness can be proven. There is a variant version of loop rule that can be formulated to prove total correctness[^2].  But as deciding if a program halts is known as undecidable, it is hard to work with total correctness, or it would require special designs of programming languages.

Formalize it in Coq

```coq
Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
```
## Summary
- Assertions are properties of program states.
- Hoare Triples are built on assertions.
- Hoare Triples can be reasoned mechanically through proof rules 

## Reference

[^1]: [PROGRAMMING LANGUAGE FOUNDATIONS](https://softwarefoundations.cis.upenn.edu/plf-current/index.html)
[^2]: [Wikipedia: Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic)
