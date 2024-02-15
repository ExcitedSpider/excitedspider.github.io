---
layout: post
title:  "Hoare Logic - Decorated Program"
categories: [Software-Foundations]
description: Decoration and Automated Verification
tags: [Coq, PLT]
---

* TOC
{:toc}

{% raw %}

## Decorated Programs
The aesthetics of Hoare Logic is that it follows the structure of the program itself, which enables a powerful way to reason about a program -- by decoration.

This naive program which subtracts a number is from the PLT series[^1]. 
```plain
{{ True }} ->> // 1
{{ m = m }}
  X := m
		 {{ X = m }} ->>
		 {{ X = m /\ p = p }};
  Z := p;
		 {{ X = m /\ Z = p }} ->>
		 {{ Z - X = p - m }}
  while X ≠ 0 do
		 {{ Z - X = p - m /\ X ≠ 0 }} ->>
		 {{ (Z - 1) - (X - 1) = p - m }}
	Z := Z - 1
		 {{ Z - (X - 1) = p - m }};
	X := X - 1
		 {{ Z - X = p - m }} // 2
  end
{{ Z - X = p - m /\ ¬(X ≠ 0) }} ->>
{{ Z = p - m }}
```

In this example, we showed that the result of the program is indeed `p - m` by a *decorated proof*. Each line accompanies an assertion which states the condition that the program state meets. The mark 1 "narrows down" the assertion, which is discussed in the previous article[^2]. To remind it, we can use a weaker assertion to replace a stronger one to meet the requirement of the proof goal. The *loop invariant* (mark 2) states the condition that the loop satisfies. For assignments, conditions and most other commands that do not involve loops, finding the assertions is fairly easy by following the rules of Hoare Logic. We could see finding loop invariant is the creative part of this art.  

One could prove a decorated proof is indeed logically correct by an almost automated process - a "prover" (proof assistant) could look at each assertion and line of programs to decide if the deduction is correct. The reason why it could be automated is that the rules of Hoare logic are mechanical enough, as discussed in the previous post[^2].
### Simplified Decorated Programs
The straightforward way to formalize a decorated program is to present two assertions to each one command. Just like the classic Hoare logic statement:
$$
{\displaystyle \{P\}C\{Q\}}
$$
But it turns out to be too verbose that even reading it makes people frustrated.  A decorated program which contains two `skip` would look like this:

```
{{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}
```

An obvious observation is that for two sequential commands, the postcondition of the former one is the precondition of the later one. So we could agree that it's sound to remove one of it.

For `skip` command, apparently, the assertion should not change after the execution. So we don't need to provide the precondition. 
> [!NOTE] Discussion
> Why not omit the postconditions instead? Because the preconditions are always provided either from the start of the program or from the previous command.

Similarly, we could only provide postconditions of assignments, as the preconditions could be derived easily.  

Loops `while b do d` can be simplified by omitting the assertion inside the commands because they can be derived from the preconditions and the postconditions.

```
while b do {{ P }} d end {{ Q }}
```

At last, we arrived to the simplified version of decorated programs, which can be implemented in Coq with some notation magic. The full implementation could be found on[^1]. 
## Automated Verification
A decorated program could be translated to a sequence of verification conditions. By reading each line of the program and the related condition, a proof assistant is able to decide whether the condition could be satisfied. 

Let's look at the standard Hoare triple:
$$
{\displaystyle \{P\}C\{Q\}}
$$
The condition is whether the Hoare triple could be proved *valid*. The command $C$ might be composed by a sequence of commands, and they can be verified mechanically.  Formally, a proof assistant would walk recursively into the command $C$ and generated a big conjunction that checks
- *Local consistency* of each command and
- To "bridge the gap" try to narrow down the assertion found in the program and the assertion imposed by the context. This post adopts the notation  `->>` to notate this "narrowing down" from PLT series[^1]. 
	```
	"P->>Q" <-> forall (st: State), P st -> Q st
	```

A decorated command is local consistent with a precondition `P` if
- it is a skip `skip;{Q}` and  `P ->> Q`.
- it is an assignment `X:=a {Q}` and `P ->> Q[X|->a]` 
- it is a condition
	```
	if b then {{P1}} d1 else {{P2}} d2 end {{Q}}
	```
	- `P /\ b ->> P1`
	- `P /\ ~b ->> P2`
	- `post P1 ->> Q`
	- `post P2 ->> Q`
	where `post` is to get the postcondition of a decorated program
- it is a loop
	```
	while b do {{Q}} d end {{R}}
	```
	- `P /\ b ->> Q`
	- `P /\ ~b ->> R`
	- `post d /\ b ->> Q`
	- `post d /\ ~b ->> R`
- if all explicit usages of `->>` are valid

Following these rules, an automated proof program could be developed. 
## Finding loop invariants
Once the outermost precondition and postcondition are chosen, the only left creative part of this "decorated" art is finding the loop invariants. You can't choose an invariant that is too weak (such as `st -> True`), because you'd need it to bridge the following conditions. Similarly, you can't choose an invariant that is too strong, because it would be extremely hard or impossible to prove. It is indeed an art of finding the most appropriate loop invariants. 

There is no silver bullet to solve the problem, but a few tips might help:
- Try to use the strongest condition as the invariant first (the postcondition of the loop), and see what made it fails. Then adjust the invariants to a more "realistic one" 
- Think about what the loop does and, how, by the end of the loop, the assertion `Q /\ b` is useful for proving the postcondition.
- What variables are used in the loop and how to propagate these variables into the information that the invariant carries.

## Summary
- Decorated Programs could be viewed as proofs of programs.
- Simplified Decorated Programs are equivalent to a fully decorated one, and it could help to avoid verbose, and thus, easier to read.
- The verification of a decorated program could be made automated.
- Finding loop invariants is relatively hard in this art.

## Referrecne

[^1]: https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html
[^2]: https://excitedspider.github.io/software-foundations/2024/02/02/Hoare-Logic-Basic.html

{% endraw %}