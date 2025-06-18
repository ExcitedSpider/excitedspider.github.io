#import "@preview/dvdtyp:1.0.1": *

#show: dvdtyp.with(
  title: "A Note on Abstract Interpreter Using Compositional Semantics",
  // subtitle: [A Note on Abstract Interpreter Using Compositional Semantics],
  author: "Chew Feng",
  // abstract: lorem(50),
)
=  Background

I always believe that scalability is the key for verification. 
I have been aware of an analysis technique called _abstract interpretation_ for a while. People say it is a technique that scales very well. 
But there are not so many holistic materials on this topic, expect a recent textbook by Rival @rival2020introduction.  
Therefore, I requested the school library to find it.
Luckily, they find it from the library of University of Queensland and get it back to me after some 3 months. 
I was surprised by how this inter-library loan works.   

This is a note of the Chapter 3 from Rival’s textbook, which focuses on building an abstract interpreter of a language with _compositional semantics_.

= Compositional Semantics

A language is equipped with a *compositional semantics* if the meaning of a complex expression is determined by the meanings of its sub-expressions.
An example of compositional semantics is the *denotational semantics*, which view the meaning of program as an mathematical function in the form of$ "program": "input" mapsto "output" $ 
In this view, programs have no side effect, thus it is compositional: suppose $g$ and $f$ are two programs and $g compose f$ is the composed program, we have :
$ forall x, g compose f (x) = g (f(x)) $

Rival uses the classical _WHILE_ language for an example to illustrate its denotational semantics. It would be too tedious to list the syntax of its language. Let’s just look at some examples: 

```c
// max(x, y)
input(x);
input(y);
if(x >= y) {
	skip;
} else {
	x := y
}

// Fibonacci Sequence
a := 0;
b := 1;
while b <= 1000000 {
  b := a + b;
  a := b - a
}
```

This language only has two types for value: natural numbers $NN$ and booleans $BB$.
While minimalist, this language has (nondeterministic) input, if-else, assignment, while commands. In addition, there are two types expressions to consider:
- Scalar Expression $dot.circle: NN -> NN -> NN$. This includes “`+`”, “`-`” in the example.
- Boolean Expression: $lt.circle: NN -> NN -> BB$. This includes "`<=`" in the example

Representing expressions in denotational semantics is fairly easy: just define mathematical functions for operators `+`, `-`, etc. 

#let intl = $bracket.l.double$
#let intr = $bracket.r.double$
#let int(content) = $ intl #content intr$

For commands, it needs some thoughts. Firstly, this is an imperative language and it works fundamentally on reading from and writing to the memory.  
To assign it with denotational semantics, we need a formalism of program state $MM$ (for memory). The straightforward one is 

$ MM : XX -> VV $

where $XX$ is a set of variables and $VV$ is a set of values, and we view a program as a function:
#let scr(it) = text(
  features: ("ss01",),
  box($cal(it)$),
)
$ intl C intr: scr(P) (MM) -> scr(P) (MM) $

where $scr(P)$ is the power set function. That is to say, a program takes a set of input states, return a set of output states. By doing so, we interpret the composition of programs by
$ intl C_1 ; C_2 intr (M) = intl C_1 intr (intl C_2 intr (M)) $ 

#problem[
  Why the input and output is a set of states, instead of a single state? This is because the language has a nondeterministic command `input`.  
  Consider this program:
  ```
  input(x)
  if(x > 10) {
    y = true;
  } else {
    y = false;
  }
  ```

  What should be the output of the semantics? Intuitively, it should be two states: $ {{x > 10, y mapsto T }, {x <=10, y mapsto F}} $

  Now you should agree that output should be a set of states, not a single state. 
  Besides, to make the semantics composable, the input should be of the same type of the output. 
]<exm1>

*Semantics for input*
Input is nondeterministic. The command `input(x)` has the semantics that assign $x$ to a symbolic value that represent all possible result. #footnote[We only assume input natural numbers] Let $n$ represents this magical value,
Hence we have:
$ intl "input"(x) intr (M) = {m[x mapsto n] | forall m in M  } $


*Semantics for branching.*
Let's design the semantics for the if-else statement. It needs to execute different branch based on if the program state $MM$ satisfy a boolean condition $B: MM -> BB$.  
Let $scr(F)_B$ be a filter function on $B$, which filters the state based on whether a state satisfies $B$: 

$ 
scr(F)_B: scr(P)(MM) -> scr(P)(MM) \
scr(F)_B(M) := {m in M | intl B intr (m) = T }
$

We now can use the filter function for semantics of branching 

$
  intl "if"(B){C_0}"else"{C_1} intr = 
  scr(F)_B(M) := {m in M | intl B intr (m) = T }
$

*Semantics For Loops*
The final block of this language is the loop command $"while"(B){C}$.
Informally, the semantics should be composed by a number of $C$s until condition $B$ turns false. 

As an aside, by viewing the program as a function $"input" mapsto "output"$, we already assume that the program halts eventually.

The textbook gives such interesting semantics for loops @rival2020introduction:

$ int("while"(B){C})(M) = scr(F)_(not B) (union.big_(i>=0)(int(C) circle.small scr(F)_B)^i) (M) $

What makes it interesting is that it does not calculate the iteration of the loops. Instead, it exploit the filter function $scr(F)$ in such a way:
- The number of iteration is unbounded. Hence, it unions all $i > 0$.
- After compose the loop command $C$, it filters out the states where the condition $B$ does not hold. Hence, for each iteration, the semantics is $int(C) circle.small scr(F)_B$.
- The loops end when the condition $B$ becomes false. The outer filter function $scr(F)_(not B)$ guards such requirement. 

Apart from the trick of exploiting the filter function, it is also interesting because it shows that it is not necessary for the semantics to be always computable: this semantics rule is valid even it assume the loop is unbounded. 

= Analysis by Abstraction

*Properties of Interest*
Now consider what we want to know about a program before it executes. 
One fundamental property of programs is the _reachability_, which ask what states can be reached in execution and what can not. 
This is a fundamental property. For example, people want to show that a program never goes to some error state, and this reduces to the reachability property.

*Programs are hard to statically simulated*
Most useful programs contain nondeterministic components. It might from user input, a random number generator, etc. Consider this program:

```c
input(x1); input(x2);
if x1 > 0 then
  if x2 > 0 then ...
```

There're $2^2$ possible paths to track. 
More generally, when there is $n$ nondeterministic variables being tested by branching commands, $2^n$ possible paths need to be tracked. 
People have an cool name for this problem: _path explosion_.

This is when abstraction comes into play. While states in the _concrete domain_ is hard to simulate, we can design an _abstract domain_ that over-approximate it. For example, one abstract domain of concrete real numbers $RR$ is the domain ${+, -, 0}$ that represent positive, negative numbers and zero.

$ {{x mapsto 1}, {x mapsto 2}, {x mapsto 3}, ...} $ 

can be described by simply 
$ {x mapsto +} $

The textbook define the formal relation of abstraction.
- $CC$ is the concrete domain, and $AA$ is the abstract domain
- $forall c in CC, a in AA, c ⊨ a $ when $a$ describes $c$. I read "⊨" as "abstract to". Not sure why they use this entailment symbol. 
- A function $gamma: AA -> CC$ is the concretization function if $gamma(a) ⊨ a$ and $gamma(a)$ is the maximum element of $CC$ satisfies a .

== Colorful wooo!!

#problem[
  Prove that $1+1=3$.
]

#theorem("Euclid")[
  infinite primes what???
]

#definition("hi")[
  i define hi as a greeting
]

#proof[
  $ "hi"="hello"="greeting" $
]


#bibliography("refs.bib")
