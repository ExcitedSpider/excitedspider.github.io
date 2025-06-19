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
  intl "if"(B){C_0}"else"{C_1} intr (M) = 
  int(C_0) (scr(F)_B (M)) union int(C_1) (scr(F)_(not B)(M))
$

This definition is accurate by taking the union of all states produced two possible branches. 
However, it is hard for analyzer to simulate : If there are $n$ states in $M$, the branching command can create $2n$ states.  

*Semantics For Loops*
The final block of this language is the loop command $"while"(B){C}$.
Informally, the semantics should be composed by a number of $C$s until condition $B$ turns false. 

As an aside, by viewing the program as a function $"input" mapsto "output"$, we already assume that the program halts eventually.

The textbook gives such interesting semantics for loops @rival2020introduction:

$ int("while"(B){C})(M) = scr(F)_(not B) (union.big_(i>=0)(int(C) circle.small scr(F)_B)^i) (M) $

What makes it interesting is that it does not calculate the iteration of the loops. Instead, it exploit the filter function $scr(F)$ in such a way that allows unbounded loops:
- The number of iteration is unbounded. Hence, it unions all $i > 0$.
- After compose the loop command $C$, it filters out the states where the condition $B$ does not hold. Hence, for each iteration, the semantics is $int(C) circle.small scr(F)_B$.
- The loops end when the condition $B$ becomes false. The outer filter function $scr(F)_(not B)$ guards such requirement. 

Apart from the trick of exploiting the filter function, it is also interesting because it shows that it is not necessary for the semantics to be computable: this semantics rule is valid even it assume the loop is unbounded. 

= Analysis by Abstraction

== An Abstract Interpreter

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

*Abstraction*
To deal with path explosion, abstraction comes into play. While states in the _concrete domain_ is hard to simulate, we can design an _abstract domain_ that over-approximate it. 
One abstract domain of concrete real numbers $RR$ is the domain ${>=0, <=0, 0}$ that represent the sign of an variable. 

For example,
$ {{x mapsto 1}, {x mapsto 2}, {x mapsto 3}, ...} $ 

can be simply abstracted by
$ {x mapsto [>= 0]} $

#let bottom = $tack.t$

In addition, we usually require the abstract domain to be a lattice. For the abstract sign domain, we add $top$ for all signs and $bottom$ for no result. This allows us to use the join $union.sq$ and meet $inter.sq$ operator to simplify the analysis.
We have this lattice:

#figure(
image("./lattice.jpg", height: 150pt),
caption: [The lattice of abstract sign domain]
)<lattice-sign-dom>

#let below = $subset.eq.sq$

The textbook define the formal relation of abstraction.
- $CC$ is the concrete domain, and $AA$ is the abstract domain. 
- It is required that there is an order relation $subset.eq$ defined on $CC$, and an order relation $below$ defined on $AA$.
- $forall c in CC, a in AA, c ⊨ a $ when $a$ describes $c$. #footnote[I read "⊨" as "abstract to". Not sure why they use this entailment symbol. ]
- A function $gamma: AA -> CC$ is the concretization function if $gamma(a) ⊨ a$ and $gamma(a)$ is the maximum element in $CC$ satisfies $a$.

Finally, we call define abstraction:

#definition("Abstraction")[
Domain $AA$ is an abstraction of $CC$ if
- $forall c in CC, forall (a_0, a_1 in AA), c ⊨ a_0 -> a_0 below a_1 -> c ⊨ a_1 $ 
- $forall (c_0, c_1 in CC), forall a in AA, c_0 subset.eq c_1 -> c_1 ⊨ a -> c_0 ⊨ a$
]

This definition essentially requires $⊨$ to be compatible with both order relations. Consider the abstract domain of signs @lattice-sign-dom and concrete domains of real numbers. An example of the first assertion is #footnote[
  Here, ${1,2,3}$ means the set of program states ${{x mapsto 1}, {x mapsto 2}, {x mapsto 3} }$. 
]
$ {0} ⊨ {[= 0]} and {[=0]} below {[>=0]} -> {0} ⊨ {[>=0]} $ 
And similarly, an example of the second assertion:
$ {1, 2} subset.eq {1, 2, 3} and {1, 2, 3} ⊨ {[>=0]} -> {1, 2} ⊨ {[>=0]} $

#let inta(content) = $int(content)_sharp$

Hence, we have this lattice:
- 

Having the abstraction, we can simulate the program behaviors on the abstract domain, instead of on the concrete domain.
The process is like *executing the program on the abstract domain*.  
Like $int(C)$, We use $inta(C)$ for interpreting program the $C$ on the abstract domain.  


*Abstract Semantics for Branching*
Consider following program that computes the absolute value of x, we can use the abstract sign domain (@lattice-sign-dom) to simulate it:

```
input(x);
if(x > 0) {y = x} else {y = -x}
```

Before branching, the state is 

$ { x |-> top } $

For the branch where $x > 0$, we have
$ {x |-> [>=0],  y |-> [>=0] } $ 

similarly, for the branch where $x <= 0$, we have
$ {x |-> [<=0],  y |-> [>=0] } $ 

To join these two states by $union.sq$, we have 

$ {x |-> top, y |-> [>=0]} $

Thus, we prove that this program always produce a non-negative `y`.

Recall that the concrete semantics of branching: for $n$ input states, there will be $2 n$ states be produced. 
However when abstractly analysed, we use the join operator on the lattice to avoid the increase of states, and it makes analysis more scalable, at the cost of losing precision (we give up all information about $x$).


*Abstract Semantics for Loops*
Another important trick about abstract interpretation is the handling of loops. 
Recall that the concrete semantics treat loops as unbounded iteration. 
While accurate, it is not a computable procedure. For analysis, we need to find a way out of simulating a loop by finite steps. 

One key observation is that, if the loop _converges_, we can stop the iteration. 
Convergence of loops means that for some natural number $k$, the state at $k+1$ iteration is the same as $k$.
This fact is fairly intuitive and we omit further proof. 

#let widening = $triangle.stroked.small.b$

So, we want analysis of a loop to converge rapidly. The technique for convergence is called _widening_.

#definition("Widening")[
An operator $widening: AA -> AA -> AA$ is called widening if
1. $forall (a_0, a_1 in AA), gamma (a_0) union gamma (a_1) subset.eq gamma(a_0 widening a_1) $
2. This sequence of $a'_n$ is ultimate stationary:
$ a'_0 = a_0 \ a'_(n+1) = a'_n widening a_n $
]

Consider analysing the command $inta("while"(B){C})$, we can apply widening of the every $i$ and $i+1$ state.  
The first obligation of widening ensures that it indeed "widens" the concrete elements, not shrinking, otherwise the analysis will be unsound. 
The second one is more important: it ensures that after applying finite widening, the loops will be converged.  

The textbook takes an abstract domain of intervals as an example. The domain describes the concrete domain by the interval of variables. Consider ${x mapsto [n, p]}$: (suppose $p - n > 1$)
$ 
  {x mapsto n + 0} ⊨  {x mapsto [n, p]} \
  {x mapsto n + 1} ⊨  {x mapsto [n, p]} \
  ... \
  {x mapsto p} ⊨  {x mapsto [n, p]} \
$
A straightforward widening of two intervals is:
$ [n, p] widening [n, q] = cases(
  [n, p] &"if" p >= q,
  [n, +infinity) &"if" p < q
) $
That is to say, if the iteration starts in $[n, p]$ and ends in $[n, q]$, if the iteration increases the bound, we simply set the bound to infinite. 
For example, 

```
x := 0;
while(x < 50) {
  x := x + 1;
}
```

We mark the abstract state of nth iteration as $M^sharp_n$:
$
  &M^sharp_0 = {x |-> [0, 0]} \
  &M^sharp_1 = {x |-> [0, +infinity)}\
 & M^sharp_2 = {x |-> [0, +infinity)}
$

The analysis converges on the second iteration. Again, this will lose precision, but we have a fairly scalable analysis on loops. 

== Soundness of Analysis

The most fundamental property of an analysis is that it should be sound. 
For reachability, soundness means that all states that are reachable in execution will be captured by the analysis. 
Hence, a general soundness property of abstract interpretation is: 

#pagebreak()

#theorem[
  For all commands $C$ and all abstract states $M^sharp$, the computation of 
  $inta(C)(M^sharp)$ is a sound analysis if
  $ int(C)(gamma(M^sharp)) subset.eq gamma(inta(C)(M^sharp)) $
]

This theorem says that the states of concrete execution is a subset of abstract interpretation.
Apparently this theorem is true since it basically reiterate the definition of soundness on reachability problem.  

The textbook uses an illustration (@ai_vis) to express this visually.

#figure(
  image("./AbstractInterpreter.jpg", width: 50%),
  caption: [
    Sound Analysis by Abstraction
  ]
)<ai_vis>

On the bottom, it shows the concrete execution of program $P$ on input state $m$ gets $m'$.
On the top, the figure says the precondition (as an abstract state $a_"pre"$) is transformed to the the postcondition by abstractly interpreting program $P$.
The concretization function $gamma$ acts as the connection between two procedure: the concrete states is always described by the abstract states.   
Hence, the analysis is sound. 

= Summary

Let's summary what has been learned.  
The design of an abstract interpreter always follows this scheme:
1. Find a concrete semantics for the language.
2. Select an abstraction domain $AA$ of $CC$. 
3. Define the abstract semantics based on $AA$ and prove it is sound. 

When the analysis is not precise enough, one needs to look at the three steps. 

Abstract interpretation uses two important trick to improve scalability. 
1. Use the join operator $union.sq$ to replace the concrete union $union$. This prevent the branching command from creating exponential paths.
2. Use the widening operator $widening$ for rapid converge of loops. This avoid the unbounded loops. 

Now we have an (somehow over-simplified) theoretical abstract interpreter. Congratulations!


#bibliography("refs.bib")
