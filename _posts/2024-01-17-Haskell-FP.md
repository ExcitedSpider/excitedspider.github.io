---
layout: post
title:  "FP in Haskell - Practical Concerns"
categories: [Software-Foundations]
description: Partial Functions, Folds and as-pattern
tags: [Haskell, "Functional Programming"]
---


Shout out to [Real World Haskell](https://book.realworldhaskell.org/).
## Partial and Total functions
Following mathematics jargons, functions that works on all possible inputs are *total functions*. Correspondingly, functions that are not total are *partial* functions.

For example, function `head` is partial-defined, because it refuses to work on empty array.

```
ghci> head []
*** Exception: Prelude.head: empty list
```

Haskell makes no difference treating partial and total functions. For example, it's easy to reproduce function `head`. Haskell happily accept the definition in the beginning, but only cries on invalid input when running.

```
ghci> let myHead (x:xs) = x
ghci> myHead "hello"
'h'
ghci> myHead []
*** Exception: <interactive>:7:5-21: Non-exhaustive patterns in function myHead
```

The `Non-exhaustive patterns` error is a common mistakes programmers would do. 

Some functional programing languages do require functions to be total.  For example, Coq guarantees that functions are total and decidable. So why Haskell doesn't force it? My explanation is that it takes more efforts to make a total function, and verify an alleged total function is indeed total is not trivial. So as a general purpose programming language, it is understandable for Haskell to choose this relatively "unsafe" approach. 

It requires some efforts to find out if the functions you are using are total and it's arguably some controversy that prelude includes partial functions. 

Some programmers would like to add `unsafe` prefix to partial functions they make. A more functional approach is using `Maybe`:

```haskell
safeHead::[a] -> Maybe a
safeHead (x:xs) = Just x
safeHead _ = Nothing
```

Thanks to pattern matching, adding a "otherwise" pattern is so easy that wrap a partial function to a total function with `Maybe` is straightforward.

## Folding Things
Folds are the most useful and common functions in Haskell. But it takes some time to think about which variant of folds do you want.

Usually the choice is between `foldr` and `foldl'`.

`foldr` should be the most common one to use. Think it not "folding from the right", but "folding with right associativity". Following example shows the idea:

```haskell
foldr (+) 0 (1:2:3:[])
--          == 1 +           foldr (+) 0 (2:3:[])
--          == 1 + (2 +      foldr (+) 0 (3:[])
--          == 1 + (2 + (3 + foldr (+) 0 []))
--          == 1 + (2 + (3 + 0))
```

What benefits can right associativity brings? 
1. Build a new list with the same order 
	```haskell
	ghci> mapMult = foldr step [] where step x acc = (x*2):acc
	ghci> mapMult [1,2,3,4,5]
	[2,4,6,8,10]
	```
2. Handle infinite list
	```haskell
	ghci> take 3 (mapMult [1,2..])
	[2,4,6]
	```

In fact, there is another interpretation of `foldr`: It acts as a [transducer](https://en.wikipedia.org/wiki/Finite-state_transducer) - It transforms or filter the input in the same order.

On the other hand, `foldl'` is more efficient in some ways. But lets talk about why `foldl` is not a good choice for most situations. 

> Due to `foldl`'s thunking behavior, it is wise to avoid this function in real programs, even if it doesn't fail outright. Instead, import `Data.List` and use `foldl'`

In Haskell, expressions are evaluated lazily. `foldl` creates huge thunk.  Instead, `foldl'` is a good choice because it evaluate strictly at every step. Although `foldr` also  evaluated lazily, but it is more efficient with the construction of thunks. And if the operator or function it takes the second argument lazily, `foldr` can still be efficient. For example, the operator `:`

```
  foldr (:) [] [1, 2, 3, 4]
-- = 1 : ⟨foldr (:) [] [2, 3, 4]⟩
```

In conclusion, if we want to choose a "transducer" which produce the result in the same order, consider `foldr`. If we want to "produce an answer from a list", then use `foldl'`. Never do `foldl`. 

## As-Pattern

 The keyword `@` is called the "as pattern"
 
```haskell
suffixes xs@(_:xs') = xs: suffixes xs'
suffixes _ = []

ghci> suffixes "hello"
["hello","ello","llo","lo","o"]
```

Of course we can use conventional pattern match to achieve the same result:

```haskell
noAsPattern :: [a] -> [[a]]
noAsPattern (x:xs) = (x:xs) : noAsPattern xs
noAsPattern _ = []                 
```

But compared to as-pattern, we actually did one redundant destruction, which causes extra space allocation. It may be cheap, but it isn't free. So use the as-pattern wisely.
## References

Foldr Foldl Foldl’. (n.d.). Retrieved from [wiki.haskell.org](https://wiki.haskell.org/Foldr_Foldl_Foldl')
Fixing foldl. (n.d.). Retrieved from https://www.well-typed.com/blog/90/
Real World Haskellby Bryan O’Sullivan, Don Stewart, and John Goerzen. (n.d.). Retrieved from https://book.realworldhaskell.org/