---
layout: post
title:  Language Models and N-Grams
categories: [NLP]
description: What is a language models (LMs), and the very basic example of LMs -- the n-grams
---

This article concerns two questions
- what is a language models (LMs), and 
- the very basic example of LMs: the n-grams

## Language Models
People talk a lot about Language Models, but what are them exactly? Perhaps surprisingly, models that assign **probabilities** to sequences of words are called language models or LMs. To illustrate the idea, consider a (piece of) sentence "its water is so transparent that". A LM should be able to give the possibility of word "the" coming after the sentence. In other words, a LM could decide: 

$$P(\text{the}|\text{its water is so transparent that})$$

For me, it is more easy to understand that

> LM = "input a sequence of words, output the distribution of probability of the next word. "

Probabilities are useful. For example, In *speech recognition*, probabilities can help identity which word is the speaker actually saying giving the context. In *error correction*, a LM could suggest a grammatical or spelling error if it saw an extremely small probabilities. It is also useful to use the language models in a *generative* way, in a process which mathematicians called it ***sampling***. 

### Sampling 
Sampling from a language model can output a "sample" sentence. The simplest version could be just repeatedly run the LM, with each word drawn from distribution.

## N-Grams

### General Idea
N-grams are a good exemplar for LMs, and they are popular in many basic NLP tasks as well. the word "n-gram" means using the latest n words to approximates the probability. For example, a bi-gram model assumes that

$$P(\text{the}|\text{its water is so transparent that}) \approx P(\text{the}|\text{that})$$

It may sounds like the hypothesis is silly in the first place, but it surprisingly works in many applications. The assumption that the probability of a word depends on the previous words is called a **Markov assumption**.

What's the benefit to adopt the Markov assumption? The most obvious advantage is that the implementation is much easier. Take bi-grams for example, the model can just learn the probability by counting the appearance of each word pairs in the training set showing in Eq. (1). In a fancier term, it is the maximum likelihood estimation (MLE).

$$P(w_n | w_{n-1}) = \frac{C(w_{n-1}w_n)}{\sum C(w_{n-1}w)} \tag 1$$

Accordingly, a generalized n-gram model give the probability of next word according to Eq. (2). 

	$$
	P(w_n | w_{1:n-1}) \approx P(w_n | w_{n-1}) \tag 2
	$$

It's not hard to see that for a n-gram model, the probability of a complete sentence is:

$$P(w_{1:n})\approx \prod_{k=1}^n P(w_k|w_{k-1}) \tag 3$$

Why n-grams work? Because we believe the **relative frequency** has something to do with the semantic meaning of natural language. To be more specific, n-gram models could capture **syntactic facts**: What comes after "eat" is usually a noun or an adjective. And it can even cultural information - if people like Chinese food more than Australian food, the model could capture <code>P(Chinese | eat) > P(Australian | eat)</code> .

Generally speaking, LM captures some of the characteristics of the corpus. A language model trained on Shakespeare's plays is expected to perform poorly for regular applications in which most of the sentences are informal English ones. 

### The Zeroes
Intuition is that the longer the context, the more coherent. But longer context would increase training cost, and it might suffers from lack of combination of words (the **zeros**). 

The zeroes - combinations of words that don't ever occur in the training set but do occur in the test set. If we are building a trigram, we do see "denied the rumors" and "take the loan" in the training set, but when "denied the loan" occurs in the test set that we have never seen it before, according to Eq. (3), the probability of such sentence is reduced to 0.

Many approaches are developed to solve this. 
- Unknown words cause zeros:  we can use a **closed vocabulary** where unseen words are not allowed. or mark the out out vocabulary (OOV) words as a special token `<UNK>`. Estimate the probabilities for `<UNK>` just like any other regular word in the training set
- ***Smoothing*** can treat words that are in our vocabulary but in an unseen context. 
- ***interpolation*** and ***Backoff*** draw on "primitive" n-gram information to ameliorate the lack of information in a higher-n-gram model.

Laplace smoothing simply adds one to each count. 

### Smoothing
Smoothing (or discounting) means we shave off a bit of probability from some frequent events to those events that we never seen. Intuitively, you can imagine this approach would add bias to the model because after smoothing, the distribution is not the maximum likelihood. And you are right.

In Laplace smoothing, we simply adds one to each count thus there is no zeros in the. Take bigram for example, if we see a pair appears once in the real corpus, we record it actually twice. It introduces a huge bias.

Add-k smoothing is a modified version of Laplace smoothing. Instead of adding 1, add a small fraction k (.01?). 
### interpolation and Backoff
In **backoff**, we use trigram if the evidence suffice, else we use the bigram (and unigram if necessary). Sufficient evidence = not zero.

In **interpolation**, we mix the probability from all n-gram LMs. The term **linear interpolation** means the probability our LM gives is a linear combination of all n-gram models (Eq. 4)

$$P(w_n|w_{n-2}w_{n-1}) = \sum_{i=0} \lambda_i P(w_n|w_{n-1:n-i}) \tag 4 $$

## Evaluation of Language Models
Generally, there are two types of evaluation:
- ***extrinsic evaluation*** is to embed a LM in the real-world application (say a machine translator). it is practical, direct, but expensive, sometimes even impossible
- ***intrinsic evaluation*** is to measure the performance of an application by some metrics, independent of any application (traditional ML). But an intrinsic improvement doesn't guarantee an extrinsic improvement  

We would like to go for intrinsic evaluation first. The most popular intrinsic evaluation metric is the ***perplexity***. Perplexity describes how "surprising" the test set sounds like to our LM. Formally, the perplexity of a LM is the inverse probability of the test set. A test set consisted with N words $W = w_1 \cdots w_N$,

We have perplexity

$$\text{perplexity}(W) = P(w_1w_2\cdots w_N)^{-\frac{1}{N}} \tag 4$$

To calculate the perplexity, we should follow how the LM is defined. For instance, the perplexity of a bigram is (apply Eq .2 in Eq. 4) 

$$\text{perplexity}(W) = {\prod_{i=1}^N P(w_i|w_i-1)}^{-\frac{1}{N}} \tag 5$$

Lower perplexity often implies a better LM, as the test set is less surprising to our LM. But if we want to assure that it is indeed better in the real-world application, we still need to carry out extrinsic evaluation. 