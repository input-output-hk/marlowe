# Marlowe Tutorials

This document gives an overview of a set of Marlowe tutorials.

> Important note: these tutorials address Marlowe 1.3, which 
> is the version implemented in the current version of Meadow,
> and is covered in the ISoLA paper.

> They will be updated to cover Marlowe 2.0, which 
> will be in the new version of Meadow, for the summit in April.

### Contributing materials
- Marlowe paper from ISoLA
- Marlowe section in the Plutus platform paper
- The Meadow video from PlutusFest
- Examples from repo and presentations
- Using the functions in the Marlowe codebase
  - Particularly the semantics and analysis functions
- ACTUS example(s)
- Marlowe 2.0 rationale

##  [Introducing Marlowe](./introducing-marlowe.md)

This tutorial gives an overview of the ideas behind Marlowe, as a domain-specific languages embedded in Haskell. It also introduces commitments and timeouts, which are central to how Marlowe works in a blockchain context. 

## [A first example: the escrow contract](./escrow-ex.md)

As introduced in the slides from PlutusFest.


## [Marlowe as a Haskell data type](./marlowe-data.md)

The constructors of Marlowe: informal introduction.

- Simple exercise building a contract.
## Understanding the semantics

Based on the ISoLA paper

## Meadow overview (part 1)

A tour of the some of the facilities; the video accompanies this.

Include an image with callouts.

## An example in Meadow

Exercising an example: taking it through its paces in Meadow.

## Other functions in Marlowe: analysis

Understanding aspects of a contract *without* running it.

## Marlowe as an embedded DSL

Using the embedding to define common values, functions etc.

- Smart constructors?

## Meadow overview (part 2)

Looking at the *elaboration* of embedded contracts (or whatever else we call it) into pure Marlowe.

## ACTUS

Introduction to the general idea of the ACTUS taxonomy.

## ACTUS example(s) in Marlowe

At least the PAM contract, and hopefully others.

## Marlowe as a Plutus contract

Marlowe on mockchain: from the Plutus platform paper.

## For the future: Marlowe 1.3 and 2.0

*Might just include this as an appendix.*

What has changed in moving from 1.3 (the version in the ISoLA paper) and the current version. This is added to put this document into context, and to give an indication of how sections of this tutorial will have be changed before the summit in April.


