# Marlowe Tutorials

This document gives an overview of a set of Marlowe tutorials.

> __Important note:__ these tutorials address Marlowe 1.3, which 
> is the version implemented in the current version of Meadow,
> and is covered in the ISoLA paper. This version is tagged as **v1.3**
> and is available here: [https://github.com/input-output-hk/marlowe/tree/v1.3](https://github.com/input-output-hk/marlowe/tree/v1.3).
>
> They will be updated for [the summit in April](https://iohksummit.io) to cover Marlowe 2.0, which irons out
> a number of infelicities in 1.3, and which will be in the version released at the summit.

##  [Introducing Marlowe](./introducing-marlowe.md)

This tutorial gives an overview of the ideas behind Marlowe, as a domain-specific languages embedded in Haskell. It also introduces commitments and timeouts, which are central to how Marlowe works in a blockchain context. 

## [A first example: the escrow contract](./escrow-ex.md)

This tutorial introduces a simple financial contract in pseudocode, before explaining how it is modified to work in Marlowe, giving the first example of a Marlowe contract.

## [Marlowe as a Haskell data type](./marlowe-data.md)

This tutorial formally introduces Marlowe as a Haskell data type, building on the escrow example in the previous tutorial. It also describes the different types used by the model, as well as discussing a number of assumptions about the infrastructure in which contracts will be run.

## [Understanding the semantics](./marlowe-semantics.md)

This tutorial gives a formal semantics for Marlowe by presenting a Haskell definition of the semantic `step` function, so that we have a _semantics that we can execute_. 

## [Embedded Marlowe](./embedded-marlowe.md)

This tutorial shows how to use some simple features of Haskell to write Marlowe contracts that are more readable, maintainable and reusable, by revisiting the  escrow contract.

## [Using Marlowe](./using-marlowe.md)

This tutorial shows you how to use Marlowe from within Haskell, and in particular shows how to exercise a contract using the semantics given in the [earlier tutorial](./marlowe-semantics.md).

## [Meadow overview](./meadow-overview.md) 

This tutorial introduces Meadow, and is accompanied by a video. Once you have followed this video you will be able to use Meadow to interact with the escrow and other Meadow contracts.

## [Other functions in Marlowe: analysis](./analysis.md)

Understanding aspects of a contract without running it.

## [ACTUS and Marlowe](./actus-marlowe.md)

Introduction to the general idea of the ACTUS taxonomy, plus examples implemented in Marlowe (at least the PAM contract, and hopefully others).

## [Implementing Marlowe in Plutus](./marlowe-plutus.md)

So far these tutorials have dealt with Marlowe as a “stand alone” artefact; this tutorial describes how Marlowe is implemented on blockchain, using the “mockchain” that provides a high-fidelity simulation of the Cardano SL layer.

