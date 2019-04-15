
# Learning about Marlowe and Meadow

Marlowe is a domain-specific language (DSL) for writing financial contracts that run on blockchain. 

This document describes the different materials available for learning about Marlowe and the online tool that accompanies it: Meadow. It also advises you where to begin, depending on what you want to learn, and where you are starting from.

Marlowe is realised as DSL embedded in Haskell, but it is possible to use Marlowe without being a Haskell expert. Marlowe is a live project, and the materials here describe two versions of Marlowe: the earlier [version 1.3]( https://github.com/input-output-hk/marlowe/tree/v1.3), and the [current version](https://github.com/input-output-hk/marlowe/), 2.0.

Meadow is also available in two versions:

* The [original Meadow tool](https://input-output-hk.github.io/marlowe/) supports v1.3, including contract development using Blockly, a visual programming environment. It also supports the development of “embedded” contracts using aspects of Haskell, but because this runs a Haskell environment in the browser, it has a substantial latency.

* The latest version, [Meadow in the cloud](https://prod.meadow.marlowe.iohkdev.io), supports development of embedded contracts is a much more efficient way, as well as presenting a substantially cleaner interface, but doesn't currently support visual program development.

## Where should I start?

I want to learn the ideas behind Marlowe, but not to write Marlowe contracts myself.

* The first parts of the tutorial, [link](./tutorial-v1.3/README.md), and the Udemy course, [link](https://www.udemy.com/marlowe-programming-language/), will give you this introduction.

I want to learn how to write simple Marlowe contracts, and to run them in the Meadow tool.

* The Udemy course, [link](https://www.udemy.com/marlowe-programming-language/),  and tutorial, [link](./tutorial-v1.3/README.md), will give you an introduction to building contracts using Blockly.
* If you are not a Haskell programmer, then you can skip the tutorial sections on [Understanding the semantics](./tutorial-v1.3/marlowe-semantics.md) and [Using Marlowe](./tutorial-v1.3/using-marlowe.md).

I have learned about Marlowe 1.3, and written contracts there, but I want to convert to v2.0 use Meadow in the cloud.

* You can find out about the differences in v1.3 and v2.0 [here](./tutorial-v1.3/differences.md), and this checklist, [link](./tutorial-v1.3/checklist.md), will help you to convert contracts from v1.3 to v2.0.

I am a Haskell programmer, and I want to get started developing Marlowe contracts embedded in Haskell and to run them in Haskell and Meadow.

* To do this, follow the tutorial on the current version of Marlowe, [link](./tutorial-v2.0/README.md), and develop your programs in Meadow in the cloud, [link](https://prod.meadow.marlowe.iohkdev.io).

## Materials available

This section lists all the learning resources for Marlowe and Meadow.

* Tutorial for version 1.3 of Marlowe and the first version of the Meadow tool. [Link](./tutorial-v1.3/README.md)
* Tutorial for version 2.0 of Marlowe and Meadow in the cloud. [Link](./tutorial-v2.0/README.md)
* An overview of the differences between v1.3 and v2.0. [Link](./tutorial-v1.3/differences.md)
* A checklist for converting a v1.3 contract to v2.0. [Link](./tutorial-v1.3/checklist.md)
* Udemy course on Marlowe (v1.3) and Meadow. [Link](https://www.udemy.com/marlowe-programming-language/)
* Paper on Marlowe, describing v1.3 and the orginal Meadow. [Link](https://iohk.io/research/papers/#2WHKDRA8)
* Video run-through of the original Meadow. [Link](https://youtu.be/_loz70XkHM8)

