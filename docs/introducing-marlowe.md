# Introducing Marlowe

This tutorial gives an overview of the ideas behind Marlowe, as a domain-specific languages embedded in Haskell. It also introuduces commitments and timeouts, which are central to how Marlowe works in a blockchain context. 

## Programming Languages and Domain-Specific Languages

The first computers were programmed in “machine code”. Each kind of system had a different code, and these codes were low-level and inexpressive: programs were long sequences of very simple instructions, incompressible to anyone who had not written them. Nowadays we are able to use higher-level languages like C, Java and Haskell to program systems. The same languages can be used on widely different machines, and the structure of the programs reflects what they do. On blockchain, their equivalents are languages like Solidity and Simplicity. These modern higher-level languages are general purpose – they can be used to solve all sorts of different problems – but the solutions they express are still programs, and they still require programming skills to use them effectively.

In contrast, Marlowe is a domain-specific language (DSL) which is designed to be usable by someone who is expert in a particular field: in the case of Marlowe, financial contracts, rather than requiring programming skills to use it. Using a DSL has many advantages beyond its use by non-programmers:

- We can ensure that certain sorts of bad programs cannot even be written by designing those possibilities out of the language, and by doing this we can aim to avoid some of the unanticipated exploits which have been a problem for existing blockchains.

- We can also more easily check that programs have the properties that we want: for example, in the case of a financial contract we might want to make sure that the contract can never fail to make a payment that it should.

- Because it is a DSL, we can build special-purpose tools to help people write programs in the language. In the case of Marlowe we can emulate how a contract will behave before it is run for real on the system; this helps us to make sure that the contract we have written is doing what it is intended to.

Marlowe is also an _embedded_ DSL, hosted in the [Haskell](https://www.haskell.org) programming language. While it is possible to use “pure” Marlowe if we wish, being embedded in a general-purpose language allows contract writers to selectively exploit features of Haskell in writing Marlowe contracts, making them easier to read, supporting re-use and so forth.

## Marlowe in a nutshell

Marlowe is modelled on financial contract DSLs popularised in the last decade or so by academics and enterprises such as LexiFi, which provides contract software in the financial sector. In developing Marlowe we have adapted these languages to work on blockchain. Marlowe is implemented on the settlement layer (SL) of the Cardano blockchain, but could equally well be implemented on Ethereum/Solidity or other blockchain platforms; in this respect it is “platform agnostic” just like modern programming languages like Java and C++. The Meadow online emulator tool allows you to experiment with, develop and interact with Marlowe contracts in your web browser, without having to install any software for yourself.

What does a Marlowe contract look like? It is built by combining a small number of building blocks that describe making a payment, making an observation of something in the “real world”, waiting until a certain condition becomes true, and so on. 

## Commitments and timeouts

Where we differ from non-blockchain approaches is in how we make sure that the contract is followed. This means not only that the instructions of the contract are not disobeyed (_“nothing bad happens”_), but also that the participants participate and don’t walk away early, leaving money locked up in the contract forever (_“good things actually happen”_). We do this using two constructs: commitments and timeouts.

A __commitment__ requires a participant to “put their money on the table” – more formally, to commit an amount of currency to the contract – and so to lock it up there for a certain period of time that is known in advance. If some or all of the currency remains in the contract at the end of the commitment period, then it can be reclaimed by the participant.

In our model a running contract cannot force a payment or a commitment to happen: all it can do is to request that a payment takes place, or to request a commitment from a participant. In other words it cannot “_push_” , but it can “_pull_”. How then deal with the situation in which a request to make a payment or to make a commitment is not acted upon? Using __timeouts__ we can make sure that if this commitment doesn’t happen in a timely manner then remedial action will be taken. This, in turn, ensures that contract execution will eventually progress, whether ot not contract participants choose to engage. 

## Marlowe in action

We are working on a production release of Marlowe on the Cardano blockchain later this year (2019). From today, you are able to explore Marlowe for yourself, either by downloading it and using the Haskell implementation directly, or by using the online Meadow simulation tool; these will both be covered in a subsequent tutorials. These will also cover the details of Marlowe, introduce a series of examples, look deeper into the tools for Marlowe and  In the next six months we’ll be polishing the language design itself and developing a set of templates for popular financial instruments, as well as using formal logic tools to prove properties of Marlowe contracts, giving users the highest level of assurance that their contracts behave as intended.



## Where to go to find out more 
- The Marlowe github repository: [link](https://github.com/input-output-hk/marlowe)
- The Marlowe paper: [link](https://files.zotero.net/19150029952/Seijas%20and%20Thompson%20-%20Marlowe%20financial%20contracts%20on%20blockchain.pdf)
- Marlowe video at PlutusFest, December 2018: [link](https://www.youtube.com/watch?v=rSpFOADHLqw)

### [Next tutorial](marlowe-data.md)