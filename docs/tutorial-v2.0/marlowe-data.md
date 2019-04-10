# Marlowe as a Haskell data type

This tutorial formally introduces Marlowe as a Haskell data type, building on the escrow example from the previous tutorial. It also describes the different types used by the model, as well as discussing a number of assumptions about the infrastructure in which contracts will be run.

## Marlowe

The Marlowe domain-specific language (DSL) is modelled as an algebraic type in Haskell: the `!` symbol makes a constructor strict in a particular argument. In our case we choose to make Marlowe strict in all arguments to all constructors, which has the effect of making Marlowe contracts strictly finite as data structures. 

```haskell
data Contract =
    Null |
    Commit !IdAction !IdCommit !Person !Value !Timeout !Timeout !Contract !Contract |
    Pay !IdAction !IdCommit !Person !Value !Timeout !Contract !Contract |
    Both !Contract !Contract |
    Choice !Observation !Contract !Contract |
    When !Observation !Timeout !Contract !Contract |
    While !Observation !Timeout !Contract !Contract |
    Scale !Value !Value !Value !Contract |
    Let !LetLabel !Contract !Contract |
    Use !LetLabel
               deriving (Eq,Ord,Show,Read)
```

```haskell
data Contract =
   Null |
   CommitCash IdentCC Person Money Timeout Timeout Contract Contract |
   RedeemCC IdentCC Contract |
   Pay IdentPay Person Person Money Timeout Contract |
   Both Contract Contract |
   Choice Observation Contract Contract |
   When Observation Timeout Contract Contract
```

Informally, this type provides these contracts.
- A `Null` contract, which does nothing. 
- The next two constructs are the simplest contract-building prmitives. They contain two sub-contracts: the first to be followed if the action has been performed successfully, and the second to use in the case of a timeout.
    - `Commit` will wait for a participant to make a commitment, and 
    - `Pay` will wait for a payment to be claimed by the recipient.
 
- The remaining constructors form composite contracts from simpler components, including `Contract`s and `Observation`s: 
  - `Both` has the behaviour of both its components, 
  - `Choice` chooses between two contracts on the basis of an observation,  
  - `When` is quiescent until a condition – an observation – becomes true,
  - `While` is active until a condition becomes false.
  - `Scale` is used to scale the scalar values in a contract, and
  - `Let` and `Use` allow for making and using local definitions (“shorthand”) within a contract.

Additionally, many of the contracts have timeouts that also help to shape their behaviour. 


## The model types

A running contract interacts with its environment in two ways, as shown here.

![Environment](./pix/context.png)

### Observables 

First, it  needs to _observe_ different kinds of varying quantities including, for example, the current time, the current block number and sources of random numbers, as well as “real world” quantities like “the price of oil” or “the exchange rate between currencies A and B”. 

As the examples illustrate, observables come both from aspects of the blockchain (e.g. the current block or slot number) and externally. In the latter case, all participants of the contract will need to agree on a trusted oracle or source of information. Each instance of such an observable will be observed at a particular time and in a particular context. 

<!--We assume that the system infrastructure ensures that these values are recorded on the blockchain to allow the computation to be repeated for verification purposes.
-->
It is assumed that at each step of the execution of the contract, the values of observables will be available if needed, and these values are (together) given by a value of type `OS` (for “observable set”), where individual observations are described in a “little language” for that purpose: `Observation`. Note that these values are not determined by the participants in the contract, but rather by the external environment in which the contract is run.

While we provide some built-in observations, we expect to extend this type. For instance, using `ValueGE` we can check whether one value is greater than or equal to another, but we have not added primitives for equality, or ‘less than or equal’. On the other hand, we can build complex logical combinations of observations using `OrObs` and `NotObs`, and so, if we wished, we could define an equality for values this way.

### Inputs and Commitments 

On the other hand, at each step there are – potentially, at least – a variety of inputs available from the participants themselves. These include commitments of currency (or “cash”), redemption of commitments, and claims of payments by a participant. Moreover, it is also possible for a participant to input an arbitrary value (which we term a “choice”). The particular inputs at a given step are described by a value of type `Input`.

While informally we might see a commitment to something as being indefinite, as noted earlier, it is important to realise that, on blockchain, a commitment needs to have a timeout so that progress is ensured in contracts. After the timeout period, the cash can be refunded through the user creating a transaction to reclaim the cash. Information about the commitments currently in force forms the `State`, which can be modified at each execution step.

### Actions 

Payments can be granted by using committed money, but they must be manually redeemed by the recipient, in the same way that cash commitments are redeemed when they expire. The effects of the contract in the blockchain are represented by a list `AS` of `Actions` that is derived from the execution of each step of the semantics.

### People 

In the semantics for  Marlowe we use integers to model people; on blockchain we will use public keys for this purpose.

### Infrastructure 

The model makes a number of assumptions about the blockchain infrastructure in which it is run.
- It is assumed that cryptographic functions and operations are provided by a layer external to Marlowe, and so they need not be modelled explicitly.
- We assume that time is “coarse grained” and measured by block or slot number, so that, in particular, timeouts are delimited using block/slot numbers.
- Making a commitment is not something that a contract can perform; rather, it can request that a commitment is made, but that then has to be established externally: hence the input of (a set of) commitments at each step.
- The model manages the release of funds back to the committer when a cash commitment expires (see discussion of the stepBlock function below).
 
## Notes

- Marlowe 2.0 extends the Marlowe type with local definitions and a `While` construct.
- The informal semantics of Marlowe 2.0 differs from that presented here, replacing sets of input and observations with individual values. This is done to guarantee that the semantics is deterministic.

### [Prev](./escrow-ex.md) [Up](./README.md) [Next](./marlowe-semantics.md)