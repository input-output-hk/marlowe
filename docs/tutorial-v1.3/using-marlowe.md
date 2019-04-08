# Using Marlowe

This tutorial shows you how to use Marlowe from within Haskell, and in particular shows how to exercise a contract using the semantics given in the [earlier tutorial](./marlowe-semantics.md).

## Marlowe in Haskell

This tutorial works in `v1.3` of Marlowe, and to use it you need to clone the repository,
```bash
git clone https://github.com/input-output-hk/marlowe.git
```
Once you have done this, or if you have already cloned the repository, you need to  switch into version `v1.3`,
```bash
git checkout v1.3
```
Alternatively, you can perform the clone and version change in one step,
```bash
git clone -b 'v1.3' https://github.com/input-output-hk/marlowe.git
```
In either case, this command yields a warning:
```bash
Note: checking out 'v1.3'.
You are in 'detached HEAD' state. ...
```
but as you simply want to use Marlowe this can be safely ignored. (The warning message also tells you want you need to do if you do indeed want to make changes to this version of Marlowe).

## Stepping through contracts


As we saw in the [semantics for Marlowe](./marlowe-semantics.md) the semantics of a single block is defined by the function `stepBlock` of type
 ```haskell
stepBlock :: Input -> State -> Contract -> OS -> (State,Contract,AS)
```
which has the same type as `step`, as illustrated here: 

![the step type](./pix/step-type.png)

We can use the facilities of `ghci` to step through a contract one block at a time, and, here, we will do that with the embedded escrow contract contained in [`EscrowV2.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/EscrowV2.hs).

To single step you can work in `ghci` like this, using the facility to make local bindings:
```haskell
*Build> let (st1,c1,as1) = stepBlock input1 start_state escrow os0
*Build> let (st2,c2,as2) = stepBlock input2 st1 c1 os1
*Build> let (st3,c3,as3) = stepBlock input3 st2 c2 os2
*Build> ...
```
and then explore the values produced. Note, however, that the local bindings each time a `:load` or `:l` command is performed). 

An alternative way of doing this is to add these definitions to a working file, e.g. `Build.hs`, where these definitions will be preserved. Indeed, it would be very sensible to include some of the definitions used above in such a file.

The earlier description of the [semantics](./marlowe-semantics.md) concentrated on the high-level steps taken, and did not cover the constituent types in much detail. These are all defined in [`Semantics.hs`](https://github.com/input-output-hk/marlowe/blob/v1.3/src/Semantics.hs)

## States and Inputs

The `State` of a Marlowe contract  keeps track of the current state of the existing 
commitments (`sc`) and choices (`sch`) that have been made.
```haskell
data State = State {
               sc  :: Map.Map IdentCC CCStatus,
               sch :: Map.Map (IdentChoice, Person) ConcreteChoice
             }
```
and so, at the start, the state contains no information,
```haskell
start_state = State Map.empty Map.empty
```
and, at each block, the `OS` contains a random number and the current block number, so for the cases above
```haskell
os0 = OS 42 1
os1 = OS 42 2
```
For the contract to progress, it needs to be presented with inputs, as represented by the `Input` type, which has  four components
  - a set `cc` of cash commitments made at that step
  - a set `rc` of cash redemptions made at that step
  - a map `rp` of payment requests made at that step, and
  - a map `ic` of choices made at that step

```haskell
data Input = Input {
                cc  :: Set.Set CC,
                rc  :: Set.Set RC,
                rp  :: Map.Map (IdentPay, Person) Cash,
                ic  :: Map.Map (IdentChoice, Person) ConcreteChoice
              }
```
In practice, we could use sets for all of them,
but using a map ensures that there is only one
entry per identifier / person pair and would
make access more efficient if we needed to find
an entry without knowing the concrete choice
or amount of cash being claimed.

## Back to single stepping

To single step through the escrow contract we construct three inputs to represent a commitment, two choices being made and a payment. Together these represent the successful execution of the escrow contract: Alice gets the cat, and Bob the money.
```haskell
input1,input2,input3 :: Input

input1 = Input (Set.singleton cc1) Set.empty Map.empty Map.empty
            where
                cc1 = CC (IdentCC 1) 1 450 100

input2 = Input Set.empty Set.empty Map.empty map1
            where
                map1 = Map.fromList [((IdentChoice 2,2),1),
                                     ((IdentChoice 3,3),1)]

input3 = Input Set.empty Set.empty map2 Map.empty 
            where
                map2 = Map.singleton (IdentPay 1,2) 450
```                    
Why is single stepping useful? It is the equivalent of debugging, and we are able to see the internal state of the contract at each stage, the contract _continuation_, i.e. what remains to be executed, and the actions produced at each step.

> __Exercise__
>  
> Explore some other ways of engaging with the contract
> - What happens when two participants choose to refund the money to Alice? 
> - What happens if Bob requests a payment before the choice is made to make the payment to him?
> - What happens if the contract reaches timeout? 
>
> The last case here is tedious to do by hand, so next we look at another way of engaging with contracts.

## Building sequences of inputs and `OS` values

Single stepping allows us to see the “internal state” of a contract as it evolves, but it can be tedious to do that when a timeout might be set for block 100, as in the case of `escrow`. We can instead use the `driver` function 
```haskell
driver :: State -> Contract -> [(Input,OS)] -> [AS]
```
that takes a (lazy) list of `Input` and `OS` pairs, one for each block, and delivers the corresponding list of (sets of) actions, `AS`, block by block.

> __Exercise__
>  
> To assist in constructing input/OS sequences for `driver`, define the value  `empties` and the function `wrap`
> 
> ```haskell
> -- a list of empty inputs 
> empties :: [Input]
>
> -- wrap a list of inputs with OS values
> -- 42 as constant random value
>
> wrap :: [Input] -> [(Input,OS)]
> ```





>
> __Exercise__
>  
> Using the `driver` function, explore how the `escrow` contract behaves 
> - in the two scenarios when choices are made,  
> - on timeout of the original commitment, when Alice's original payment can be 
>     redeemed, and
> - in situations where inputs are presented out of order.
>


>
> __Exercise__
>  
> The `escrow` contract has been written so that _any two_ participants can choose 
> one of the options; modify it so that it is more precise, identifying the two 
> participants who can make the two choices. 
>
> Add a third choice to the contract whereby Alice and
> Bob can choose for the money to go to one of the three participants, chosen randomly.
> Devise inputs that will demonstrate the correct behaviour of the contract; you may wish to modify the `wrap` function so that it contains a (repeatable) sequence of random choices of `1`, `2` or `3`.


## There must be an easier way!

Yes, there is! 
       
We look next at how we can build a tool, Meadow, that will capitalise on the fact that we are working in a DSL to _automate_ picking the right inputs and allow users to interact with contracts.


### [Prev](./embedded-marlowe.md) [Up](./README.md) [Next](./meadow-overview.md)