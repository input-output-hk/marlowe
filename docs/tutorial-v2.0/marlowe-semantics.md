# The semantics of Marlowe 2.0

This tutorial gives a high-level formal semantics of Marlowe 2.0 by describing the types of inputs supported, and the main semantic functions.

In general, participants in a Marlowe contract communicate with the contract by issuing _transactions_. At each block, a sequence of zero or more transactions can be processed – in sequence – by a contract.

From the point of view of the semantics, a transaction consists of a list of inputs, and the whole transaction may be _signed_ by one or more participants. Concretely, we represent a transaction as a list of `AnyInput`s together with a set of integers representing the set of signatories.

As we mentioned in [the previous tutorial](./marlowe-data.md), inputs can have one out of four kinds: `Commit`, `Pay`, `Choice`, and `Oracle`. Of these, `Commit` and `Pay` are considered to be _actions_ and are typically associated with the transfer of money between a participant and the contract. `Choice` and `Oracle` are used to provide information from the external world to the contract.

## The `applyTransaction` function

The effect of executing a transaction in a Marlowe contract is modelled by the top-level function `applyTransaction`. This takes the transaction to process and the current state of the contract (including the internal state, the remaining contract, and the amount of funds remaining in the contract), and it returns the new state of the contract together with the amount of money that each participant is supposed to transfer to or from the contract as part of the transaction.

<p align="center">
 <img width="100%" src="pix/applyTransaction.svg">
</p>

The `applyTransaction` function has the following Haskell type:

```haskell
applyTransaction :: [AnyInput] -> S.Set Person -> BlockNumber -> State -> Contract -> Integer
                    -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
```

In turn, the `applyTransaction` function calls three principal auxiliary functions: `reduce`, `fetchPrimitive`, and `eval`.

- The `reduce` function (and its auxiliary function `reduceRec`) are applied before and after each input, 
- `fetchPrimitive` is applied only for inputs that are actions (i.e: `Commit`s and `Pay`s), and 
- `eval` is applied to the result of `fetchPrimitive` whenever appropriate.

In addition to these three functions, there are three additional functions that are applied in every transaction. Before processing the inputs, the function `expireCommits` is applied, and after processing the inputs the functions `redeemMoney` and `simplify` are applied.

<p align="center">
  <img width="500px" src="pix/flowchart.svg">
</p>

## Action processing

Let us start by looking at the parts of the processing that the semantics does exclusively for actions (that is, inputs of the kind `Commit` and `Pay`).

An action is represented by its `IdAction`. The function `fetchPrimitive` will traverse the parts of the contract that are currently in force (activated) and look for a primitive that matches the `IdAction` provided by the input. `fetchPrimitive` will only succeed if there is exactly one primitive that corresponds to the given `IdAction`.

```haskell
fetchPrimitive idAction blockNum state (Both leftContract rightContract) =
  case (go leftContract, go rightContract) of
     (Picked (result, cont), NoMatch) -> Picked (result, (Both cont rightContract))
     (NoMatch, Picked (result, cont)) -> Picked (result, (Both leftContract cont))
     (NoMatch, NoMatch) -> NoMatch
     _                  -> MultipleMatches
  where go = fetchPrimitive idAction blockNum state
```

If it succeeds, `fetchPrimitive` will return a `DetachedPrimitive`:

```haskell
data DetachedPrimitive = DCommit IdCommit Person Integer Timeout
                       | DPay IdCommit Person Integer
```

`fetchPrimitive` will also return the contract after removing the chosen primitive; this new contract will be taken as the remaining contract if the evaluation succeeds. The `DetachedPrimitive` is passed to `eval`, together with the current `State` of the contract.

```haskell
fetchPrimitive :: IdAction -> BlockNumber -> State -> Contract
               -> FetchResult (DetachedPrimitive, Contract)
```

### `Commit`

A `Commit` allows a participant `person` to transfer to the contract an amount of money `value`. This money will be recorded in the contract under the identifier `idCommit` and future payments can use this identifier as a source of money. Once the block specified by `timeout` (the second `Timeout` in `Commit`) is reached, any money from the `Commit` that has not been spent (through payments) will be frozen, and the participant that performed the commitment will be able to withdraw with the next transaction that he or she signs.

```haskell
eval (DCommit idCommit person value timeout) state =
  if (isCurrentCommit idCommit state) || (isExpiredCommit idCommit state)
  then InconsistentState
  else Result ( addOutcome person (- value) emptyOutcome
              , addCommit idCommit person value timeout state )
              NoProblem
```

For a commitment to be valid, no commitment with the identifier `idCommit` must have been issued before (only one `Commit` per identifier is allowed).

In addition, `reduceRec` (the auxiliary function of `reduce`) specifies that a `Commit` will be reduced to its second `continuation` if any of the timeouts is reached.

```haskell
reduceRec blockNum state env c@(Commit _ _ _ _ timeout_start timeout_end _ continuation) =
  if (isExpired blockNum timeout_start) || (isExpired blockNum timeout_end)
  then reduceRec blockNum state env continuation
  else c
```

**COMMENT: this next sentence seems not be linked with what comes before. Specifically, "instead of" what? (Same comment for `Pay` too)** 
The `fetchPrimitive` function will use the first continuation (the first `Contract` in `Commit`) instead.

### `Pay`

A `Pay` allows a participant `person` to claim from the contract an amount of money `value`. This money will be discounted from the money committed under the identifier `idCommit`, and the contract will only pay up to the amount that remains available under `idCommit`, even if there is extra money available in the contract. In any case, `Pay` will pay no money if the commit `idCommit` has expired.

```haskell
eval (DPay idCommit person value) state =
  if (not $ isCurrentCommit idCommit state)
  then (if (not $ isExpiredCommit idCommit state)
        then Result (emptyOutcome, state) CommitNotMade
        else Result (emptyOutcome, state) CommitIsExpired)
  else (if value > maxValue
        then Result ( addOutcome person maxValue emptyOutcome
                    , fromJust $ discountAvailableMoneyFromCommit idCommit maxValue state )
                    NotEnoughMoneyLeftInCommit
        else Result ( addOutcome person value emptyOutcome
                    , fromJust $ discountAvailableMoneyFromCommit idCommit value state )
                    NoProblem)
  where maxValue = getAvailableAmountInCommit idCommit state

```

Regarding `reduceRec`, `Pay` behaves similarly to `Commit` except in that `Pay` only has one `Timeout`; `Pay` will be reduced to its second `continuation` if its timeout is reached before it is claimed.

```haskell
reduceRec blockNum state env c@(Pay _ _ _ _ timeout _ continuation) =
  if isExpired blockNum timeout
  then reduceRec blockNum state env continuation
  else c
```

Again, the `fetchPrimitive` function will use the first continuation (the first `Contract` in `Pay`) instead.

## Non-action input processing

`Choice`s and `Oracle`s inputs are processed very differently to actions. They are relatively independent of the state of the contract, and they may be issued at any time, as long as the values provided can potentially be used by the contract. In other words, there must be somewhere in the code of the contract that inspects the `Choice` or `Oracle` value in order for a participant to be able to provide that value. Otherwise, the contract does not need to know the value, and providing it anyway would just be adding clutter and load to the contract and blockchain, which could end up translating into problems like DoS. For these reasons, the Marlowe 2.0 semantics disallows providing  information that is not required.

Other than that, the only thing that Marlowe does when provided with `Choice`s and `Oracle`s is to record them in the state so that the `reduce` function can access them.

## Reducing contracts
<!-- Combinators and `Null` -->

In this section, we describe the remaining Marlowe contracts, which in general can be used to combine other contracts together and to decide between them depending on the information known to the contract at any given moment.

**NEED SOMETHING HERE that explains that `reduce/Rec` is being described? Could be reflected in the title, which I have modified. A short paragraph should be enough. Also add a type for `reduce/Rec`?** 

### `Null`

The `Null` contract does nothing and stays quiescent forever.

```haskell
reduceRec _ _ _ Null = Null
```

Nevertheless, it is used by the `simplify` function and it can be used to replace a contract by a smaller but equivalent one. For example, `Both Null Null` can be reduced to `Null`

### `Both`

The `Both` construct allows two contracts to be active simultaneously. It would be like having two separate contracts deployed simultaneously, except in that when using `Both` they will share `State`, and thus `Commit`s made in one of the contracts can be used for `Pay`s in the other contract. We have also taken a lot of care in ensuring that `Both` is symmetric, that is, writing `Both A B` should be equivalent to writing `Both B A`, no matter what `A` and `B` are.

```haskell
reduceRec blockNum state env (Both cont1 cont2) = Both (go cont1) (go cont2)
  where go = reduceRec blockNum state env
```

### `Choice`

The `Choice` construct immediately chooses between two contracts depending on the value of an `Observation`. The moment that `Choice` is activated, the value of `obs` will decide whether `Choice` gets reduced to `cont1` (if it is true) or to `cont2` (if it is false).

```haskell
reduceRec blockNum state env (Choice obs cont1 cont2) =
  reduceRec blockNum state env (if (evalObservation blockNum state obs)
                                then cont1
                                else cont2)
```

### `When`

The `When` construct delays a contract in time until an `Observation` becomes true. `When` will not activate any of its subcontracts until either the `Observation` becomes true, or until the `timeout` block is reached. If `obs` is true, then `When` is reduced to `cont1`, if `timeout` has been reached, then `When` is reduced to `cont2`.

```haskell
reduceRec blockNum state env c@(When obs timeout cont1 cont2) =
  if isExpired blockNum timeout
  then go cont2
  else if evalObservation blockNum state obs
       then go cont1
       else c
  where go = reduceRec blockNum state env
```

It is worth noting that, because Marlowe follows a ‘pull’ model, it is not just enough for the `Observation` to become true for `When` to evolve; the contract needs to be triggered while the `Observation` is true. The contract can be triggered at any time by issuing a transaction that does not need to have any inputs and does not need to be signed; indeed anyone can trigger the contract.

### `While`

The `While` construct works in the opposite way to `When`, in the sense that while `When` gets reduced when it `Observation` becomes true, `While` gets reduced when its `Observation` becomes false.

```haskell
reduceRec blockNum state env (While obs timeout contractWhile contractAfter) =
  if isExpired timeout blockNum
  then go contractAfter
  else if evalObservation blockNum state obs
       then (While obs timeout (go contractWhile) contractAfter)
       else go contractAfter
  where go = reduceRec blockNum state env
```

However, there is one fundamental difference: `When` does not activate its subcontract until it gets reduced, and `While` activates its subcontract immediately, similarly to the behaviour of `Both`. And there is something unique about `While`: it may delete a contract that has already been activated once the `Observation` becomes true. 
For example, in the following contract: 

```
While 
  (NotObs 
     (ChoseSomething (1, 1))) 20 
  (Commit 1 1 1 
     (ValueFromChoice (1, 1) 
        (Constant 20)) 10 20 Null Null) Null
```

once the choice `(1, 1)` is made, it will no longer be possible to use the `Commit`.

### `Scale`

The `Scale` construct scales the amounts paid by `Commit` and `Pay`. It takes three `Value`s, the first one is the numerator, the second one is the denominator, and the third one is the default.

As soon as the `Scale` construct is activated, it activates its subcontract `contract`, and it evaluates all the three `Value`s and replaces them with a `Constant` (so that they may not change any more).

```haskell
reduceRec blockNum state env (Scale divid divis def contract) =
  Scale (Constant vsDivid) (Constant vsDivis) (Constant vsDef) (go contract)
  where go = reduceRec blockNum state env
        vsDivid = evalValue blockNum state divid
        vsDivis = evalValue blockNum state divis
        vsDef = evalValue blockNum state def
```

Once evaluated, any inner `Commit` or `Pay` (in `contract`) will get their amount scaled as follows:

- If the divisor is `0`, then the amount is replace with the default.
- If the divisor is not `0`, then the amount is multiplied by the numerator, and divided (using integer division) by the denominator.

```haskell
scaleValue :: Integer -> Integer -> Integer -> Integer -> Integer
scaleValue divid divis def val = if (divis == 0) then def else ((val * divid) `div` divis)
```

The process of scaling `Commit`s and `Pay`s is carried out by the `fetchPrimitive` function.

```haskell
fetchPrimitive idAction blockNum state (Scale divid divis def subContract) =
  case fetchPrimitive idAction blockNum state subContract of
     Picked (result, cont) -> Picked (scaleResult sDivid sDivis sDef result,
                                      Scale divid divis def cont)
     NoMatch -> NoMatch
     MultipleMatches -> MultipleMatches
  where sDivid = evalValue blockNum state divid
        sDivis = evalValue blockNum state divis
        sDef = evalValue blockNum state def
```

Once there are no `Commit`s or `Pay`s inside a `Scale`, it gets removed by the `simplify` function.

### `Let` and `Use`

**TODO**

### [Prev](./marlowe-data.md) [Up](./README.md) [Next](./embedded-marlowe.md)
