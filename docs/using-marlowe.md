# Using Marlowe

This tutorial shows you how to use Marlowe from within Haskell, and explores a number of examples.

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




As we saw in the previous 
 

Computation is modelled at two different levels.

The step function represents a single computation step and has this type:
```haskell
step :: Input -> State -> Contract -> OS -> (State,Contract,AS)
```
which is also illustrated here: 

![the step type](./pix/step-type.png)

The `step` function is total, so that for every contract a result of stepping is defined. However, for some kinds of contracts – commits, redeems or time-shifted contracts – it is possible that performing a step produces the same contract as the result; we call these _quiescent_ steps whereas all others make progress. We use this distinction in the explanation that follows.

Execution of a contract will involve multiple blocks, with multiple steps in each block. The computation at a single block is given by the `stepBlock` function: this will call the `stepAll` function that calls `step` repeatedly until it is quiescent.
In addition to calling `stepAll`, `stepBlock` will first enable expired cash commitments to be refunded and record, in the state, any choices made at that step. The functions `stepAll` and `stepBlock` have the same type as `step` itself.

We now explain the detailed behaviour of contracts by describing how the `step` function operates on each of the constructors of the `Contract` type.

### `Null`

`Null` is the null contract; it will always be quiescent: 
```haskell
step _ st Null _ = (st, Null, [])
```

### `CommitCash`

`CommitCash ident person val start_timeout end_timeout con1 con2`: in order for this contract to make progress,
- either, before the timeout `start_timeout`, the user `person` makes a cash commitment of value `val` and timeout `end_timeout` with  identifier `ident`,
- or the timeout `start_timeout` is exceed:
```haskell
step
    commits
    st
    c@(CommitCash ident person val start_timeout end_timeout con1 con2)
    os
    | cexe || cexs 
          = (st {sc = ust}, con2, [])
    | Set.member (CC ident person cval end_timeout) (cc commits)
          = (st {sc = ust}, con1, [SuccessfulCommit ident person cval])
    | otherwise 
          = (st, c, [])
    where ccs = sc st
          cexs = expired (blockNumber os) start_timeout
          cexe = expired (blockNumber os) end_timeout
          cns = (person, if cexe || cexs
                            then ManuallyRedeemed
                            else NotRedeemed cval end_timeout)
          ust = Map.insert ident cns ccs
          cval = evalMoney st val
```          
In the first case, a `SuccessfulCommit` action is generated and the contract continues as `con1`; in the second case no action is generated and the contract continues as `con2`. While neither case holds, the contract is quiescent, waiting for the cash to be committed.

If the cash is committed successfully and the timeout `end_timeout` is reached, then it is impossible to further spend the committed cash, and any unspent funds can be reclaimed by `person`. This is enforced by the `stepBlock` function, as noted above.

### `RedeemCC`

`RedeemCC ident con` (`CC` stands for ‘cash commitment’). In order for this contract to make progress, the creator of the cash commitment with identifier `ident` is allowed to redeem the unspent funds in that commitment; the contract then continues as `con`, and the action `CommitRedeemed` is produced.
```haskell
step commits st c@(RedeemCC ident con) _ =
      case Map.lookup ident ccs of
        Just (person, NotRedeemed val _) ->
          let newstate =
            st {sc = Map.insert ident (person, ManuallyRedeemed) ccs}
          in
            if Set.member (RC ident person val) (rc commits)
            then (newstate, con, [CommitRedeemed ident person val])
            else (st, c, [])
        Just (person, ManuallyRedeemed) ->
          (st, con, [DuplicateRedeem ident person])
        Nothing -> 
          (st,c,[])
  where
  ccs = sc st
```
Committed cash can only be redeemed once, and an attempt to redeem it a second time will produce a `DuplicateRedeem` action, continuing as `con`.
If the cash commitment with identifier `ident` has expired, it becomes possible
for the remaining funds to be redeemed by the committer; this can be done by the `stepBlock` function processing the appropriate `Input`, and an `ExpiredCommitRedeemed` action will be produced. Once the commitment `ident` has expired and is redeemed, a `RedeemCC ident con` contract will immediately evolve to `con`.

### `Pay`

`Pay idpay from to val expi con` makes it possible, assuming that sufficient funds are available, for `to` to claim a payment with id `idpay` of `val` from `from` before the timeout `expi`. The contract continues as `con`.
```haskell
step inp st c@(Pay idpay from to val expi con) os
    | expired (blockNumber os) expi 
       = (st, con, [ExpiredPay idpay from to cval])
    | right_claim
       = if ((committed st from bn >= cval) && (cval >= 0))
         then (newstate, con, [SuccessfulPay idpay from to cval])
         else (st, con, [FailedPay idpay from to cval])
    | otherwise 
       = (st, c, [])
    where
      cval = evalMoney st val
      newstate = stateUpdate st from to bn cval
      bn = blockNumber os
      right_claim =
        case Map.lookup (idpay, to) (rp inp) of
          Just claimed_val -> claimed_val == cval
          Nothing -> False
```
By ‘available’ we mean that sufficient commitments have been made and not yet expired to cover the payment; in this case, the payment uses the currency allocated by the cash commitments made by `from` that expire the earliest. This contract will result in a `FailedPay` action if the funds are not available; otherwise a `SuccessfulPay` action is generated.

### `Both`
`Both con1 con2` enforces the behaviour of both contracts `con1` and `con2`. 
```haskell
step comms st (Both con1 con2) os =
      (st2, result, ac1 ++ ac2)
      where
          result | res1 == Null = res2
                 | res2 == Null = res1
                 | otherwise = Both res1 res2
          (st1,res1,ac1) = step comms st con1 os
          (st2,res2,ac2) = step comms st1 con2 os
```          
Because the model is _stateful_ and produces output actions, to make a step, it is necessary to execute a single step of each of the contracts `con1` and `con2` in sequence: first `con1` then `con2`.

### `Choice`

`Choice obs conT conF` behaves as either `conT` or `conF` depending on the (Boolean) result of `obs` at the time that the observation is made, `conT` if it is
`True` and `conF` if `False`.
```haskell
step _ st (Choice obs conT conF) os =
       if interpretObs st obs os
       then (st,conT,[])
       else (st,conF,[])
```

### `When`

`When obs expi con con2` This contract will not progress until `obs` is `True` or until the current block number is greater than or equal to the one specified by timeout `expi`. In case the timeout applies, the contract will continue as `con2`; if the timeout does not apply and `obs` is `True`, then the contract continues as `con`. Otherwise the contract is quiescent.
 ```haskell
 step _ st (When obs expi con con2) os
     | expired (blockNumber os) expi 
       = (st,con2,[])
     | interpretObs st obs os 
       = (st,con,[])
     | otherwise 
       = (st, When obs expi con con2, [])
```
       
We look next at an example of Marlowe in action.

## Where to go to find out more 
- blah

### [Prev](./embedded-marlowe.md) [Up](./Tutorials.md) [Next]()