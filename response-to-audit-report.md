
# DRAFT Response to Audit Report

TODO:

- [ ] Add prefatory text and executive summary.
- [ ] Add responses and mitigation commits to Isabelle-related findings.
- [x] Add responses and mitigation commits to Haskell-related findings.
- [ ] Fix display of equations or replace ones that cannot be fixed with ellipses ("...").
- [ ] Replace broken links and cross references, or use elipses ("...").
- [ ] Verify the section numbering is correct.
- [ ] Add table of contents.
- [ ] Proofread.


## Executive Summary

TODO: @bwbush will add text here after everything else is written.


## Acknowledgement

TODO: @bwbush will add text thanking the audit team.


## Overview of Isabelle Changes


## Overview of Changes to Marlowe-Cardano Specification and Haskell (Plutus) Implementation

The audit report's main and high-severity concerns for the Plutus validators for Marlowe on Cardano fell into to four clusters:

1. Incorrect handling of negative deposits
    - "2.1.1 Negative deposits allow stealing funds"
2. Incomplete prevention of double satisfaction
    - "2.1.2 Contracts vulnerable to double satisfaction attacks"
3. Lax enforcement of invariants in Marlowe state
    - "2.1.7 Positive balances are not checked for the output state"
    - "2.1.8 Non-validated Marlowe states"
    - "2.1.9 Total balance of ending state uncomputed"
    - "2.1.10 Unchecked ending balance"
4. Difference semantics of association lists in Isabelle and Plutus
    - "2.1.12 Different insertion functions used in Isabelle and Haskell code"

Incorrect handling of negative deposits (item 1 above) was mitigated by the addition of a guard against this in Marlowe's Plutus validator so that its behavior was consistent with Marlowe semantics. Property-based tests were also added to check the correctness of the mitigation.

Although the Marlowe validator had prevented double-satisfaction among multiple copies of the Marlowe validator script running in the same transaction, it did not prevent double-satisfaction in cases where the Marlowe validator run alongside another Plutus validator in the same transaction (item 2 above). Double satisfaction has now been prevented by enforcing that the Marlowe validator is the only Plutus script that runs in transactions that make payments to parties. This allows Marlowe contracts to coordinate with other Plutus scripts, but only under conditions where double satisfaction is impossible. Once again, property-based tests were added to check the correctness of this mitigation.

The Marlowe validator had made optimistic assumptions about its own correct operation and hence did not check certain invariants in order to save on Plutus execution costs (item 3 above). The Marlowe semantics validator has now been thoroughly hardened against corruption of initial or final state so that it ensures that the three state-invariants of positive accounts, non-duplication of state entries (accounts, choices, and bound values), and a total internal value matching the script UTxO's value. This hardening was completed without unduly increasing the size (in bytes) of the validator or its Plutus execution cost: such was verified with simulated and on-chain measurement of execution costs for a library of real-life Marlowe contracts. Notably, the enforcement of the final invariants protects against funds becoming permanently locked in a Marlowe contract due to a garbled state: even in cases where the implementation of Marlowe semantics or parts of the Plutus validator are flawed, at least some of the execution paths of a Marlowe contract remain viable, so funds could be released even under nominally impossible but catastrophic difficulties. The property-based test suite was significantly enhanced to 

Mitigation of the difference between association lists (item 4 above) in Isabelle (`MList`) and Plutus (`AssocMap`) was handled by the aforementioned enforcement of invariants, by line-by-line code inspection and annotation, and by thoroughly enhanced property-based testing. Work is in progress on a formal proof of the equivalence of `MList` and `AssocMap` under pre-conditions that hold within Marlowe semantics. Note that porting Isabelle's `MList` implementation to Plutus would have enlarged the Marlowe semantics validator by at least 2000 bytes and rendered it too costly to execute within the Cardano ledger's present execution-cost limits.

The audit report for Marlowe on Cardano was based on the commit hash [523f3d56](https://github.com/input-output-hk/marlowe-cardano/commit/523f3d56f22bf992ddb0b0c8a52bb7a5a188f9e9). The revisions and mitigations discussed here apply to [69468d66](https://github.com/input-output-hk/marlowe-cardano/commit/69468d6623e24a4ccd6659e378ae012c38ca01ce) of that repository. The appendices to this report list the differences between pre- and post-audit specification and validator code for Marlowe on Cardano.

The medium-severity concerns in the audit report center around missing tests or name shadowing. With the exception of "2.7.1 More precise failure checks", these have all been remedied either by code changes (in the case of the shadowing) or by the addition of a significant augmentation of the property-based test suite. The audit's low-severity concerns generally relate to insufficiently detailed text in the Marlowe Cardano specification, the need for more elaborate comments in the code, naming of variable bindings, or typographical errors. Nearly all of these finds have been addressed, with only the exception of a few cosmetic recommendations that were not adopted.


# 2 Responses to Specific Findings


## 2.1 Main concerns


### 2.1.1 Negative deposits allow stealing funds *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Constraint 6`**
>
> The income from deposits is computed by adding up the deposit inputs, regardless of whether they are negative, while the semantics considers them as zero deposits. Combined with the absence of a balance check on the ending Marlowe state, this allows the ending balance to differ from the value paid to the Marlowe validator.
> 
> This disagreement can be exploited to steal money from a flawed Marlowe contract that allows a negative deposit. The issue is demonstrated in […].

This vulnerability was mitigated in commit [68791fac](https://github.com/input-output-hk/marlowe-cardano/commit/68791facc195068717cbc6e55d1e4fdbe1f4a521) by adding a guard against negative deposits in the Marlowe semantics validator. That guard ensures that the validator's semantics for negative deposits matches Marlowe's Isabelle semantics: namely a deposit of a negative quantity is treated as a deposit of zero. Thus a negative deposit will not decrement any of the account balances in the Plutus datum and the total of the internal balances will match the value held in the UTxO output to the Marlowe semantics script address.

A new golden test for negative deposits was added in commit [bbb9b8fc](https://github.com/input-output-hk/marlowe-cardano/commit/bbb9b8fc21ad93b7bcdb3b60be0f2f9c921f6bec) and property-based tests for negative deposits were added in commits [bbb9b8fc](https://github.com/input-output-hk/marlowe-cardano/commit/bbb9b8fc21ad93b7bcdb3b60be0f2f9c921f6bec), [9d5443c5](https://github.com/input-output-hk/marlowe-cardano/commit/9d5443c5e9306eaf49ac5389df455e07555c9e04), [4b81ee96](https://github.com/input-output-hk/marlowe-cardano/commit/4b81ee96b1e7c74c4964cf25f6bb599c80d07a52), and [15446073](https://github.com/input-output-hk/marlowe-cardano/commit/15446073131c4098fed781cdcc701b89b77f6bd0).


### 2.1.2 Contracts vulnerable to double satisfaction attacks *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Constraint 15`**
> 
> No datum is required for outputs fulfilling payments to addresses generated by the evaluation of a Marlowe contract. This implies that these outputs are vulnerable to double satisfaction in transactions involving other contracts that pay to the same wallets. An example is discussed in […].
> 
> One way to strengthen the implementation is for the Marlowe validator to demand that outputs paid to addresses contain a datum that identifies the contract instance, like the `TxOutRef` of the validator UTxO being spent. Then cooperation with other contracts is possible without double satisfaction if the validators of the other contracts demand a different datum for their outputs.

The Marlowe semantics validator had prevented a limited form of double-satisfaction attack by preventing two Marlowe validators to execute in the same transaction. The audit report correctly highlights that such an attack could be feasible in cases where another Plutus validator (not the same version of the Marlowe semantics validator) executes in a transactions where a payment to an address or to the Marlowe role-payout validator satisfies both the Marlowe semantics validator and the other validator.

Although the audit report's suggestion of including a unique datum (such as that identifying the contract instance) in any output payment from the contract would likely prevent double satisfaction, implementing such a change in the Marlowe validators would have entailed such extensive changes to the specification and implementation that the overall applicability of the audit findings might subsequently be called into question. Instead, a minimal change to the specification and implementation mitigates this vulnerability: the specification was amended with a "Constraint 20. Single satisfaction" that requires the Marlowe semantics validator be the only Plutus script running in the transaction *if payments to parties are being made in the transaction*. Thus, only allowing one script to validate in case of external payments completely eliminates the possibility that one payment would satisfy two scripts. Other contracts are permitted to cooperate with Marlowe in cases such as deposits, choices, and notifications where Marlowe is not making payments.

Commits [4adf115d](https://github.com/input-output-hk/marlowe-cardano/commit/4adf115dbf795e4b014eb6ccab0acb20a73e74ed) and [5f673c47](https://github.com/input-output-hk/marlowe-cardano/commit/5f673c477ccc9b38626dca505a399962b22c2675) augment the Marlowe-Cardano specification and the implementation of the Marlowe semantics validator. Commits [3f222bc3](https://github.com/input-output-hk/marlowe-cardano/commit/3f222bc363fcf3e9cd2fa0cb5206933ef597a619), [6f6331b4](https://github.com/input-output-hk/marlowe-cardano/commit/6f6331b463e7f2fddce7ec0f64b37b030f2f795b), [39fcc8aa](https://github.com/input-output-hk/marlowe-cardano/commit/39fcc8aa9d61ed97dfa56e7ce078bf5e4c4cd6cc), [435ac680](https://github.com/input-output-hk/marlowe-cardano/commit/435ac680eb8119db1c43ec968cf8ea4ef08158b6), and [9f4fc9cd](https://github.com/input-output-hk/marlowe-cardano/commit/9f4fc9cde581b6dbbb939ec9d8e6303b8b67350e) implement property-based tests for the new single-satisfaction constraint.


### 2.1.3 Missing constructor in equality instance *(Severity: High)*

> **File `Semantics.hs`, Class instance `Eq ReduceWarning`, line *845***
> 
> The constructor `ReduceAssertionFailed` is not mentioned and compares `False` against itself. This might cause validators to fail checking the presence of this particular warning.

Although this `Eq` instance is not used by the Marlowe validators (so it does not have implications for validator security), the equality test has been fixed because it is a liability for off-chain code and for potential future versions of validators that might perform such an equality test. Commit [84d65a70](https://github.com/input-output-hk/marlowe-cardano/commit/84d65a70c29320fab501ad759bbc71855d1b63fc) fixes this and commit [04805a39](https://github.com/input-output-hk/marlowe-cardano/commit/04805a393c0815fe0f2a1a6d7f76d9867ffe0c14) hardens all of the other `Eq` instances to prevent similar problems re-arising if sum types are augmented in the future.


### 2.1.4 Inaccurate formulation of Money preservation *(Severity: High)*

> **File `specification-v3-rc1.pdf`, Section `3.1 Money preservation`, page *29***
> 
> As the property stands, it is permitted to make deposits in one currency and return payments in a different currency. As long as the sums of the amounts match, the equality is satisfied. Yet it is unlikely that the participants of the contract would agree that money has been preserved.
> 
> Money preservation is a property stated with an equality. The left hand side is the sum of the deposits done by a list of transactions. The right hand side of the equality is the sum of all the payments done in the same list of transactions. Each sum, in turn, is represented as a single integer which aggregates the amounts of the various payments and deposits, irrespective of what currencies correspond to these amounts.


### 2.1.5 Insufficient documentation of Money preservation *(Severity: Medium)*

> **File `specification-v3-rc1.pdf`, Section `3.1 Money preservation`, page *29***
> 
> Money preservation is formulated in terms of functions that are not discussed in the specification. It is necessary to explain the meaning of these functions in sufficient detail so readers can understand the property.


### 2.1.6 Missing description of Merkleization *(Severity: High)*

> **File `specification-v3-rc1.pdf`, `Merkleization`**
> 
> There is no property about merkleization, but merkleization is implemented in the Cardano integration.
> 
> Some relevant properties could be:
> 
> 1.  The merkleized contract produces the same payments as the analogous regular contract.
> 2.  If a merkleized case input is applied successfully, it implies that the contract hash in the input corresponds to the continuation of the contract.
> 3.  Merkleizing and unmerkleizing a contract gives back the original contract.


### 2.1.7 Positive balances are not checked for the output state *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Constraint 13`** 
> 
> *Positive balances* are only checked for the input, not for the output Marlowe state. If the semantics are flawed, a transaction can produce an unspendable output that does not satisfy this constraint.
> 
> If such a transaction is accepted, no further evaluation will be possible since all subsequent transactions will be rejected due to the very same Constraint 13. This is an hypothetical attack vector, where a malicious actor could send a transaction to block a contract.

The Plutus code for the Marlowe semantics validator had been implemented with the optimistic assumption that semantics would not be flawed and that the additional execution cost of checking the output state was not warranted. However, as the audit report points out, such a flaw would result in the contract being forever blocked from further execution. Adding a check on the final output's validity would prevent a contract from ever reaching a fully blocked state. Even if the semantics or Plutus code were flawed, at least some execution paths in the contract would remain viable, so that the contract could eventually terminate and would not permanently lock funds.

Commits [0a890845](https://github.com/input-output-hk/marlowe-cardano/commit/0a890845c44ccfe4df97e765e9b9eb743ce7d580), [8855feae](https://github.com/input-output-hk/marlowe-cardano/commit/8855feae473882b82643db792327423152e45b5c), [26f024e8](https://github.com/input-output-hk/marlowe-cardano/commit/26f024e80cea0dd4ebf8bff0f1a10b97aea87894), and [201c5df9](https://github.com/input-output-hk/marlowe-cardano/commit/201c5df9de29b3b142be5ff7d0a9b56d1b378204) augment the Marlowe Cardano specification to require positive balances upon output and implements the corresponding check in the Marlowe Semantics validator.  Commit [d514bcd0](https://github.com/input-output-hk/marlowe-cardano/commit/d514bcd075732b07e1c6a73e2e3c68afa01acf2c), [7f562545](https://github.com/input-output-hk/marlowe-cardano/commit/7f562545d013dd17472b692b550ffdc7f8a383f3), and [ebab31d9](https://github.com/input-output-hk/marlowe-cardano/commit/ebab31d9ba6dd322d374b34cad3995050a0e476e) adds a property-based test for this.


### 2.1.8 Non-validated Marlowe states *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Missing constraint`** 
> 
> The validator is not specified to check that the Marlowe states in the input and output datums are valid. This condition is necessary for the lemmas about the Marlowe semantics to be applicable. The Marlowe state could become invalid if there is a flaw in the implementation of the semantics.
> 
> It also could be possible for the Marlowe state to be invalid if someone pays an output to the Marlowe validator with an invalid Marlowe state. Though this problem could be addressed with off-chain checks that prevent sending transactions that spend outputs with invalid Marlowe states. If off-chain checks are used, a note in the specification about how this is handled would be helpful.
> 
> An example showing betrayed user expectations is discussed in […].
> 
> For a valid Marlowe state, the association lists for bound values, accounts, and choices have keys sorted and without duplicates.

Prompted on this finding in the audit report, the Marlowe semantics validator has been altered to enforce all invariants (positive accounts; non-duplication of accounts, choices, and bound values; a total internal account balance that exactly matches the value in the script's UTxO) on both the initial and final states. This prevents execution of a Marlowe contract that was inadvertently or purposefully created by off-chain code with an invalid initial state. It also prevents transactions that corrupt the final state; such corruption could only happen if there were a flaw in the Plutus validator or Marlowe semantics implementation, in which case that execution-path of the contract would be blocked. The [Marlowe Best Practices Guide](https://github.com/input-output-hk/marlowe-cardano/blob/main/marlowe/best-practices.md) and [Marlowe Security Guide](https://github.com/input-output-hk/marlowe-cardano/blob/main/marlowe/security.md) warn of the importance of off-chain code creating valid initial state for Marlowe contracts.

Commits [0a890845](https://github.com/input-output-hk/marlowe-cardano/commit/0a890845c44ccfe4df97e765e9b9eb743ce7d580), [8855feae](https://github.com/input-output-hk/marlowe-cardano/commit/8855feae473882b82643db792327423152e45b5c), [26f024e8](https://github.com/input-output-hk/marlowe-cardano/commit/26f024e80cea0dd4ebf8bff0f1a10b97aea87894), and [201c5df9](https://github.com/input-output-hk/marlowe-cardano/commit/201c5df9de29b3b142be5ff7d0a9b56d1b378204) enforce that both the initial and final states in the respective incoming and outgoing datum obey the aforementioned three invariants of total value, non-duplication, and positivity. That commit also adds "Constraint 19. No duplicates" to the Marlowe Cardano specification. Property-based tests in commit [d514bcd0](https://github.com/input-output-hk/marlowe-cardano/commit/d514bcd075732b07e1c6a73e2e3c68afa01acf2c), [7f562545](https://github.com/input-output-hk/marlowe-cardano/commit/7f562545d013dd17472b692b550ffdc7f8a383f3), and [ebab31d9](https://github.com/input-output-hk/marlowe-cardano/commit/ebab31d9ba6dd322d374b34cad3995050a0e476e) check the implementation.


### 2.1.9 Total balance of ending state uncomputed *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Constraint 6`** 
> 
> The constraint says
> 
> > The beginning balance plus the deposits equals the ending balance plus the payments.
> 
> However, the Marlowe validator never computes the total balance of the accounts in the ending Marlowe state. Instead, the ending balance is assumed to be whatever value is paid by the transaction to the Marlowe validator. The natural language should describe precisely what is being checked.

The mitigation of the previous audit-report finding ("2.1.8 Non-validated Marlowe states") also mitigates this finding: in the validator, `checkOwnOutputConstraint marloweData finalBalance` ensures that the computed final balance of accounts matches the value output to the script's UTxO and `checkState "o" finalBalance txOutState` ensures that it matches the sum of value in the internal accounts.

Again as previously, the relevant commits are [0a890845](https://github.com/input-output-hk/marlowe-cardano/commit/0a890845c44ccfe4df97e765e9b9eb743ce7d580), [8855feae](https://github.com/input-output-hk/marlowe-cardano/commit/8855feae473882b82643db792327423152e45b5c), [26f024e8](https://github.com/input-output-hk/marlowe-cardano/commit/26f024e80cea0dd4ebf8bff0f1a10b97aea87894), and [201c5df9](https://github.com/input-output-hk/marlowe-cardano/commit/201c5df9de29b3b142be5ff7d0a9b56d1b378204) for specification and implementation and [d514bcd0](https://github.com/input-output-hk/marlowe-cardano/commit/d514bcd075732b07e1c6a73e2e3c68afa01acf2c), [7f562545](https://github.com/input-output-hk/marlowe-cardano/commit/7f562545d013dd17472b692b550ffdc7f8a383f3), and [ebab31d9](https://github.com/input-output-hk/marlowe-cardano/commit/ebab31d9ba6dd322d374b34cad3995050a0e476e) for property-based tests.


### 2.1.10 Unchecked ending balance *(Severity: High)*

> **File `marlowe-cardano-specification.md`, `Constraint 5`** 
> 
> The balance of the starting Marlowe state is checked to match the value in the input. However, the validator does not check that the ending balance matches the value in the output paid to the Marlowe validator. Similarly to Issue […], if there are flaws in the semantics that cause the ending balance to differ from the actual value paid to the validator, this constraint would prevent any transaction from spending the output.
> 
> The specification should at least discuss why the check is absent together with the other similar checks that are not implemented (checking that ending accounts have positive balances, checking that the ending Marlowe state is valid).

As the audit report recognizes, this concern is closely related to the three previous concerns. The revised validator's enforcement that of the three invariants for the final state ensures that the ending balance of the internal accounts in the state matches the actual output paid to the script.

Again as previously, the relevant commits are [0a890845](https://github.com/input-output-hk/marlowe-cardano/commit/0a890845c44ccfe4df97e765e9b9eb743ce7d580), [8855feae](https://github.com/input-output-hk/marlowe-cardano/commit/8855feae473882b82643db792327423152e45b5c), [26f024e8](https://github.com/input-output-hk/marlowe-cardano/commit/26f024e80cea0dd4ebf8bff0f1a10b97aea87894), and [201c5df9](https://github.com/input-output-hk/marlowe-cardano/commit/201c5df9de29b3b142be5ff7d0a9b56d1b378204) for specification and implementation and [d514bcd0](https://github.com/input-output-hk/marlowe-cardano/commit/d514bcd075732b07e1c6a73e2e3c68afa01acf2c), [7f562545](https://github.com/input-output-hk/marlowe-cardano/commit/7f562545d013dd17472b692b550ffdc7f8a383f3), and [ebab31d9](https://github.com/input-output-hk/marlowe-cardano/commit/ebab31d9ba6dd322d374b34cad3995050a0e476e) for property-based tests.


### 2.1.11 Partial functions used outside their domain *(Severity: Medium)*

> **File `MoneyPreservation.thy`, various functions ``**
> 
> `moneyInRefundOneResult`, `moneyInApplyResult`, `moneyInApplyAllResult`, `moneyInTransactionOutput`, and `moneyInPlayTraceResult` have strange meanings when the result is an error. Arguably, on error there is no money to retrieve, so the return type should be `(Token \times int) option` instead.
> 
> Some lemmas rely on this behavior to have equalities hold even in cases of errors, but the cost is that the meaning is so surprising that the reader may be confused by it. It would be more reliable to have explicit and weaker lemmas that assert equalities only when there are no errors.


### 2.1.12 Different insertion functions used in Isabelle and Haskell code *(Severity: High)*

> **File `Semantics.hs`, Several functions ``** 
> 
> Where `MList.insert` is used in the Isabelle semantics, [AssocMap.insert](https://github.com/input-output-hk/plutus/blob/v1.0.0/plutus-tx/src/PlutusTx/AssocMap.hs#L147-L148) is used in the Cardano implementation. However, the functions are not equivalent as demonstrated by the following examples:
> 
> ``` text
> AssocMap.insert 'a' 1 [('b', 0)] == [('b', 0), ('a', 1)]
> -- whereas
> MList.insert 'a' 1 [('b', 0)] == [('a', 1), ('b', 0)]
> ```
> 
> ``` text
> AssocMap.insert 'b' 1 [('a', 0), (‘b’, 0), (‘b’, 0)] == [('a', 0), ('b', 1), (‘b’, 1)]
> -- whereas
> MList.insert 'b' 1 [(‘a’, 0), ('b', 0), ('b', 0)] == [('a', 0), ('b', 1), ('b', 0)]
> ```
> 
> This renders the Isabelle lemmas inapplicable for the Cardano integration. The lemmas need to demand some properties of an `insert` function without fully spelling it out, or the Cardano integration needs to use `MList.insert` instead of `AssocMap.insert`.
> 
> Similarly, functions `AssocMap.delete` and `MList.delete` differ in behavior when the input map is not sorted:
> 
> ``` text
> AssocMap.delete 'a' [(‘b’, 0), (‘a’, 0)] == [('b', 0)]
> -- whereas
> MList.delete 'a' [(‘b’, 0), ('a', 0)] == [('b', 0), ('a', 0)]
> ```
> 
> Functions `AssocMap.lookup` and `MList.lookup` also differ in behavior when the input map is not sorted:
> 
> ``` text
> AssocMap.lookup 'a' [(‘b’, 0), (‘a’, 0)] == Just 0
> -- whereas
> MList.lookup 'a' [(‘b’, 0), ('a', 0)] == Nothing
> ```
> 
> The following usage places were found:
> -   Line 395, `evalValue` depends on `moneyInAccount` which depends on `AssocMap.lookup`.
> -   Line 413, `evalValue` depends on `AssocMap.lookup`.
> -   Line 428, `evalObservation` depends on `AssocMap.member`.
> -   Line 456, function `updateMoneyInAccount` relies on `AssocMap.delete` and `AssocMap.insert`.
> -   Line 482, function `reduceContractStep` relies on `AssocMap.insert`.
> -   Line 567, function `applyAction` relies on `AssocMap.insert`.

The porting of `MList` from Isabelle to Plutus would have increased the size and execution cost of the Marlowe semantics validator beyond the present limits of the Cardano ledger. Work is underway to modify the Isabelle semantics and proofs to use a data structure similar to Plutus's `AssocMap`. Instead of modifying the Marlowe semantics validator, all usages of `AssocMap` were manually reviewed to verify that no vulnerability was introduced by its use (as compared to `MList`) *provided that the precondition of no duplicate entries in the `AssocMap` held*: the source code was annotated with informal reasoning documenting the safety of `AssocMap`'s use. That manual review was augmented by a comprehensive set of property-based tests to check the behavior of `MList` (under the precondition that it was ordered and contained no duplicates) against `AssocMap` (under the precondition that it contained not duplicates) for all functions used in Marlowe semantics or in the Marlowe validator.

Commit [a2ff6aa3](https://github.com/input-output-hk/marlowe-cardano/commit/a2ff6aa334efb7b7955408d29cf0e2edf06bca08) annotates the Marlowe semantics validator with reasoning as to the safe use of `AssocMap`. Commits [af380a29](https://github.com/input-output-hk/marlowe-cardano/commit/af380a292c0369bcc77d8584d81ea80a31326b61), [e2277677](https://github.com/input-output-hk/marlowe-cardano/commit/e2277677987f359dcd8754275eccd5b7c9a880a7), [a95a616a](https://github.com/input-output-hk/marlowe-cardano/commit/a95a616aca59bc7159d3ffa92487f8f021820bff), [b65ccfec](https://github.com/input-output-hk/marlowe-cardano/commit/b65ccfec3708484ff52514671e0e227c13f084f3), and [9e068b6a](https://github.com/input-output-hk/marlowe-cardano/commit/9e068b6a60103f2a40604a7eaea57c5f29b59180) implement the property-based tests for the behavior of the Plutus `AssocMap` against the Isabelle `MList`.


### 2.1.13 Missing specification tests *(Severity: Medium)*

> **File `Spec/Marlowe/Semantics/Compute.hs`, ``** 
> 
> There are no tests for the properties in Section 3 of `specification-v3-rc1.pdf`. Besides checking that there are no translation mistakes, these properties would also help contrasting the assumptions in the Isabelle and the Haskell sides, like the meaning of validity of an association list, which is focused in the previous issue.

Subsequent to the commencement of the audit, a "test oracle" was developed that checks implementations of Marlowe semantics (such as the Plutus validator) against a reference implementation generated directly from the Isabelle specification. That generated Haskell implementation is backed by Isabelle proofs of the correctness of Haskell code generation by Isabelle. The test oracle is now applied to the Marlowe semantics implementation in Plutus that the validator use. The test oracle uses the refference implementation to generates test cases to challenge the Plutus implementation and then it checks the Plutus results against its own. This oracle provides sufficient coverage to address the audit-reports concerns regarding the lack of property-based tests for Section 3 of the Marlowe specification.


## 2.2 Marlowe specification


### 2.2.1 Lack of explanation regarding changing choices *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.1.4 Choices`, page *10***
> 
> Choices can only be changed when evaluating `When` statements. This is something only evident after looking at the implementation of `computeTransaction`. It needs to be discussed when first introducing choices and the `When` contract.


### 2.2.2 Undefined reference *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.1.7 Contracts`, page *13***
> 
> There is an undefined reference.


### 2.2.3 Lack of explanation for necessity of `Environment` type *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.1.8 State and Environment`, page *14***
> 
> An `Environment` type is introduced, but it is unclear why it is needed as it is defined as a synonym for time intervals.


### 2.2.4 Unclear meaning of execution environment *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.1.8 State and Environment`, page *14***
> 
> The meaning of the execution environment of the transaction is unclear. This is due to the concept of *transaction* being assumed by the specification and never formally introduced.
> 
> The specification reads
> 
> > The execution environment of a Marlowe contract simply consists of the (inclusive) time interval within which the transaction is occurring.
> 
> One has to infer that evaluating a Marlowe contract is undefined if it does not happen within a transaction, as otherwise the description of the execution environment would not make sense. It would be necessary to establish more explicitly the relationship between the contract evaluation and the notion of transaction.


### 2.2.5 Unexplained interval data types *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.1.8 State and Environment`, page *14***
> 
> The meaning of the data types `IntervalError` and `IntervalResult` needs to be explained.


### 2.2.6 Incomplete explanation for `TransactionOutput` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.1 Compute Transaction`, page *15***
> 
> The meaning of the data type `TransactionOutput` needs to be explained. More generally, the meaning of the return types of most functions has to be explained. Currently, the meaning can only be inferred from looking at how the types are used, which makes it harder to identify if they are used as intended.
> 
> The purpose of these types needs to be made explicit so it can be checked if the code is doing what is intended.


### 2.2.7 Code snippets switch languages *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.1 Compute Transaction`, page *15***
> 
> The specification changes from using Isabelle to using Haskell henceforth. Making the reader aware of the criteria for the language change would help maintaining the document.


### 2.2.8 Repeated definition of `IntervalResult` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Sections `2.1.8 State and Environment, 2.2.2 Fix Interval`, pages *14, 16***
> 
> The `IntervalResult` type is defined twice in the specification. One should be removed.


### 2.2.9 Poorly named variable `newAccount` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.6 Reduce Contract Step`, page *19***
> 
> In the implementation of the function `reduceContractStep`, the variable `newAccount` should be named `newAccounts`.


### 2.2.10 Poorly named variable `acc` in specification *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.8 Apply Cases`, page *22***
> 
> On the last equation of `applyCases`, `acc` should be named `input`.


### 2.2.11 Inaccurate specification of `giveMoney` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.9 Utilities`, page *22***
> 
> It says
> 
> > The *giveMoney* function transfers funds internally between accounts.
> 
> which is not accurate. It should say instead
> 
> > The *giveMoney* function deposits funds to an internal account.
> 
> This function is confusing in that it takes the account identifier of the paying account which is not used for anything other than filling a field in the returned value.


### 2.2.12 Redundant evaluation in `addMoneyToAccount` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.9 Utilities`, page *22***
> 
> `addMoneyToAccount` is redundantly evaluating `money <= 0` when invoking `updateMoneyInAccount`. The else branch could be replaced instead with `insert (accId, token) money accountsV`.


### 2.2.13 Redundant statement regarding addition *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, page *24***
> 
> It says that addition is associative and commutative. This is true but it is already implied by the equation preceding the statement. Maybe change to
> 
> > Note that addition is associative and commutative.
> 
> or remove the redundant statement.


### 2.2.14 Missing implementation for negation case of `evalValue` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, page *24***
> 
> Negation for `evalValue` does not show the implementation, just one lemma about `NegValue`, which is inconsistent with how other operations are presented.


### 2.2.15 Missing parentheses in `div` specification *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, page *25***
> 
> On page 25 formula $$c \neq 0 \Rightarrow c \mathbin{∗} a \mathbin{\mathrm{div}} (c \mathbin{∗} b) = a \mathbin{\mathrm{div}} b$$ needs additional parentheses around the term $c \mathbin{∗} a$, otherwise it can be parsed as $$c \neq 0 \Rightarrow c \mathbin{∗} (a \mathbin{\mathrm{div}} (c \mathbin{∗} b)) = a \mathbin{\mathrm{div}} b$$ which does not hold (Counter-example: $c=2, a=3, b=2$). The lemma `divMultiply` in the file `Semantics.thy` does use extra parentheses around $c \mathbin{∗} a$.


### 2.2.16 Unclear division explanation *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, page *25***
> 
> It says
> 
> > Division is a special case because we only evaluate to natural numbers.
> 
> The meaning of this statement needs to be further explained, since the arguments of `DivValue` could evaluate to negative numbers.


### 2.2.17 Discrepancy with `evalValue` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, pages *23--26***
> 
> The order of some cases for `evalValue` is different in the specification text and in the actual Isabelle code, and several cases (for example, `NegValue`) are missing from the specification entirely.
> 
> Moreover, the definition of `evalValue` is juxtaposed with some lemmas about its behavior (for example, `AddValue` being associative and commutative), making it harder to match the specification text with the Isabelle code.


### 2.2.18 Missing `evalValue` lemmas in specification *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, pages *23--26***
> 
> Not all lemmas about `evalValue` are listed in the specification. The absent lemmas include `evalDoubleNegValue`, `evalMulValue`, `evalSubValue`, and all division lemmas.


### 2.2.19 Typo in **Use Value** case of `evalValue` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2.2.10 Evaluate Value`, page *26***
> 
> The **Use Value** case mentions `TimeIntervalEnd` instead of `UseValue`.


### 2.2.20 Unexplained parameters of `playTrace` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3 Marlowe Guarantees`, page *28***
> 
> The parameters of the function `playTrace` need to be explained.


### 2.2.21 Type parameter discrepancy in `playTrace` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3 Marlowe Guarantees`, page *28***
> 
> The first parameter of `playTrace` in the specification is `int`, while it is `POSIXTime` in the code. Even though the latter is an alias for the former, it is beneficial to use the `POSIXTime` name both for consistency and readability.


### 2.2.22 Money preservation on failing transactions not specified *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3.1 Money preservation`, page *29***
> 
> Money preservation is expressed with an equality. This equality, however, only ensures money preservation for those lists of transactions that produce no error. In other words, there is no guarantee that money will be preserved for those lists of transactions that fail.
> 
> This is not a concern in practice because the lists of transactions that fail to evaluate are not accepted in the blockchain. However, this should be made explicit in the explanation of the property.


### 2.2.23 Complicated definition of `allAccountsPositive` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3.3 Possitive Accounts`, page *30***
> 
> The definition of\ `allAccountsPositive` is complicated and can be refactored as `all ((_, money) -> money > 0)`.


### 2.2.24 Discrepancy with Isabelle code for `allAccountsPositive` *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Sections `3.3 Positive Accounts`, page *30***
> 
> The `allAccountsPositive` function is defined differently in the specification and in the Isabelle code, although both definitions show the same behavior. These definitions need to be consolidated.


### 2.2.25 Misleading or incorrect formula for contract not holding funds *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3.6.3 Contract Does Not Hold Funds After it Closes`, page *32***
> 
> The statement in natural language looks unconnected from the proposed formula. Otherwise, it is unclear how not holding funds forever is a consequence of producing no warnings.


### 2.2.26 Different format for lemma statement *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Sections `3.6.2 All Contracts Have a Maximum Time`, page *32***
> 
> The lemma is stated using the proof derivation tree format as opposed to the rest of the specification and the Isabelle code.


### 2.2.27 Function `isClosedAndEmpty` is unexplained *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `3.6.2 All Contracts Have a Maximum Time`, page *32***
> 
> The function `isClosedAndEmpty` needs to be explained.


### 2.2.28 Top-down definitions *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Section `2`** 
> 
> In Section 2, the order of definitions is reversed, and the reader is thus faced with functions which call other functions that have not been introduced yet, despite the claim in Section 1.3 that the definitions will be presented bottom-up.


### 2.2.29 No mention of Isabelle lemmas in specification *(Severity: Low)*

> **File `specification-v3-rc1.pdf`, Multiple sections ``** 
> 
> Generally, readability can be improved by mentioning the Isabelle lemma names alongside their statements. This way, it would be much easier to search for the actual Isabelle code and proofs matching the informal specification text, and compare the two.


## 2.3 Lemmas and proofs


### 2.3.1 Unnecessarily large proofs *(Severity: Medium)*

> **Several Isabelle files, several lemmas**
> 
> Some Isabelle proofs are written with long apply-scripts, where Isar would document the proof better. Proofs could also be split using more auxiliary lemmas.
> 
> As the proofs stand, it is hard to figure out why a proof step fails, after changes elsewhere required a proof to be updated. Since the newly-failing proof step was designed with specific goals in mind, and changes in the code may lead to it facing a different set of goals, the maintainer might need to reconstruct the whole structure of the proof from an older version to infer state that Isabelle produces at each step.
> 
> What Isar brings is making the intention of the author explicit at every step of the proof. This helps the maintainer of the proofs and fixes the concerns mentioned above.
> 
>  will likely have to update the proofs. We conjecture that it will happen at least every time they target a new platform. In the case of Cardano, they need to extend the semantics to explain Merkleization. Another action that would make long proofs easier to understand is to split them using more auxiliary lemmas, thus feeding the information to the reader in smaller chunks.
> 
> Some examples of large proofs:
> -   in `MoneyPreservation.thy`, lemmas `reduceContractStep_preserves_money` and\ `reductionLoop_preserves_money`
> -   in `SingleInputTransactions.thy`, lemmas `applyAllInputsPrefix_aux`,\ `computeTransactionIterative`, and `computeTransactionStepEquivalence_error`


### 2.3.2 Long lines in lemmas *(Severity: Low)*

> **Several Isabelle files, several lemmas**
> 
> Lines are sometimes long which makes it difficult to understand the lemmas. Lemmas need to be formulated expressing one hypothesis per line and the conclusion on a separate line. Complex hypotheses need to be indented using several lines to expose their structure.
> 
> Besides the effort of scrolling the text horizontally, the hypotheses are hard to separate visually, and so is the conclusion. Furthermore, when a hypothesis is a nested implication it is difficult to see where it ends without further indentation.
> 
> Some examples of lemmas with long lines or non-trivial hypothesis follow.
> -   in `CloseSafe.thy`, lemmas `closeIsSafe_reduceContractUntilQuiescent`, and `closeIsSafe_reductionLoop`
> -   in `MoneyPreservation.thy`, lemmas `reductionLoop_preserves_money_Payment_not_ReduceNoWarning`, `reductionLoop_preserves_money_Payment` and `reduceContractStep_preserves_money_acc_to_party`
> -   in `SingleInputTransactions.thy`, lemma `applyAllLoop_longer_doesnt_grow`
> -   in `TimeRange.thy`, lemmas `reduceStep_ifCaseLtCt` and `reduceLoop_ifCaseLtCt`
> -   in `ValidState.thy`, lemma `reductionLoop_preserves_valid_state_aux`


### 2.3.3 Confusing auxiliary lemmas *(Severity: Low)*

> **Several Isabelle files, several lemmas**
> 
> Some Isabelle proofs resort to declaring auxiliary lemmas with names suffixed with *\_aux*. Sometimes these lemmas are not expressed succinctly, and look more like a punctual copy of the state of some particular proof that is later developed. For the sake of maintaining the proofs, it would be necessary to structure them in a way that presents the information piecewise to the reader. More generally, even auxiliary lemmas should have a well-defined meaning.
> 
> We found this problem at least in the following:
> -   in `QuiescentResult.thy`, lemmas `reduceContractStepPayIsQuiescent`, `reductionLoopIsQuiescent_aux`, and `applyAllInputsLoopIsQuiescent_loop`
> -   in `PositiveAccounts.thy`, lemma `positiveMoneyInAccountOrNoAccountImpliesAllPositive_aux2`
> -   in `SingleInputTransactions.thy`, lemma `applyAllInputsPrefix_aux`


### 2.3.4 Undescriptive variable names *(Severity: Low)*

> **Several Isabelle files, several lemmas**
> 
> Many Isabelle proof statements and proofs use uninformative variable names. The most common example occurs with variables named $\mathit{x11}, \mathit{x12}$, etc. These inhibit the reader from easily understanding the lemma statements, and often require looking back at constructors to understand what these variables represent.
> 
> Some examples of lemmas with these uninformative variable names follow:
> -   in `QuiescentResult.thy`, lemma `reductionLoopIsQuiescent_aux`
> -   in `SingleInputTransactions.thy`, lemmas `beforeApplyAllLoopIsUseless` and\ `applyAllInputsPrefix_aux`
> -   in `ValidState.thy`, lemma `reductionLoop_preserves_valid_state_aux`
> -   in `TimeRange.thy`, lemmas `resultOfReduceIsCompatibleToo`, `resultOfReductionLoopIsCompatibleToo`, `resultOfReduceUntilQuiescentIsCompatibleToo`, `reduceLoop_ifCaseLtCt`, and\ `reduceContractUntilQuiescent_ifCaseLtCt`


### 2.3.5 Involved proof of `insert_valid` *(Severity: Low)*

> **File `MList.thy`, theorem `insert_valid`, line *66***
> 
> The proof of `insert_valid` sprouts three other lemmas of difficult characterization: `insert_valid_aux`, `insert_valid_aux2`, and `insert_valid_aux3`. These lemmas make assumptions with implications that get in the way of understanding them in isolation.
> 
> An alternative to make the proof pieces more reusable is to use instead the following set of lemmas, which also offers insight on how function `insert` interacts with predicates `sorted` and `distinct`:
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   lemma insert_set:
>     "set (map fst (insert a b xs)) = set (map fst xs) |$\cup$| { a }"
> 
>   lemma insert_sorted:
>     "List.sorted (map fst c) |$\Longrightarrow$| List.sorted (map fst (insert a b c))"
> 
>   lemma insert_distinct :
>     "List.distinct (map fst c)
>      |$\Longrightarrow$|
>      List.sorted (map fst c)
>      |$\Longrightarrow$|
>      List.distinct (map fst (MList.insert a b c))"
> ```
> 
> which then can be combined in the proof of `insert_valid` as follows:
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   theorem insert_valid2 : "valid_map c |$\Longrightarrow$| valid_map (MList.insert a b c)"
>     using insert_sorted[of c a b] insert_distinct[of c a b] by fastforce
> ```
> 
> The proofs of the lemmas can be found in […].


### 2.3.6 Repeated verbose expression *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `removeMoneyFromAccount_preservation`, line *202***
> 
> The expression
> 
> ``` text
>   giveMoney
>     accId
>     (Party p)
>     tok
>     paidMoney
>     (updateMoneyInAccount accId tok (balance - paidMoney) accs)
> ```
> 
> is large and used in other lemmas as well. It would need to be moved to a separate function to save the effort of reading it repeteadly.


### 2.3.7 Inconsistent variable name `valTrans` *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `transferMoneyBetweenAccounts_preserves_aux`, line *257***
> 
> The lemma uses a variable `valTrans` where other proofs use the name `paidMoney`. To convey the meaning of the variable faster, the same name should be used consistently in all places.


### 2.3.8 Unused binding `interAccs` *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `transferMoneyBetweenAccounts_preserves_aux`, line *263***
> 
> The binding `interAccs` was probably intended to be used on this line. It should either be used or removed from the premise.


### 2.3.9 Undescriptive variable name `acc` *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `transferMoneyBetweenAccounts_preserves`, line *295***
> 
> This lemma has a variable `acc` that is used together with `tok2`. It would be more descriptive to call it `accId2`.


### 2.3.10 Misleading indentation *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemmas `reductionLoop_preserves_money_NoPayment_not_ReduceNoWarning, reductionLoop_preserves_money_NoPayment`, lines *430, 439***
> 
> The indentation is misleading: the premises on these lines are indented as if they are a part of the previous functional premise.


### 2.3.11 Missing theorem regarding `playTrace` *(Severity: Low)*

> **File `PositiveAccounts.thy`, `playTrace preserves valid and positive state`** 
> 
> There is no theorem that `playTrace` keeps the state valid and positive when given a state which is valid and positive. This trivially follows from `playTraceAux_preserves_validAndPositive_state` but no such theorem is present.


### 2.3.12 Unconcise goal in `reduceContractStepPayIsQuiescent` *(Severity: Low)*

> **File `QuiescentResult.thy`, lemma `reduceContractStepPayIsQuiescent`, line *8***
> 
> This lemma does not express its goal concisely, as it makes no mention of `reduceContractStep` in the formulation. Changing the first assumption to $\texttt{reduceContractStep}\ \mathit{env}\ \mathit{sta}\ (\texttt{Pay}\ \mathit{x21}\ \mathit{x22}\ \mathit{tok}\ \mathit{x23}\ \mathit{x24})$ makes more explicit in which contexts this lemma can be useful. Modifying this assumption requires an additional `apply simp` to be added to the proof (before line 30) for the lemma to go through. Further, an additional `apply simp` will need to be added in lemmas `reduceContractStepIsQuiescent` (before line 44) and `timedOutReduce_only_quiescent_in_close` (`Timeout.thy`, before line 128) as well.


### 2.3.13 Misleading lemma names *(Severity: Low)*

> **File `PositiveAccounts.thy`, lemma `reduceOne_gtZero`, line *80***
> 
> This lemma should be renamed as `refundOne_gtZero`.
> 
> **File `QuiescentResult.thy`, lemma `reduceOneIsSomeIfNotEmptyAndPositive`, line *32***
> 
> This lemma should be renamed as `refundOneIsSomeIfNotEmptyAndPositive`.
> 
> **File `TransactionBound.thy`, lemma `computeTransaction_decreases_maxTransaction_aux`, line *240***
> 
> This lemma should be renamed as `applyAllInputs_decreases_maxTransactions` or `applyAllInputs_reduced_decreases_maxTransactions`.


### 2.3.14 Misleading variable name `reduced` *(Severity: Low)*

> **File `QuiescentResult.thy`, lemmas `reductionLoop_reduce_monotonic, reduceContractUntilQuiescent_ifDifferentReduced`, lines *138, 153***
> 
> The boolean variable name `reduce` would be better named `reduced` as it is signifying that the contract has been reduced.


### 2.3.15 Undescriptive name `beforeApplyAllLoopIsUseless` *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemma `beforeApplyAllLoopIsUseless`, line *270***
> 
> This lemma seems to say that `reduceContractUntilQuiescent` has no effect when composed with `applyAllLoop`, because `applyAllLoop` evaluates `reduceContractUntilQuiescent`, and `reduceContractUntilQuiescent` is idempotent.
> 
> A more descriptive name for this lemma could be `reduceContractUntilQuiescent_hasNoEffect_before_applyAllLoop`


### 2.3.16 Unused and undocumented lemmas *(Severity: Low)*

> **Several Isabelle files, several lemmas**
> 
> Some lemmas are never used, and they would need comments motivating their presence:
> 1.  In file `MoneyPreservation.thy`, line 257, lemma `transferMoneyBetweenAccounts_preserves_aux`.
> 2.  In file `QuiescentResult.thy`
>     1.  Line 5, lemma `reduceOne_onlyIfNonEmptyState`
>     2.  Line 153, lemma `reduceContractUntilQuiescent_ifDifferentReduced`
> 3.  In file `PositiveAccounts.thy`, line 66, lemma `positiveMoneyInAccountOrNoAccount_sublist_gtZero`. Furthermore, it is identical to `positiveMoneyInAccountOrNoAccount_gtZero_preservation`, but with an additional assumption `money > 0`.
> 4.  In file `ValidState.thy`
>     1.  Line 9, lemma `valid_state_valid_choices`
>     2.  Line 13, lemma `valid_state_valid_valueBounds`
> 5.  In file `SingleInputTransactions.thy`, line 1214, lemma `traceListToSingleInput_isSingleInput`. It is mentioned in a commented out line in `StaticAnalysis.thy`. Furthermore, the lemma can be expressed more concisely as $$\llparenthesis \mathit{interval} = \mathit{inte}, \mathit{inputs} = \mathit{inp\_h}\ \#\ \mathit{inp\_t} \rrparenthesis\ \#\ t = \mathit{traceListToSingleInput}\ \mathit{t2} % \mathrel{% \mbox{\fontfamily{cmr}\fontencoding{OT1}\selectfont=}}% \joinrel\Rightarrow\mathit{inp\_t} = []$$


### 2.3.17 Redundant `reduceContractStep` lemmas *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `reduceContractStep_preserves_money_acc_to_acc_aux`, line *310***
> 
> This lemma is weaker than `transferMoneyBetweenAccounts_preserves`. If we replace its usage at line 351 with `transferMoneyBetweenAccounts_preserves`, the proof goes through.


### 2.3.18 Redundant `transferMoneyBetweenAccounts_preserves` *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `reduceContractStep_preserves_money_acc_to_acc`, line *332***
> 
> This lemma is weaker than `transferMoneyBetweenAccounts_preserves`. We can replace its usage site in line 376
> 
> ``` text
>   using
>     reduceContractStep_preserves_money_acc_to_acc
>     validAndPositive_state.simps
>    by blast
> ```
> 
> with
> 
> ``` text
>   using transferMoneyBetweenAccounts_preserves validAndPositive_state.simps by auto
> ```


### 2.3.19 Duplicated lemmas *(Severity: Low)*

> **File `PositiveAccounts.thy`, theorems `computeTransaction_gtZero, accountsArePositive`, lines *257, 369***
> 
> These theorems are identical (modulo variable names), and one of them should be removed.
> 
> **File `PositiveAccounts.thy, ValidState.thy`, lemma `valid_state_valid_accounts`, lines *381, 5***
> 
> This lemma is defined twice, once in each of these files. One of them should be removed.


### 2.3.20 Redundant `computeTransaction` lemmas *(Severity: Low)*

> **File `ValidState.thy`, lemmas `computeTransaction_preserves_valid_state_aux, computeTransaction_preserve_valid_state`, lines *160, 176***
> 
> If `computeTransaction_preserves_valid_state_aux` is rewritten to have the same formulation as `computeTransaction_preserves_valid_state`, then the lemma (with the exact same proof) is still accepted, and these lemmas become duplicates of each other. Thus, no auxiliary lemma is needed.


### 2.3.21 Complicated formulation of `updateMoneyInAccount_money2_aux` *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `updateMoneyInAccount_money2_aux`, line *159***
> 
> `updateMoneyInAccount_money2_aux` could be expressed simpler by removing the hypothesis `moneyToPay >= 0`, leaving
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   valid_map (((thisAccId, tok), money) # tail) |$\Longrightarrow$|
>   allAccountsPositive (((thisAccId, tok), money) # tail) |$\Longrightarrow$|
>   moneyInAccount thisAccId tok (((thisAccId, tok), money) # tail) > 0"
> ```
> 
> The proof of `updateMoneyInAccount_money2` can then in turn be trivially adjusted so it still works, by changing the step cases
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   cases "moneyInAccount accId tok ((thisAccIdTok, money) # tail) + moneyToPay |$\leq$| 0"
> ```
> 
> to
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   cases "moneyInAccount accId tok ((thisAccIdTok, money) # tail) |$\leq$| 0"
> ```


### 2.3.22 Complicated proofs that can be simplified *(Severity: Low)*

> **File `MoneyPreservation.thy`, lemma `moneyInInput_is_positive`, line *53***
> 
> The proof could be more general with `apply (cases x; simp)` instead of using `metis`.
> 
> **File `MoneyPreservation.thy`, lemma `reductionLoop_preserves_money_NoPayment_not_ReduceNoWarning`, line *434***
> 
> This lemma can be proved directly with `metis reductionLoop_preserves_money_NoPayment`, and reversing the order in which the lemmas are defined.
> 
> **File `TimeRange.thy`, lemma `inIntervalIdempotentToIntersectInterval`, line *5***
> 
> The lemma can use a shorter proof: `apply (cases min2;cases max2;auto) done`.
> 
> **File `TimeRange.thy`, lemma `inIntervalIdempotency1, inIntervalIdempotency2`, lines *20, 36***
> 
> These lemmas use the `smt` tactic and `metis` where a simpler Isar proof would work, for example:
> 
> ``` text
>   lemma inIntervalIdempotency1 :
>     assumes "inInterval (x, y) (intersectInterval b c)"
>     shows "inInterval (x, y) b"
>   proof (cases b)
>     case [simp]:(Pair b1 b2)
>     thus ?thesis proof (cases c)
>       case (Pair c1 c2)
>       thus ?thesis using assms by (cases c1; cases c2; cases b1;cases b2; simp)
>     qed
>   qed
> ```
> 
> **File `SemanticsGuarantees.thy`, `Various lemmas/instantiations`**
> 
> Multiple lemmas and `linorder` instantiations in this file repeat auxiliary facts within the proof that are not necessary. For example, in the `linorder` instantiation for `Party`, lines 51--53 state
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   have "(x < y) = (x |$\le$| y |$\land$| |$\neg$| y |$\le$| (x :: Token))"
>     by (meson less_Tok.simps less_Token_def less_eq_Token_def linearToken)
>   thus "(x < y) = (x |$\le$| y |$\land$| |$\neg$| y |$\le$| x)" by simp
> ```
> 
> This can be rewritten to avoid repeating the fact as
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   show "(x < y) = (x |$\le$| y |$\land$| |$\neg$| y |$\le$| (x :: Token))"
>     by (meson less_Tok.simps less_Token_def less_eq_Token_def linearToken)
> ```
> 
> This pattern appears many times in this file. For example, in the `Party` instantation alone, it is present on lines 51 -- 53, 56 -- 57, 77 -- 80, and 83 -- 84.


### 2.3.23 Inconsistent style when applying constructor *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemmas `beforeApplyAllLoopIsUseless, fixIntervalOnlySummary`, lines *275, 398***
> 
> The lines mentioned in these lemmas display the resulting constructor before the function application, which differs from the general style in the rest of the codebase.


### 2.3.24 Unsimplified boolean formulas *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemma `computeTransactionIterative_aux2`, lines *708, 710***
> 
> In multiple places, this lemma formulation includes top-level negation in front of nontrivial conjunctions and disjunctions. These negations should be distributed. Otherwise, the reader is taxed with the chore to mentally distribute the negation to understand the lemma.


### 2.3.25 Typo with "independet" in multiple lemmas *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemmas `applyAllLoop_independet_of_acc_error1, applyAllLoop_independet_of_acc_error2`, lines *977, 987***
> 
> In both of these lemmas, there is a typo with the word "independet".


### 2.3.26 Poorly named `acc` lemmas *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemmas `applyAllLoop_independet_of_acc_error1, applyAllLoop_independet_of_acc_error2`, lines *977, 987***
> 
> It is unclear what `acc` refers to in these lemma names, as the lemmas are about the independence of warnings and payments, not accounts.


### 2.3.27 Verbose lemma statement `playTraceAuxIterative_base_case` *(Severity: Low)*

> **File `SingleInputTransactions.thy`, lemma `playTraceAuxIterative_base_case`, line *1063***
> 
> The statement of this lemma is very verbose. A more natural (and slightly stronger) formulation could be $$\begin{aligned} &\mathit{playTraceAux}\ \mathit{txOut}\ [\ \llparenthesis \mathit{interval} = \mathit{inte}, \mathit{inputs} = [h] \rrparenthesis, \llparenthesis \mathit{interval} = \mathit{inte}, \mathit{inputs} = t \rrparenthesis \ ] \\ =\ &\mathit{playTraceAux}\ \mathit{txOut}\ [\ \llparenthesis \mathit{interval} = \mathit{inte}, \mathit{inputs} = h\ \#\ t \rrparenthesis \ ]\end{aligned}$$


### 2.3.28 `playTrace_only_accepts_maxTransactionsInitialState` not written as `theorem` *(Severity: Low)*

> **File `TransactionBound.thy`, lemma `playTrace_only_accepts_maxTransactionsInitialState`, line *316***
> 
> This lemma seems like the main result of this file. Assuming it is an important result, we recommend writing it as a `theorem` rather than a `lemma`.


### 2.3.29 Inconsistent style with assumptions *(Severity: Low)*

> **File `Timeout.thy`, lemmas `timedOutReduceContractUntilQuiescent_closes_contract, timedOutReduceContractStep_empties_accounts`, lines *201/204, 211/214***
> 
> These lemmas use the hypothesis $\mathit{minTime}\ \mathit{sta} \leq \mathit{iniTime}$ and build a state $\mathit{sta}\ \llparenthesis \mathit{minTime} := \mathit{iniTime} \rrparenthesis)$ while other lemmas simply say $\mathit{minTime}\ \mathit{sta} = \mathit{iniTime}$. Readability would be improved by presenting these lemmas in the same style as the others, or documenting the need for these distinct presentations via code comments.


### 2.3.30 Function `validTimeInterval` unnecessarily unfolded in lemma *(Severity: Low)*

> **File `TimeRange.thy`, lemma `reduceStep_ifCaseLtCt_aux`, line *234***
> 
> For consistency, $a \leq b$ should be replaced by $\texttt{validTimeInterval}$.


### 2.3.31 Overly specific auxiliary lemma *(Severity: Low)*

> **File `ValidState.thy`, lemma `reductionLoop_preserves_valid_state_aux`, line *73***
> 
> This lemma on its own is very specific, and is only used in `reductionLoop_preserves_valid_state`. If possible, we recommend this lemma to be generalized or broken down into smaller lemmas, in order to present the arguments to the reader in smaller pieces.


### 2.3.32 `playTrace_preserves_valid_state` not written as `theorem` *(Severity: Low)*

> **File `ValidState.thy`, lemma `playTrace_preserves_valid_state`, line *194***
> 
> This lemma seems like the main result of this file. Assuming it is an important result, we recommend writing it as a `theorem` instead.


### 2.3.33 Unnecessary assumptions *(Severity: Low)*

> **File `PositiveAccounts.thy`, lemmas `addMoneyToAccountPositive_match, addMoneyToAccountPositive_noMatch`, lines *12, 23***
> 
> The assumptions $$\forall x\ \mathit{tok}.\ \mathit{positiveMoneyInAccountOrNoAccount}\ x\ \mathit{tok}\ \mathit{accs}$$ in `addMoneyToAccountPositive_match` and $$\mathit{money > 0}$$ in `addMoneyToAccountPositive_noMatch` are unnecessary.
> 
> **File `PositiveAccounts.thy`, lemma `reduceContractStep_gtZero_Refund`, line *93***
> 
> The lemma has an assumption that is mostly redundant.
> 
> ``` {.text escapeinside="||" mathescape="true"}
>   Reduced
>     ReduceNoWarning
>     (ReduceWithPayment (Payment party (Party party) tok2 money))
>     (state|$\llparenthesis$|accounts := newAccount|$\rrparenthesis$|) Close
>     =
>   Reduced wa eff newState newCont
> ```
> 
> A stronger lemma would be valid, which results from eliminating the assumption and changing the conclusion to `positiveMoneyInAccountOrNoAccount y tok3 newAccount`.
> 
> **File `QuiescentResult.thy`, lemma `reduceContractStepPayIsQuiescent`, line *17***
> 
> The assumption $\mathit{cont} = \texttt{Pay}\ \mathit{x21}\ \mathit{x22}\ \mathit{tok}\ \mathit{x23}\ \mathit{x24}$ is unnecessary.
> 
> **File `Timeout.thy`, lemma `timedOutReduce_only_quiescent_in_close_When`, line *43***
> 
> The assumption $\mathit{minTime}\ \mathit{sta} \leq \mathit{iniTime}$ is unnecessary.
> 
> **File `Timeout.thy`, lemma `timedOutReduce_only_quiescent_in_close`, line *122***
> 
> The assumption\ $\mathit{minTime}\ \mathit{sta} \leq \mathit{iniTime}$ is unnecessary. However, removing it will require the later proof `timedOutReduceContractLoop_closes_contract` to be adjusted.
> 
> **File `Timeout.thy`, lemma `timedOutReduceContractLoop_closes_contract`, lines *170, 173***
> 
> The assumptions $\mathit{minTime}\ \mathit{sta} \leq \mathit{iniTime}$ and $\mathit{minTime} \mathit{sta} = \mathit{iniTime}$ are both present. The former is redundant.
> 
> **File `TimeRange.thy`, lemma `reduceStep_ifCaseLtCt_aux`, line *234***
> 
> The assumption\ $\mathit{env} = \llparenthesis \mathit{timeInterval} = (a, b) \rrparenthesis$ is unnecessary.
> 
> **File `ValidState.thy`, lemma `reductionStep_preserves_valid_state_Refund`, line *29***
> 
> The assumption $$\begin{aligned} \mathit{newState} = \llparenthesis &\mathit{accounts} = \mathit{newAccounts}, \mathit{choices} = \mathit{newChoices}, \\ &\mathit{boundValues} = \mathit{newBoundValues}, \mathit{minTime} = \mathit{newMinTime} \rrparenthesis\end{aligned}$$ is unnecessary.


## 2.4 Isabelle implementation


### 2.4.1 Variable shadowing in `applyAllLoop` *(Severity: Medium)*

> **File `Semantics.thy`, function `applyAllLoop`, line *575***
> 
> The $\texttt{cont}$ variable introduced by the pattern match shadows another $\texttt{cont}$ variable, coming from the pattern match of an outer case expression, making the function harder to follow while also making it more error-prone to future changes.


### 2.4.2 Undescriptive name `moneyInPayment` *(Severity: Low)*

> **File `MoneyPreservation.thy`, function `moneyInPayment`, line *5***
> 
> The name of the function can be more precise. Perhaps `moneyInPaymentToParty` or `moneyInExternalPayment` would work.


### 2.4.3 Typo in section name *(Severity: Low)*

> **File `OptBoundTimeInterval.thy`, line `37`** 
> 
> Typo in section name: "Interval intesection".


### 2.4.4 Typo in comment *(Severity: Low)*

> **File `OptBoundTimeInterval.thy`, line `42`** 
> 
> Typo in comment: "endpoits".


### 2.4.5 Unclear need for multiple formulations for positive accounts *(Severity: Low)*

> **File `PositiveAccounts.thy`, `Throughout`** 
> 
> It is unclear what the use is for multiple formulations (and lemmas about) positive accounts. The first formulation (with the theorems `playTraceAux_gtZero` and `playTrace_gtZero`) is not used in any other modules but the alternative formulation is used instead. If both formulations are relevant, then it should be explained why.


### 2.4.6 Variable name discrepancy in `reductionLoop` *(Severity: Low)*

> **File `Semantics.thy`, function `reductionLoop`** 
> 
> When comparing this function against `specification-v3-rc1.pdf`, different names are used for a let-bound variable. It is `a` in the pdf and `newPayments` in the file `Semantics.thy`. There are similar issues in the function `reduceContractStep` in the equation for the `If` case, and in the function `giveMoney`.


### 2.4.7 Typo in constructor *(Severity: Low)*

> **File `Semantics.thy`, function `applyCases`, line *505***
> 
> Apparent typo in the error message constructor: the party mentioned should be $\texttt{party2}$.


### 2.4.8 Unclear function name `calculateNonAmbiguousInterval` *(Severity: Low)*

> **File `Semantics.thy`, function `calculateNonAmbiguousInterval`, line *725***
> 
> The meaning of the function is not obvious. It needs a comment to explain it.


### 2.4.9 Non-modularized file `SingleInputTransactions.thy` *(Severity: Low)*

> **File `SingleInputTransactions.thy`, `Splitting File`** 
> 
> This file is very long, and it covers more than just single-input transactions. For instance, about 530 lines at the beginning are rather dedicated to idempotence of certain operations. Then, the lemmas around lines 530 -- 700 focus on "well-foundedness" of the recursion on contract steps. Then there is also a clear block of lemmas about "distributivity" of semantics over transaction lists.
> 
> Splitting the module, grouping the related lemmas, would help understanding the relationships between the groups.


### 2.4.10 Misleading function names *(Severity: Low)*

> **File `SingleInputTransactions.thy`, function `inputsToTransactions`, line *9***
> 
> This function name is not very descriptive of its meaning. It takes a transaction (both a time interval and a list of inputs) and returns a list of transactions at the same interval containing a single input each. A name like `splitTransactionIntoSingleInputTransactions` would convey better what the input and the output are.
> 
> Moreover, the code would be cleaner if the function takes a single argument of type `Transaction`, instead of asking the caller to rip apart its fields.
> 
> **File `SingleInputTransactions.thy`, function `traceListToSingleInput`, line *18***
> 
> This function name is not descriptive of what it does. Perhaps a more telling name could be `splitTransactionsIntoSingleInputTransactions`.
> 
> **File `SingleInputTransactions.thy`, function `isSingleInput`, line *1222***
> 
> This function should be renamed or repurposed. If renamed, `allAreSingleInput` more accurately reflects the meaning of the function. If repurposed, it should check that a single transaction has a single input, and `all isSingleInput` can be used to express the current behavior.


### 2.4.11 Unused parameter in `maxTransactionCaseList` *(Severity: Low)*

> **File `TransactionBound.thy`, function `maxTransactionCaseList`, line *16***
> 
> This function has a parameter of type `State` that is completely unused and can be removed.


### 2.4.12 Duplicated `isValidInterval` function *(Severity: Low)*

> **File `TimeRange.thy`, function `isValidInterval`, line *231***
> 
> This function duplicates $\texttt{validTimeInterval}$ from $\texttt{OptBoundTimeInterval.thy}$, and the latter has certain additional properties proven about it specifically, so it makes sense to use the latter in both cases.


## 2.5 marlowe-cardano specification


### 2.5.1 Lack of guidelines for creating cooperating contracts *(Severity: Medium)*

> **File `marlowe-cardano-specification.md`, Section `Life Cycle of a Marlowe Contract`** 
> 
> Given that transactions are expected to work with Marlowe and non-Marlowe contracts simultaneously, it would be helpful to offer some guidelines for other contracts to avoid double satisfaction. Some degree of cooperation between the contracts that can appear in the same transaction is unavoidable.
> 
> One measure could be to ask every cooperating contract to refrain from paying to the payout validator. In this way, double satisfaction can not affect the payments of the Marlowe contract, if the Marlowe contract only pays to roles rather than addresses.
> 
> Another alternative would be to demand other contracts' outputs to use datums that are different from the roles used by the Marlowe contract for payments.

Commit [00010ea4](https://github.com/input-output-hk/marlowe-cardano/commit/00010ea48439892ff9eec54fb93929f56bcb6c7b) adds a paragraph of guidance to the Marlowe Cardano specification. The mitigation above for "2.1.2 Contracts vulnerable to double satisfaction attacks" implements validator changes to address this.


### 2.5.2 No reference to creating a minting policy *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Monetary Policy for Role Tokens`** 
> 
> The minting policy is not specified, but a reference needs to be offered to explain how to create one.

The monetary policy is not a concern of the Marlowe validator, but commit [fe00af7d](https://github.com/input-output-hk/marlowe-cardano/commit/fe00af7d622bbd17c3327363d4650ee544d1fff7) adds a sentance referencing the discussion of monetary policies for role tokens in the [Marlowe Best Practices Guide](https://github.com/input-output-hk/marlowe-cardano/blob/main/marlowe/best-practices.md).


### 2.5.3 Argument for Contract in `txInfoData` not specified *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Types`** 
> 
> The argument by which the `Contract` in the `txInfoData` list corresponds to the given hash needs to be made explicit.

Commit [b6366efc](https://github.com/input-output-hk/marlowe-cardano/commit/b6366efc9f8df38bfe9232f81e6caf2c7f11ffa8) makes this hash correspondence explicit in the Marlowe Cardano specification and adds a code snippet concretizing it, namely that the hash and continuation must be present in the script context datum map.


### 2.5.4 Merkleization section not detailed enough *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Merkleization`**
> 
> This section is too terse. It needs to explain what Merkleization is, and to motivate why it is needed.
> 
> When explaining how it works, it needs to make explicit that only the `Case` type is modified, and that in the semantics, only the `Input` type is modified. It needs to explain why the `Input` type needs to carry a hash and a contract, and why the evaluation of the contract is changed as described.

Commit [a9d40432](https://github.com/input-output-hk/marlowe-cardano/commit/a9d4043230cb4f240fab2d816bed6a3cab4f5053) adds to the Marlowe Cardano specification a paragraph elaborating on mechanics and motivation for Merkleization, namely the ability to handle Marlowe contract that are too large to store in a datum.


### 2.5.5 Unnecessary constraint *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, `Constraint 12. Merkleized continuations`** 
> 
> This constraint is unnecessary to have in the Marlowe validator, since the construction of the arguments for evaluation of the Marlowe contract would fail. However, it would be useful to have it appear in the specification for users to be aware of it when crafting transactions. A note to motivate the presence of the constraint could be helpful.

Commit [fda1d3e8](https://github.com/input-output-hk/marlowe-cardano/commit/fda1d3e862fc8f8c31ff479fbd338226e661eb0b) to the Marlowe Cardano specification clarifies that the constraint is supplementary (informational) in nature.


### 2.5.6 Asymmetry between role and wallet payouts *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, `Constraint 15`, **
> 
> The marlowe validator allows multiple outputs to be paid to a wallet, but it demands that a single output exists when paying to a role instead. The motivation to use different approaches needs to be documented. This is implemented in `Scripts.hs` at line 371, in function `payoutConstraints`.

The asymmetric is a convenience and practicality related to the manner in which coin selection and transaction balancing typically occurs nowadays in wallets. Commit [4e81470d](https://github.com/input-output-hk/marlowe-cardano/commit/4e81470de90ddd6858c3ad8aace96e90df5a86ae) adds to the Marlowe Cardano specification a paragraph justifying this asymmetry in payout style and a comment to the Marlowe semantics validator along the same lines.


### 2.5.7 Incorrect description of `rolePayoutValidator` *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Plutus Validator for Marlowe Payouts`** 
> 
> The description of the Marlowe payout validator in the specification states that it is parameterized by the currency symbol. However, this is not correct as the validator is unparameterized; rather, the datum type of the validator includes the currency symbol (as well as token name). The description should be modified to reflect this.

This incorrect signature is fixed in commit [1d16de1f](https://github.com/input-output-hk/marlowe-cardano/commit/1d16de1f1b7a167dc4eb4a057a3df2c24d0194c9).


### 2.5.8 Unspecified initial state *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Life Cycle of a Marlowe Contract`** 
> 
> The specification should say what the initial state of a Marlowe contract should be. In particular, creating a contract requires giving the minimum Ada to some account in the Marlowe state. Otherwise, Constraint 5 will reject the transactions that try to spend the output.

Commit [e150e308](https://github.com/input-output-hk/marlowe-cardano/commit/e150e30867dfa5466639f46bf39656aee2888e38) details the three invariants that the initial state must satisfy: positivity of accounts, non-duplication of state entries (accounts, choices, bound values), and matching the total value in the internal state to the value of the script's UTxO.


### 2.5.9 Unspecified behavior when multiple cases can apply *(Severity: Low)*

> **File `Semantics.hs`, Function `applyCases`, line *597***
> 
> If multiple cases in a case list can apply, the first one is taken. This behavior should be better communicated in the specification.

Although this behavior is required by the Isabelle specification and implemented in the Plutus validator, the comment on `applyCases` has been editing in commit [08d6f34a](https://github.com/input-output-hk/marlowe-cardano/commit/08d6f34ac91da7aa34e7414c5bae0e33e9235d74) to reinforce that the first applicable `Case` is taken for a `When`.


## 2.6 Haskell implementation


### 2.6.1 Name shadowing in `applyAllInputs` *(Severity: Medium)*

> **File `Semantics.hs`, Function `applyAllInputs`, line *658***
> 
> The binding `cont` from the `Applied` constructor shadows the `cont` variable coming from the pattern match in an enclosing case expression. This makes the code error-prone to subsequent changes and refactorings.

The binding of `cont` has been renamed to `cont'` in commit [1c96edfe](https://github.com/input-output-hk/marlowe-cardano/commit/1c96edfe7e22ecc499ed75dd175490a4f2427bdc).


### 2.6.2 Non-isomorphic types in `playTraceAux` *(Severity: Medium)*

> **File `Semantics.hs`, Function `playTraceAux`, line *710***
> 
> The function in the Isabelle code takes a `TransactionOutputRecord` while the Haskell version takes a `TransactionOutput`. This means `TransactionError` cannot be an input to `playTraceAux` in Isabelle, possibly invalidating proofs about its properties.

The `playTrace` and `playTraceAux` functions are not used by the Marlowe validators, so no mitigation was made for this audit-report finding.


### 2.6.3 Variable names differ from Isabelle code *(Severity: Low)*

> **File `Semantics.hs`, Several functions ``** 
> 
> Different variable names in Isabelle and Haskell make comparison harder. It is less of an issue when only one variable has been renamed in a function, but multiple variable renames require carefully mapping between the names to avoid confusion. For example, the code of `reduceContractStep` in line 482 (`Pay` case) is hard to compare.
> 
> Other name changes include:
> -   Line 456, function `updateMoneyInAccount` uses variable `money` where the Isabelle code uses `amount` and omits naming the last parameter.
> -   Line 473, function `giveMoneyToPay` uses variables `amount` and `accounts` instead of `money` and `accountsV` as in the Isabelle code.
> -   Line 541, function `reductionLoop` uses variable `con` instead of `ncontract`.
> -   Line 300, the data type `TransactionInput` corresponds to the type `Transaction` in the Isabelle code.
> -   Line 313, the data type `TransactionOutput` is isomorphic but not identical to the homonymous data type in the Isabelle code.
> -   Line 439, function `refundOne` uses a variable `balance` where the Isabelle code uses `money`.
> -   Line 463, function `addMoneyToAccount` uses variable `accounts` where the Isabelle code uses `accountsV`.

These cosmetic recommendations of the audit report have not been implemented in the Marlowe semantics validator, as the discrepancies do not strongly impact comparison.


### 2.6.4 Naming of functions and variables *(Severity: Low)*

> **File `Several files`, `several functions`** 
> 
> Several functions or variables could have more descriptive or precise names, for example:
> -   `Scripts.hs:193`: `validateBalances` could be called `allBalancesArePositive`.
> -   `Scripts.hs:206`: `validateInputs` could be called `allInputsAreAuthorized`.
> -   `Scripts.hs:324`: `checkScriptOutputAny` could be called `noOutputPaysToOwnAddress`, as it checks that *no* outputs pay to the script address.
> -   `Semantics.hs:439`: `refundOne` is named somewhat confusingly, and understanding the name requires the context of `reduceContractStep` where the function is called. Perhaps a better name would be `dropWhileNonPositiveAndUncons`.
> -   `Semantics.hs:597`: the binding `tailCase` should rather be named `tailCases`.

The aforementioned bindings `validateBalances`, `validateInputs`, and `tailCase` have been renamed to `allBalancesArePositive`, `allInputsAreAuthorized`, and `tailCases` in commit [1c96edfe](https://github.com/input-output-hk/marlowe-cardano/commit/1c96edfe7e22ecc499ed75dd175490a4f2427bdc). For historical reasons, `refundOne` has not been renamed. The function `checkScriptOutputAny` is no longer present due to other mitigations made to the validator.


### 2.6.5 Unused functions *(Severity: Low)*

> **File `Several files`, `several functions`** 
> 
> Several functions are unused and perhaps should be removed:
> -   `Semantics.hs:741`: `contractLifespanUpperBound` does not seem to be used anywhere, including tests.
> -   `Semantics.hs:680`: `isClose` is not used in the rest of the codebase (besides checking its behavior via testing). It should either be removed, or comments justifying its existence should be included.
> 
> In addition to that, the functions `validateBalances` and `totalBalance` (defined at `Semantics.hs:755` and `:762`) are only used in `Scripts.hs` and never reused, so they should probably be moved to `Scripts.hs`.

Although the validator does not use these functions, off-chain code in other Haskell modules does. For the time being, the `contractLifespanUpperBound` and `isClose` have been retained in `Language.Marlowe.Core.V1.Semantics`. They will be relocated in the future if validator and non-validator code is separated into different modules.


### 2.6.6 Comments *(Severity: Low)*

> **File `Semantics.hs`, Function `refundOne`, line *439***
> 
> The comment describing the function is overly concise, as it does not mention the function removing all non-positive accounts before the first positive one, and effectively `uncons`-ing the list.
> 
> **File `Semantics.hs`, Function `addMoneyToAccount`, line *461***
> 
> There is a typo in the comment: `accoun` is written instead of `account`.

Commit [1c96edfe](https://github.com/input-output-hk/marlowe-cardano/commit/1c96edfe7e22ecc499ed75dd175490a4f2427bdc) fixes this typo.


### 2.6.7 Record updates in `playTraceAux` *(Severity: Low)*

> **File `Semantics.hs`, Function `playTraceAux`, line *710***
> 
> The function could have followed the Isabelle code more closely if it used a record update instead of creating a new `TransactionOutput` record from scratch.

The `playTrace` and `playTraceAux` functions are not used by the Marlowe validators, so no mitigation was made for this audit-report finding.


### 2.6.8 Potential simplifications *(Severity: Low)*

> **File `Semantics.hs`, Function `totalBalance`, line *755***
> 
> The function uses `foldMap f . AssocMap.toList`. Here, `AssocMap.toList` is redundant.

Actually, the `PlutusTx.AssocMap.Map`'s implementation of `foldMap` does not permit this: type checking fails for this proposed change.

> **File `Types.hs`, Class instance `Eq Contract`, line *873***
> 
> The equality of cases for the `When` constructor would be simplified by using `cases1 == cases2`. If there is a reason for the more verbose equality condition, it should be outlined in a comment.

A comment explaining the rationale for this equality test has been added in commit [faaae175](https://github.com/input-output-hk/marlowe-cardano/commit/faaae1751957b4f750e3c11ffdc946de07baf0cd).


### 2.6.9 `computeTransaction` differs from the Isabelle implementation *(Severity: Low)*

> **Helper function `evalValue, evalObservation`, lines *391 (Semantics.hs), 34 (Semantics.thy)***
> 
> `evalValue` and `evalObservation` differ from the Isabelle implementation in the introduction of auxiliary variables to abbreviate the recursive calls. The comparison would be simpler if both definitions were consolidated.

The Plutus implementation differs slightly from the Isabelle for efficiency and to conform to Plutus's different restrictions on recursive calls.
 
> **Helper function `evalValue`, lines *395 (Semantics.hs), 35 (Semantics.thy)***
> 
> The Isabelle implementation should use the helper function `moneyInAccount` instead of inlining its definition, so as to maintain consistency with the Haskell implementation.

TODO: @hrajchert will add text here.
 
> **Helper function `applyCases`, lines *596 (Semantics.hs), 498 (Semantics.thy)***
> 
> The structure of function `applyCases` differs between the Haskell and Isabelle files. Specifically, the Haskell implementation has an additional function `applyAction` where the Isabelle implementation does not. A comment motivating the discrepancy would be needed. This is likely due to the lack of Merkleization in the Isabelle implementation.

Commit [d0a3834a](https://github.com/input-output-hk/marlowe-cardano/commit/d0a3834ae8484bb6c7d0ecd3aeec60871b3fd165) adds a comment that the Plutus implementation differs from the Isabelle one due to the former's support for merkleization.
 
> **Helper function `convertReduceWarnings`, lines *617 (Semantics.hs), 537 (Semantics.thy)***
> 
> The Haskell function is implemented using `foldr`, while the Isabelle function uses explicit recursion, making a one-to-one comparison less obvious. If there is a reason for this discrepancy, such as `foldr` yielding some optimizations, this should be outlined in a comment.

Commit [d1477610](https://github.com/input-output-hk/marlowe-cardano/commit/d14776101c22eac7fbc67893020f37cbc2a9e339) adds a comment that the use of `foldr` in the Plutus implementation is for efficiency.


### 2.6.10 Constraint implementations differ from description *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Plutus Validator for Marlowe Semantics`** 
> 
> Some constraints mentioned in the specification are written in a different structure than the corresponding constraint in `Scripts.hs`. While such a discrepancy may be useful to minimize verbosity, a unified structure when possible would alleviate a side-by-side comparison. Examples of these differing structures include Constraint 6 and Constraint 14.

The discrepancies of implementation between the constraints in the specification and the Plutus code result from the emphasis on readability in the specification and of efficiency in the implementation. The need to minimize of validator size and execution cost in the implementation has sometimes resulted in less consise or readible code. The Plutus compile can be quite sensitive to the precise expression of a constraint as Haskell code.


### 2.6.11 Missing argument of `computeTransaction` *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Section `Relationship between Marlowe Validator and Semantics`** 
> 
> The specification mentions the output datum as the (fifth) argument for the `computeTransaction` function, while it is not an argument to it.

Commit [00a0c240](https://github.com/input-output-hk/marlowe-cardano/commit/00a0c2406665f06753aecf6dbb63933edb275436) moves the comment about the non-existant fifth argument to a separate sentance following the list of arguments.


### 2.6.12 Missing `smallMarloweValidator` *(Severity: Low)*

> **File `marlowe-cardano-specification.md`, Various sections ``** 
> 
> The specification mentions `smallMarloweValidator` in a few places, but it is never mentioned in the source code.

This reference is changed to `marloweValidator` in commit [87cf548d](https://github.com/input-output-hk/marlowe-cardano/commit/87cf548d9ae7934a702ea1a1c85d7d9bd4993aa9).


### 2.6.13 Incorrect constraint reference *(Severity: Low)*

> **File `Scripts.hs`, Function `mkRolePayoutValidator`, line *150***
> 
> This line should refer to Constraint 17 rather than Constraint 16.

This incorrect reference is fixed in commit [3fac0d17](https://github.com/input-output-hk/marlowe-cardano/commit/3fac0d1749d107f13743756aa50c9723e776e391).


### 2.6.14 `MarloweParams` differs from the specification *(Severity: Low)*

> **File `Semantics.hs`, type `MarloweParams`, line *355***
> 
> The specification defines `MarloweParams` to contain just the payout validator hash, while the definition in the Haskell code contains just the roles currency symbol.

This mistatement is remedied in commit [8691f335](https://github.com/input-output-hk/marlowe-cardano/commit/8691f3351e55758cc750eee0800b1458f0a8c554).


### 2.6.15 Timeout boundary differs from the specification *(Severity: Low)*

> **File `Semantics.hs`, type `reduceContractStep`, line *518***
> 
> The specification mentions
> 
> > If a valid Transaction is computed with a TimeInterval with a start time bigger than the Timeout t, the contingency continuation c is evaluated.
> 
> where "bigger" implies strict inequality, while the code makes non-strict comparison. This difference needs to be acknowledged and further explained in the specification.

TODO: @hrajchert will add text here, since it relates to the Isabelle specification.


## 2.7 Haskell tests


### 2.7.1 More precise failure checks *(Severity: Medium)*

> **File `Spec/Marlowe/Plutus/Specification.hs`, `Various tests`** 
> 
> The tests use the functions `checkSemanticsTransaction` and `checkPayoutTransaction` to verify that various error conditions cause transactions to be rejected. These functions test that a transaction passes or fails, but when it fails, the functions do not consider the error cause. Checking the exact cause is necessary to ensure the transaction is rejected because of the intended reason and not because of some other error condition arising in a particular test case by coincidence.
> 
> The absence of this information makes it easier to accidentally produce a test that is not testing what is intended.

TODO: @bwbush will add text here.


### 2.7.2 Missing tests *(Severity: Medium)*

> **File `Spec/Marlowe/Semantics/Compute.hs`, ``** 
> 
> The following properties could additionally be tested for `computeTransaction`:
> -   payment subtracts from an account,
> -   deposit adds to an account,
> -   `INotify` input produces the expected continuation,
> -   `IChoice` input produces the expected continuation,
> -   the hash of a successfully applied merkleized input matches the hash of the merkleized case.
> 
> Some of these are tested in `Spec/Marlowe/Semantics/Functions.hs` already for auxiliary functions.

Commit [ee2e5222](https://github.com/input-output-hk/marlowe-cardano/commit/ee2e52220e25736af29a1f01144d5fafbe9eed76) adds a property-based test that choice and deposit continue as expected; commit [333eee29](https://github.com/input-output-hk/marlowe-cardano/commit/333eee293aa3afe95d0aa7f678c7e7b7bad660ea) tests that choice produces expected continuation; commit [477284c7](https://github.com/input-output-hk/marlowe-cardano/commit/477284c78095482eba63adc2e6090ea68553db9d) tests that that deposits add to an account; commit [d241669b](https://github.com/input-output-hk/marlowe-cardano/commit/d241669bfb7ec8dad1cc92a7ca6185d08229817e) tests that payout substracts from an account; and commit [f33fc720](https://github.com/input-output-hk/marlowe-cardano/commit/f33fc7206522031c93253323f3b8ca083d8ca8c7) tests that Merkleization continues as expected.
 
> **File `Spec/Marlowe/Semantics/Functions.hs`, `Missing merkleization tests`** 
> 
> The properties in this module do not seem to be tested with merkleized contracts or inputs except for `checkGetContinuation`. More merkleization tests should be added.

Commits [2a936bf1](https://github.com/input-output-hk/marlowe-cardano/commit/2a936bf1bbb890cc811b966b46a10fd38314dc25) and [8f8183d7](https://github.com/input-output-hk/marlowe-cardano/commit/8f8183d7f14c6bdc3841a1999077ef01ebac4144) significantly increase the coverage of merkleization in validator tests by utilizing a much larger set of test contracts and adding a probability that almost any test will involve a merkleized contract.
 
> **File `Spec/Marlowe/Semantics/Compute.hs`, function `checkFixInterval`, lines *100-102***
> 
> The test `checkFixInterval` is never instantiated with an invalid interval that is in the past, meaning the function `fixInterval` is never tested for that case.

Commit [811f048b](https://github.com/input-output-hk/marlowe-cardano/commit/811f048ba93db10972641c0c235864db1d6014e7) adds a property-based test for an invalid in terval in the past.


## Appendices


### Post-Audit Changes in Marlowe Specification

```bash
git diff 523f3d56f22bf992ddb0b0c8a52bb7a5a188f9e9 69468d6623e24a4ccd6659e378ae012c38ca01ce marlowe/specification/marlowe-cardano-specification.md
```

```diff
diff --git a/marlowe/specification/marlowe-cardano-specification.md b/marlowe/specification/marlowe-cardano-specification.md
index 326f6f321..312ccf361 100644
--- a/marlowe/specification/marlowe-cardano-specification.md
+++ b/marlowe/specification/marlowe-cardano-specification.md
@@ -3,7 +3,7 @@
 
 ## Scope
 
-This document defines the specification for Marlowe semantics's interface with the Cardano blockchain. Marlowe utilizes three Plutus scripts: (i) a monetary policy for the roles currency used in some Marlowe contracts; (ii) the Marlowe application validator script that enforces Marlowe semantics; and (iii) the Marlowe payout-validator script that allows the holder of a role token to withdraw funds paid by the Marlowe application. Marlowe semantics are defined in the Isabelle language and specified in [Marlowe Specification, Version 3 (draft)](marlowe-isabelle-specification-4f9fa249fa51ec09a4f286099d5399eb4301ed49.pdf).
+This document defines the specification for Marlowe semantics's interface with the Cardano blockchain. Marlowe utilizes three Plutus scripts: (i) a monetary policy for the roles currency used in some Marlowe contracts; (ii) the Marlowe application validator script that enforces Marlowe semantics; and (iii) the Marlowe payout-validator script that allows the holder of a role token to withdraw funds paid by the Marlowe application. Marlowe semantics are defined in the Isabelle language and specified in [Marlowe Specification, Version 3](marlowe-isabelle-specification-4f9fa249fa51ec09a4f286099d5399eb4301ed49.pdf).
 
 
 ## Contents
@@ -30,9 +30,14 @@ Marlowe contracts identify each participant by either a *public-key hash (PKH)*
 The execution of a Marlowe contract instance proceeds as a sequence of applications of inputs at the contract's script address.
 1. Role tokens are typically minted prior to or within the creation transaction of the contract instance, though this is not enforced on-chain.
 2. The creation transaction for the contract stores the state of the contract instance in the datum at the contract's script address.
-3. Each transaction that interacts with the contract instance updates the state/datum at that same address.
-4. If the contract instance pays funds to a role during application of inputs, those funds are sent to the address of the Marlowe payout-validator script, with a datum equal to the role name.
-5. When a contract instance closes, there is no output to the contract's script address.
+    - The creation transaction must contain sufficient lovelace to meet the [minimum UTxO requirement](../best-practices.md#minimum-utxo-requirement) *for every future state of the contract.*
+    - The initial state conforms to the state invariants required by Isabelle semantics and the Marlowe validator:
+	    - positive account balances,
+	    - no duplicate accounts, choices, or bound values, and
+	    - a total value that matches the value of the UTxO for the creation transaction.
+1. Each transaction that interacts with the contract instance updates the state/datum at that same address.
+2. If the contract instance pays funds to a role during application of inputs, those funds are sent to the address of the Marlowe payout-validator script, with a datum equal to the role name.
+3. When a contract instance closes, there is no output to the contract's script address.
 
 Thus each Marlowe contract instance is a finite sequence of continuations at the script address, from creation to closure. The following three UTxO diagrams illustrate the three typical types of Marlowe transactions.
 
@@ -42,11 +47,15 @@ Thus each Marlowe contract instance is a finite sequence of continuations at the
 
 ![A typical transaction to withdraw funds from the Marlowe payout validator script address](redeem.svg)
 
+Other Plutus scripts may run when the Marlowe semantics validator runs in a transaction *provided that the Marlowe transaction does not pay out funds.* Restricting other Plutus script to non-payout Marlowe transactions eliminates the possibility of double-satisfaction attacks. Examples of Plutus scripts that would be usefully run during Marlowe transactions are (1) an oracle which checks that the correct value is being reported as an `IChoice` or (2) a minting script that mints and deposits tokens into the Marlowe contract; in general such Plutus scripts would examine the Marlowe datum and redeemer to determine whether they validate the action that they are coordinating with Marlowe.
+
 
 ## Monetary Policy for Role Tokens
 
 Any Cardano monetary policy may be used to mint the role tokens used in a Marlowe contract instance. For security in standard Marlowe use cases, a one-time or locked minting policy such as `Plutus.Contracts.Currency.OneShotCurrency` is recommended. Exotic use cases might employ other monetary policies. It is the responsibility both of the developer of the off-chain code managing a contract instance and also of the user of the contract instance to verify that the monetary policy of the role tokens meets their security requirements.
 
+The off-chain [Marlowe Runtime](../marlowe-runtime/doc/) services use a safe one-shot monetary policy to mint role tokens if the user requests. The [Marlowe Best Practices Guide](../best-practices.md) discussed security requirements for role tokens.
+
 
 ## Representation of Marlowe Semantics in Plutus
 
@@ -97,10 +106,23 @@ data Input =
 In the above, the `BuiltinByteString` is the hash of the serialized continuation `Contract`.
 
 
+### Variations from Isabelle Semantics
+
+Marlowe's semantics validator uses Plutus's association list `PlutuxTx.AssocMap` that differs from the `MList` in Isabelle semantics in several respects:
+
+1.  The `insert`, `delete`, `member`, and `lookup` functions of `AssocMap` haven an equality (`Eq`) constraint whereas `MList` has a ordering (`Ord`) constraint.
+2.  If the elements of an `MList` are not in lexicographic order, then result of `insert`, `delete`, `member`, and `lookup` may differ from that in `AssocMap`.
+3.  The ordering of the result of `toList` may differ between `AssocMap` and `MList`.
+
+Provided that the initial state of the Marlowe contract does not contain duplicate entries in `accounts`, `choices`, or `boundValues` and also provided that the behavior of Marlowe's semantics validator is compared to Isabelle semantics with the Isabelle initial state for `accounts`, `choices`, and `boundValues` lexicographic ordered, the behavior of the Marlowe semantics validator does not differ from Isabelle semantics aside from the ordering of `accounts`, `choices`, and `boundValues` in Marlowe's state in the datum. Typically, Marlowe contracts start with an empty state, so this is not an issue, but one can in principle start a Marlowe contract with a non-empty state, even with one that contains duplicate entries. Internally to the validator, `computeTransaction` might order payments upon `Close` differently from Isabelle semantics, but that is undetectable at the validation or transaction level.
+
+
 ## Merkelization
 
 A contract can be represented as a tree of continuations ("sub-contracts") where each vertex is a contract and each edge follows either an `InputContent` made by a participant or a timeout. A `When` contract includes terms that are either (1) a `Case` which contains the `Action` that matches a particular `InputContent` via `NormalInput` and that explicitly includes the `Contract` continuation or (2) a `MerkleizedCase` which contains the `Action` that matches a particular `InputContent` via `MerkleizedInput` and that implicitly includes the continuation by reference to its Merkle hash. In the latter case `MerkleizedInput` includes both the Merkle hash of the continuation and the continuation `Contract` itself. The Plutus code must verify that the hash in the contract matches the hash in the input before it proceeds to use the continuation that was provided as input.
 
+Merkleization enables large contracts to be succinctly represented on chain: instead of storing gigabytes of data representing a huge contract, only the hash of that contract need be represented on the chain. For example, a contract `When [Case action timeout continuation] contract'` that validates input `TransactionInput interval [NormalInput input]` may be "merkleized" to a contract `When [MerkleizedCase action hash] contract'` that will validate the input `TransactionInput interval [MerkleizedInput input hash contract]` provided that `DatumHash hash ≡ datumHash . Datum . toBuiltinData $ contract`. When a contract is merkelized the information `(hash, contract)` is stored off chain and provide to the Marlowe validator if needed for input. The Cardano node computes the hash and provides the `(hash, contract)` information in the script context.
+
 The Isabelle semantics do not include merkleization of Marlowe contracts, but the Haskell implementation does.
 
 
@@ -108,7 +130,7 @@ The Isabelle semantics do not include merkleization of Marlowe contracts, but th
 
 The Marlowe validator is an unparameterized interpreter of Marlowe semantics. Thus, the script address of the Marlowe validator is independent of the particular contract instance and roles currency.
 ```haskell
-smallMarloweValidator :: MarloweData -> MarloweInput -> ScriptContext -> Bool
+marloweValidator :: MarloweData -> MarloweInput -> ScriptContext -> Bool
 ```
 
 
@@ -127,7 +149,7 @@ data MarloweData =
 data MarloweParams =
     MarloweParams
     {
-      rolePayoutValidatorHash :: ValidatorHash
+      rolesCurrency :: CurrencySymbol
     }
 ```
 
@@ -139,14 +161,17 @@ data MarloweTxInput =
     Input InputContent
   | MerkleizedTxInput InputContent BuiltinByteString
 ```
-In the above, the `BuiltinByteString` is the hash of the serialized continuation of the contract. If `MerkleizedTxInput` is supplied in a redeemer, then the `ScriptContext` for the transaction must also contain an extra entry in its `txInfoData . scriptContextTxInfo` map from `DatumHash` to `Datum` for the serialized continuation of the contract.
+In the above, the `BuiltinByteString` is the hash of the serialized continuation of the contract. If `MerkleizedTxInput` is supplied in a redeemer, then the `ScriptContext` for the transaction must also contain an extra entry in its `txInfoData . scriptContextTxInfo` map from `DatumHash` to `Datum` for the serialized continuation of the contract. Thus the `continuation` for a given `hash` is computed as follows:
+```haskell
+Just continuation = fromBuiltinData =<< lookup hash (txInfoData $ scriptContextTxInfo scriptContext) :: Maybe Contract
+```
 
 
 ### A Note about `Plutus.V1.Ledger.Value`
 
 This specification relies on the following properties of `Plutus.V1.Ledger.Value` in the `plutus-ledger-api` package:
 1. `instance Monoid Value`, where `mempty` is zero value for all tokens and `mappend` sums the amounts of corresponding token types.
-2. `leq` is a partial ordering requiring that quantity of each token in the first operand is less than or equal to quanity of the corresponding token in the second operand, where a missing token in one operand represents a zero quantity.
+2. `leq` is a partial ordering requiring that quantity of each token in the first operand is less than or equal to quantity of the corresponding token in the second operand, where a missing token in one operand represents a zero quantity.
 
 
 ### Relationship between Marlowe Validator and Semantics
@@ -156,9 +181,10 @@ The arguments of `computeTransaction` must be constructed as follows:
 2. The `txInputs` of `TransactionInput` is derived from the `MarloweInput` provided as the `Redeemer` and the `txInfoData . scriptContextTxInfo` of the `ScriptContext`, as detailed below.
 3. The `State` is the `marloweState` of the `MarloweData` provided as the `Datum`.
 4. The `Contract` is the `marloweContract` of the `MarloweData` provided as the `Datum`.
-5. The new `Datum` at the script address is the `MarloweData` with the same `marloweParams` as originally, but with the new `txOutState` and `txOutContract` of the `TransactionOutput`.
 
-In the diagram below, the upper three rectangles represent functions: the untyped `Validator`, the typed validator `smallMarloweValidator`, or the semantics's `computeTransaction`. The data values (ovals) are marshalled or passed from the untyped representation over to the semantics. The `computeTransaction` function validates the semantics and returns the required new state and contract instance. Conceptually, success or failure is passed to the untyped validator. The bottom rectangle packages the `Datum` that is provided as output for the continued progression of the Marlowe contract instance.
+Additionally, the new `Datum` at the script address is the `MarloweData` with the same `marloweParams` as originally, but with the new `txOutState` and `txOutContract` of the `TransactionOutput`.
+
+In the diagram below, the upper three rectangles represent functions: the untyped `Validator`, the typed validator `marloweValidator`, or the semantics's `computeTransaction`. The data values (ovals) are marshalled or passed from the untyped representation over to the semantics. The `computeTransaction` function validates the semantics and returns the required new state and contract instance. Conceptually, success or failure is passed to the untyped validator. The bottom rectangle packages the `Datum` that is provided as output for the continued progression of the Marlowe contract instance.
 
 ![Relationship between Marlowe validator and semantics.](semantics2plutus.svg)
 
@@ -167,7 +193,7 @@ In the diagram below, the upper three rectangles represent functions: the untype
 
 Consider the application of the Marlowe validator and Marlowe semantics:
 ```haskell
-validationResult = smallMarloweValidator marloweData marloweInput scriptContext
+validationResult = marloweValidator marloweData marloweInput scriptContext
 
 transactionOutput = computeTransaction transactionInput inState inContract
 ```
@@ -241,12 +267,14 @@ inValue ≡ foldMap toValue (accounts $ marloweState marloweData)
 
 #### *Constraint 6.* Output value to script
 
-The beginning balance plus the deposits equals the ending balance plus the payments.
+The beginning balance plus the deposits (with negative deposits treated as zero, as required by the semantics) equals the ending balance plus the payments.
 ```haskell
 inValue + foldMap valueOfDeposit (fmap getInputContent transactionInput) ≡ outValue + foldMap valueOfPayment (txOutPayments transactionOutput)
   where getInputContent (Input inputContent) = inputContent
         getInputContent (MerkleizedTxInput inputContent _) = inputContent
-        valueOfDeposit (IDeposit _ _ (Token currency name) count) = Value.singleton currency name count
+        valueOfDeposit (IDeposit _ _ (Token currency name) count)
+          | count > 0 = Value.singleton currency name count
+          | otherwise = mempty
         valueOfDeposit _ = mempty
         valueOfPayment (Payment _ (Party _) value)) = value
         valueOfPayment _ = mempty
@@ -302,12 +330,16 @@ all demerkleizes transactionInput ≡ True
         demerkleizes (Input _) = True
 ```
 
+Note that this constraint is not strictly necessary and is included here for informational purposes, since a valid transaction could not be constructed if it were removed.
+
 
 #### *Constraint 13.* Positive balances
 
-All accounts in the state have positive balances.
+All accounts in the initial and final states have positive balances.
 ```haskell
-all ((> 0) . snd) (accounts $ marloweState marloweData) ≡ True
+positiveBalances $ marloweState marloweData     ≡ True
+positiveBalances $ txOutState transactionOutput ≡ True
+  where positiveBalances state = all ((> 0) . snd) (accounts state)
 ```
 
 
@@ -345,6 +377,38 @@ all sufficient (txOutPayments transactionOutput)
 
 Note that the comparison is `leq` instead of equality because additional Ada may be required in the payment in order to satisfy the ledger's `minimum UTxO` constraint.
 
+The payment to a role must be in a single output, but the payment to an address may be split in multiple outputs, so long as the total output to the address is sufficient. (Note that allowing the multiple outputs to an address may increase transaction fees and wallet fragmentation, but the magnitude of this is severely limited by the Plutus execution budget, which strongly depends upon the number of UTxOs output. The flexibily of multiple outputs accommodates wallet-related practicalities (e.g., limitations in coin-selection and transaction balancing) such as the change and the return of the role token being in separate UTxOs in situations where a contract is also paying to the address where that change and that role token are sent.)
+
+
+#### *Constraint 18.* Final balance
+
+The value output to the script's UTxO must equal the total value in the output state.
+```haskell
+outValue ≡ foldMap toValue (accounts $ txOutState transactionOutput)
+  where toValue ((_, Token currency name), count)) = Value.singleton currency name count
+```
+
+
+#### *Constraint 19.* No duplicates
+
+The initial and final state must not have duplicate keys in their account entries, choices, or bound values.
+```haskell
+hasDuplicateKey (accounts    inState ) ≡ False
+hasDuplicateKey (choices     inState ) ≡ False
+hasDuplicateKey (boundValues inState ) ≡ False
+hasDuplicateKey (accounts    outState) ≡ False
+hasDuplicateKey (choices     outState) ≡ False
+hasDuplicateKey (boundValues outState) ≡ False
+  where
+    outState = txOutState transactionOutput
+    hasDuplicateKey am = let ks = fst <$> toList am in length ks /= length (nub ks)
+```
+
+
+#### *Constraint 20.* Single satisfaction
+
+If the contract makes payments, then the Marlowe validator must be the only validator executing in the transaction.
+
 
 ## Plutus Validator for Marlowe Payouts
 
@@ -359,7 +423,7 @@ rolePayoutValidator :: (CurrencySymbol, TokenName) -> () -> ScriptContext -> Boo
 
 Consider the application of the Marlowe payout validator:
 ```haskell
-validationResult' = rolePayoutValidator rolesCurrency' role () scriptContext
+validationResult' = rolePayoutValidator (rolesCurrency', role) () scriptContext
 ```
 
 The validation fails (via returning `False` for `validationResult'` or via the throwing of an error) if any of the following constraints does not hold.
```


### Post-Audit Changes in Marlowe Validator

```bash
git diff 523f3d56f22bf992ddb0b0c8a52bb7a5a188f9e9 69468d6623e24a4ccd6659e378ae012c38ca01ce marlowe/src/Language/Marlowe/{Core/V1/Semantics*,Scripts.hs}
```

```diff
diff --git a/marlowe/src/Language/Marlowe/Core/V1/Semantics.hs b/marlowe/src/Language/Marlowe/Core/V1/Semantics.hs
index e31b8c478..82b57b903 100644
--- a/marlowe/src/Language/Marlowe/Core/V1/Semantics.hs
+++ b/marlowe/src/Language/Marlowe/Core/V1/Semantics.hs
@@ -94,12 +94,12 @@ module Language.Marlowe.Core.V1.Semantics
   , TransactionError(..)
   , TransactionWarning(..)
     -- * Utility Functions
+  , allBalancesArePositive
   , contractLifespanUpperBound
   , isClose
   , notClose
   , paymentMoney
   , totalBalance
-  , validateBalances
     -- * Serialisation
   , currencySymbolFromJSON
   , currencySymbolToJSON
@@ -217,6 +217,26 @@ import Text.PrettyPrint.Leijen (comma, hang, lbrace, line, rbrace, space, text,
 data Payment = Payment AccountId Payee Token Integer
   deriving stock (Haskell.Eq, Haskell.Show)
 
+instance ToJSON Payment where
+  toJSON (Payment accountId payee token amount) =
+    object
+      [
+        "payment_from" .= accountId
+      , "to" .= payee
+      , "token" .= token
+      , "amount" .= amount
+      ]
+
+instance FromJSON Payment where
+  parseJSON =
+    withObject "Payment"
+      $ \o ->
+        Payment
+          <$> o .: "payment_from"
+          <*> o .: "to"
+          <*> o .: "token"
+          <*> o .: "amount"
+
 
 -- | Extract the money value from a payment.
 paymentMoney :: Payment -> Money
@@ -293,7 +313,28 @@ data TransactionError = TEAmbiguousTimeIntervalError
                       | TEUselessTransaction
                       | TEHashMismatch
   deriving stock (Haskell.Show, Generic, Haskell.Eq)
-  deriving anyclass (ToJSON, FromJSON)
+
+instance ToJSON TransactionError where
+  toJSON TEAmbiguousTimeIntervalError = JSON.String "TEAmbiguousTimeIntervalError"
+  toJSON TEApplyNoMatchError = JSON.String "TEApplyNoMatchError"
+  toJSON (TEIntervalError intervalError) = object ["error" .= JSON.String "TEIntervalError", "context" .= intervalError]
+  toJSON TEUselessTransaction = JSON.String "TEUselessTransaction"
+  toJSON TEHashMismatch = JSON.String "TEHashMismatch"
+
+instance FromJSON TransactionError where
+  parseJSON (JSON.String s) =
+    case s of
+      "TEAmbiguousTimeIntervalError" -> return TEAmbiguousTimeIntervalError
+      "TEApplyNoMatchError" -> return TEApplyNoMatchError
+      "TEUselessTransaction" -> return TEUselessTransaction
+      "TEHashMismatch" -> return TEHashMismatch
+      _ -> Haskell.fail "Failed parsing TransactionError"
+  parseJSON (JSON.Object o) = do
+                                err <- o .: "error"
+                                if err Haskell.== ("TEIntervalError" :: Haskell.String)
+                                  then TEIntervalError <$> o .: "context"
+                                  else Haskell.fail "Failed parsing TransactionError"
+  parseJSON _ = Haskell.fail "Failed parsing TransactionError"
 
 
 -- | Marlowe transaction input.
@@ -319,6 +360,31 @@ data TransactionOutput =
     | Error TransactionError
   deriving stock (Haskell.Show)
 
+instance ToJSON TransactionOutput where
+  toJSON TransactionOutput{..} =
+    object
+      [
+        "warnings" .= txOutWarnings
+      , "payments" .= txOutPayments
+      , "state" .= txOutState
+      , "contract" .= txOutContract
+      ]
+  toJSON (Error err) = object ["transaction_error" .= err]
+
+instance FromJSON TransactionOutput where
+  parseJSON =
+    withObject "TransactionOutput"
+      $ \o ->
+        let
+          asTransactionOutput =
+            TransactionOutput
+              <$> o .: "warnings"
+              <*> o .: "payments"
+              <*> o .: "state"
+              <*> o .: "contract"
+          asError = Error <$> o .: "transaction_error"
+        in
+          asTransactionOutput <|> asError
 
 -- | Parse a validator hash from JSON.
 validatorHashFromJSON :: JSON.Value -> Parser ValidatorHash
@@ -404,12 +470,22 @@ evalValue env state value = let
                                    then 0
                                    else n `Builtins.quotientInteger` d
         ChoiceValue choiceId ->
+            -- SCP-5126: Given the precondition that `choices` contains no
+            -- duplicate entries, this lookup behaves identically to
+            -- Marlowe's Isabelle semantics given the precondition that
+            -- the initial state's `choices` in Isabelle was sorted and
+            -- did not contain duplicate entries.
             case Map.lookup choiceId (choices state) of
                 Just x  -> x
                 Nothing -> 0
         TimeIntervalStart    -> getPOSIXTime (fst (timeInterval env))
         TimeIntervalEnd      -> getPOSIXTime (snd (timeInterval env))
         UseValue valId       ->
+            -- SCP-5126: Given the precondition that `boundValues` contains
+            -- no duplicate entries, this lookup behaves identically to
+            -- Marlowe's Isabelle semantics given the precondition that
+            -- the initial state's `boundValues` in Isabelle was sorted
+            -- and did not contain duplicate entries.
             case Map.lookup valId (boundValues state) of
                 Just x  -> x
                 Nothing -> 0
@@ -425,6 +501,11 @@ evalObservation env state obs = let
         AndObs lhs rhs          -> evalObs lhs && evalObs rhs
         OrObs lhs rhs           -> evalObs lhs || evalObs rhs
         NotObs subObs           -> not (evalObs subObs)
+                                   -- SCP-5126: Given the precondition that `choices` contains no
+                                   -- duplicate entries, this membership test behaves identically
+                                   -- to Marlowe's Isabelle semantics given the precondition that
+                                   -- the initial state's `choices` in Isabelle was sorted and did
+                                   -- not contain duplicate entries.
         ChoseSomething choiceId -> choiceId `Map.member` choices state
         ValueGE lhs rhs         -> evalVal lhs >= evalVal rhs
         ValueGT lhs rhs         -> evalVal lhs > evalVal rhs
@@ -439,6 +520,12 @@ evalObservation env state obs = let
 refundOne :: Accounts -> Maybe ((Party, Token, Integer), Accounts)
 refundOne accounts = case Map.toList accounts of
     [] -> Nothing
+    -- SCP-5126: The return value of this function differs from
+    -- Isabelle semantics in that it returns the least-recently
+    -- added account-token combination rather than the first
+    -- lexicographically ordered one. Also, the sequence
+    -- `Map.fromList . tail . Map.toList` preserves the
+    -- invariants of order and non-duplication.
     ((accId, token), balance) : rest ->
         if balance > 0
         then Just ((accId, token, balance), Map.fromList rest)
@@ -447,18 +534,30 @@ refundOne accounts = case Map.toList accounts of
 
 -- | Obtains the amount of money available an account.
 moneyInAccount :: AccountId -> Token -> Accounts -> Integer
-moneyInAccount accId token accounts = case Map.lookup (accId, token) accounts of
-    Just x  -> x
-    Nothing -> 0
+moneyInAccount accId token accounts =
+    -- SCP-5126: Given the precondition that `accounts` contains
+    -- no duplicate entries, this lookup behaves identically to
+    -- Marlowe's Isabelle semantics given the precondition that
+    -- the initial state's `accounts` in Isabelle was sorted and
+    -- did not contain duplicate entries.
+    case Map.lookup (accId, token) accounts of
+      Just x  -> x
+      Nothing -> 0
 
 
 -- | Sets the amount of money available in an account.
 updateMoneyInAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
 updateMoneyInAccount accId token amount =
+    -- SCP-5126: Given the precondition that `accounts` contains
+    -- no duplicate entries, this deletion or insertion behaves
+    -- identically (aside from internal ordering) to Marlowe's
+    -- Isabelle semantics given the precondition that the initial
+    -- state's `accounts` in Isabelle was sorted and did not
+    -- contain duplicate entries.
     if amount <= 0 then Map.delete (accId, token) else Map.insert (accId, token) amount
 
 
--- | Add the given amount of money to an accoun (only if it is positive).
+-- | Add the given amount of money to an account (only if it is positive).
 --   Return the updated Map.
 addMoneyToAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
 addMoneyToAccount accId token amount accounts = let
@@ -482,6 +581,14 @@ giveMoney accountId payee token amount accounts = let
 reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
 reduceContractStep env state contract = case contract of
 
+    -- SCP-5126: Although `refundOne` refunds accounts-token combinations
+    -- in least-recently-added order and Isabelle semantics requires that
+    -- they be refunded in lexicographic order, `reduceContractUntilQuiescent`
+    -- ensures that the `Close` pattern will be executed until `accounts`
+    -- is empty. Thus, the net difference between the behavior here and the
+    -- Isabelle semantics is that the `ContractQuiescent` resulting from
+    -- `reduceContractUntilQuiescent` will contain payments in a different
+    -- order.
     Close -> case refundOne (accounts state) of
         Just ((party, token, amount), newAccounts) -> let
             newState = state { accounts = newAccounts }
@@ -522,7 +629,17 @@ reduceContractStep env state contract = case contract of
     Let valId val cont -> let
         evaluatedValue = evalValue env state val
         boundVals = boundValues state
+        -- SCP-5126: Given the precondition that `boundValues` contains
+        -- no duplicate entries, this insertion behaves identically
+        -- (aside from internal ordering) to Marlowe's Isabelle semantics
+        -- given the precondition that the initial state's `boundValues`
+        -- in Isabelle was sorted and did not contain duplicate entries.
         newState = state { boundValues = Map.insert valId evaluatedValue boundVals }
+        -- SCP-5126: Given the precondition that `boundValues` contains
+        -- no duplicate entries, this lookup behaves identically to
+        -- Marlowe's Isabelle semantics given the precondition that the
+        -- initial state's `boundValues` in Isabelle was sorted and did
+        -- not contain duplicate entries.
         warn = case Map.lookup valId boundVals of
               Just oldVal -> ReduceShadowing valId oldVal evaluatedValue
               Nothing     -> ReduceNoWarning
@@ -575,6 +692,11 @@ applyAction env state (IDeposit accId1 party1 tok1 amount) (Deposit accId2 party
     else NotAppliedAction
 applyAction _ state (IChoice choId1 choice) (Choice choId2 bounds) =
     if choId1 == choId2 && inBounds choice bounds
+    -- SCP-5126: Given the precondition that `choices` contains no
+    -- duplicate entries, this insertion behaves identically (aside
+    -- from internal ordering) to Marlowe's Isabelle semantics
+    -- given the precondition that the initial state's `choices`
+    -- in Isabelle was sorted and did not contain duplicate entries.
     then let newState = state { choices = Map.insert choId1 choice (choices state) }
          in AppliedAction ApplyNoWarning newState
     else NotAppliedAction
@@ -592,18 +714,20 @@ getContinuation (MerkleizedInput _ inputContinuationHash continuation) (Merkleiz
     else Nothing
 getContinuation _ _ = Nothing
 
--- | Try to apply an input to a list of cases.
+-- | Try to apply an input to a list of cases, accepting the first match.
 applyCases :: Environment -> State -> Input -> [Case Contract] -> ApplyResult
-applyCases env state input (headCase : tailCase) =
+applyCases env state input (headCase : tailCases) =
     let inputContent = getInputContent input :: InputContent
         action = getAction headCase :: Action
         maybeContinuation = getContinuation input headCase :: Maybe Contract
     in case applyAction env state inputContent action of
          AppliedAction warning newState ->
+           -- Note that this differs from Isabelle semantics because
+           -- the Cardano semantics includes merkleization.
            case maybeContinuation of
              Just continuation -> Applied warning newState continuation
              Nothing           -> ApplyHashMismatch
-         NotAppliedAction -> applyCases env state input tailCase
+         NotAppliedAction -> applyCases env state input tailCases
 applyCases _ _ _ [] = ApplyNoMatchError
 
 
@@ -615,7 +739,7 @@ applyInput _ _ _ _                          = ApplyNoMatchError
 
 -- | Propagate 'ReduceWarning' to 'TransactionWarning'.
 convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning]
-convertReduceWarnings = foldr (\warn acc -> case warn of
+convertReduceWarnings = foldr (\warn acc -> case warn of  -- Note that `foldr` is used here for efficiency, differing from Isabelle.
     ReduceNoWarning -> acc
     ReduceNonPositivePay accId payee tok amount ->
         TransactionNonPositivePay accId payee tok amount : acc
@@ -655,12 +779,12 @@ applyAllInputs env state contract inputs = let
                     curState
                     cont
                 (input : rest) -> case applyInput env curState input cont of
-                    Applied applyWarn newState cont ->
+                    Applied applyWarn newState cont' ->
                         applyAllLoop
                             True
                             env
                             newState
-                            cont
+                            cont'
                             rest
                             (warnings' ++ convertApplyWarning applyWarn)
                             payments'
@@ -759,8 +883,8 @@ totalBalance accounts = foldMap
 
 
 -- | Check that all accounts have positive balance.
-validateBalances :: State -> Bool
-validateBalances State{..} = all (\(_, balance) -> balance > 0) (Map.toList accounts)
+allBalancesArePositive :: State -> Bool
+allBalancesArePositive State{..} = all (\(_, balance) -> balance > 0) (Map.toList accounts)
 
 
 instance FromJSON TransactionInput where
@@ -845,20 +969,26 @@ instance Eq Payment where
 instance Eq ReduceWarning where
     {-# INLINABLE (==) #-}
     ReduceNoWarning == ReduceNoWarning = True
-    (ReduceNonPositivePay acc1 p1 tn1 a1) == (ReduceNonPositivePay acc2 p2 tn2 a2) =
+    ReduceNoWarning == _ = False
+    ReduceNonPositivePay acc1 p1 tn1 a1 == ReduceNonPositivePay acc2 p2 tn2 a2 =
         acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2
-    (ReducePartialPay acc1 p1 tn1 a1 e1) == (ReducePartialPay acc2 p2 tn2 a2 e2) =
+    ReduceNonPositivePay{} == _ = False
+    ReducePartialPay acc1 p1 tn1 a1 e1 == ReducePartialPay acc2 p2 tn2 a2 e2 =
         acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2 && e1 == e2
-    (ReduceShadowing v1 old1 new1) == (ReduceShadowing v2 old2 new2) =
+    ReducePartialPay{} == _ = False
+    ReduceShadowing v1 old1 new1 == ReduceShadowing v2 old2 new2 =
         v1 == v2 && old1 == old2 && new1 == new2
-    _ == _ = False
+    ReduceShadowing{} == _ = False
+    ReduceAssertionFailed == ReduceAssertionFailed = True
+    ReduceAssertionFailed == _ = False
 
 
 instance Eq ReduceEffect where
     {-# INLINABLE (==) #-}
     ReduceNoPayment == ReduceNoPayment           = True
+    ReduceNoPayment == _                         = False
     ReduceWithPayment p1 == ReduceWithPayment p2 = p1 == p2
-    _ == _                                       = False
+    ReduceWithPayment _ == _                     = False
 
 
 -- Lifting data types to Plutus Core
diff --git a/marlowe/src/Language/Marlowe/Core/V1/Semantics/Types.hs b/marlowe/src/Language/Marlowe/Core/V1/Semantics/Types.hs
index a333b8fbb..bf495773b 100644
--- a/marlowe/src/Language/Marlowe/Core/V1/Semantics/Types.hs
+++ b/marlowe/src/Language/Marlowe/Core/V1/Semantics/Types.hs
@@ -108,7 +108,7 @@ import PlutusTx.Lift (makeLift)
 import PlutusTx.Prelude hiding (encodeUtf8, mapM, (<$>), (<*>), (<>))
 import Prelude (mapM, (<$>))
 import qualified Prelude as Haskell
-import Text.PrettyPrint.Leijen (text)
+import Text.PrettyPrint.Leijen (parens, text)
 
 
 -- Functions that used in Plutus Core must be inlinable,
@@ -126,8 +126,8 @@ data Party =
   deriving stock (Generic,Haskell.Eq,Haskell.Ord)
 
 instance Pretty Party where
-  prettyFragment (Address network address) = text $ "Address " ++ Haskell.show (serialiseAddressBech32 network address)
-  prettyFragment (Role role)               = text $ "Role "    ++ Haskell.show role
+  prettyFragment (Address network address) = parens $ text "Address " Haskell.<> prettyFragment (serialiseAddressBech32 network address)
+  prettyFragment (Role role)               = parens $ text "Role "    Haskell.<> prettyFragment role
 
 instance Haskell.Show Party where
   showsPrec _ (Address network address) = Haskell.showsPrec 11 $ Haskell.show (serialiseAddressBech32 network address)
@@ -307,6 +307,13 @@ data State = State { accounts    :: Accounts
 newtype Environment = Environment { timeInterval :: TimeInterval }
   deriving stock (Haskell.Show,Haskell.Eq,Haskell.Ord)
 
+instance FromJSON Environment where
+  parseJSON = withObject "Environment"
+    (\v -> Environment <$> (posixIntervalFromJSON =<< v .: "timeInterval"))
+
+instance ToJSON Environment where
+  toJSON Environment{..} = object
+    [ "timeInterval" .= posixIntervalToJSON timeInterval]
 
 -- | Input for a Marlowe contract. Correspond to expected 'Action's.
 data InputContent = IDeposit AccountId Party Token Integer
@@ -389,23 +396,24 @@ data IntervalError = InvalidInterval TimeInterval
                    | IntervalInPastError POSIXTime TimeInterval
   deriving stock (Haskell.Show, Generic, Haskell.Eq)
 
+
 instance ToJSON IntervalError where
   toJSON (InvalidInterval (s, e)) = A.object
-    [ ("invalidInterval", toJSON (posixTimeToJSON s, posixTimeToJSON e)) ]
+    [ ("invalidInterval", A.object [("from", posixTimeToJSON s), ("to", posixTimeToJSON e)]) ]
   toJSON (IntervalInPastError t (s, e)) = A.object
-    [ ("intervalInPastError", toJSON (posixTimeToJSON t, posixTimeToJSON s, posixTimeToJSON e)) ]
+    [ ("intervalInPastError", A.object [("minTime", posixTimeToJSON t), ("from", posixTimeToJSON s), ("to", posixTimeToJSON e)]) ]
 
 instance FromJSON IntervalError where
   parseJSON (JSON.Object v) =
     let
       parseInvalidInterval = do
-        (s, e) <- v .: "invalidInterval"
-        InvalidInterval <$> ((,) <$> posixTimeFromJSON s <*> posixTimeFromJSON e)
+        o <- v .: "invalidInterval"
+        InvalidInterval <$> posixIntervalFromJSON o
       parseIntervalInPastError = do
-        (t, s, e) <- v .: "intervalInPastError"
+        o <- v .: "intervalInPastError"
         IntervalInPastError
-          <$> posixTimeFromJSON t
-          <*> ((,) <$> posixTimeFromJSON s <*> posixTimeFromJSON e)
+          <$> (posixTimeFromJSON =<< o .: "minTime")
+          <*> posixIntervalFromJSON o
     in
       parseIntervalInPastError <|> parseInvalidInterval
   parseJSON invalid =
@@ -422,11 +430,18 @@ posixTimeFromJSON = \case
   invalid ->
       JSON.prependFailure "parsing POSIXTime failed, " (JSON.typeMismatch "Number" invalid)
 
+posixIntervalFromJSON :: A.Object -> Parser TimeInterval
+posixIntervalFromJSON o = (,) <$> (posixTimeFromJSON =<< o .: "from") <*> (posixTimeFromJSON =<< o .: "to")
 
 -- | Serialise time as a JSON value.
 posixTimeToJSON :: POSIXTime -> JSON.Value
 posixTimeToJSON (POSIXTime n) = JSON.Number $ scientific n 0
 
+posixIntervalToJSON :: TimeInterval -> JSON.Value
+posixIntervalToJSON (from, to) = object
+  [ "from" .= posixTimeToJSON from
+  , "to" .= posixTimeToJSON to
+  ]
 
 -- | Result of 'fixInterval'
 data IntervalResult = IntervalTrimmed Environment State
@@ -778,23 +793,24 @@ instance ToJSON Contract where
 instance Eq Party where
     {-# INLINABLE (==) #-}
     Address n1 a1 == Address n2 a2 = n1 == n2 && a1 == a2
+    Address _ _   == _             = False
     Role r1       == Role r2       = r1 == r2
-    _             == _             = False
+    Role _        == _             = False
 
 
 instance Eq ChoiceId where
     {-# INLINABLE (==) #-}
-    (ChoiceId n1 p1) == (ChoiceId n2 p2) = n1 == n2 && p1 == p2
+    ChoiceId n1 p1 == ChoiceId n2 p2 = n1 == n2 && p1 == p2
 
 
 instance Eq Token where
     {-# INLINABLE (==) #-}
-    (Token n1 p1) == (Token n2 p2) = n1 == n2 && p1 == p2
+    Token n1 p1 == Token n2 p2 = n1 == n2 && p1 == p2
 
 
 instance Eq ValueId where
     {-# INLINABLE (==) #-}
-    (ValueId n1) == (ValueId n2) = n1 == n2
+    ValueId n1 == ValueId n2 = n1 == n2
 
 
 instance Pretty ValueId where
@@ -804,78 +820,107 @@ instance Pretty ValueId where
 instance Eq Payee where
     {-# INLINABLE (==) #-}
     Account acc1 == Account acc2 = acc1 == acc2
+    Account{}    == _            = False
     Party p1 == Party p2         = p1 == p2
-    _ == _                       = False
+    Party{}  == _                = False
 
 instance Eq a => Eq (Value a) where
     {-# INLINABLE (==) #-}
-    AvailableMoney acc1 tok1 == AvailableMoney acc2 tok2 =
-        acc1 == acc2 && tok1 == tok2
+    AvailableMoney acc1 tok1 == AvailableMoney acc2 tok2 = acc1 == acc2 && tok1 == tok2
+    AvailableMoney _    _    == _                        = False
     Constant i1 == Constant i2 = i1 == i2
+    Constant{}  == _           = False
     NegValue val1 == NegValue val2 = val1 == val2
+    NegValue{}    == _             = False
     AddValue val1 val2 == AddValue val3 val4 = val1 == val3 && val2 == val4
+    AddValue{}         == _                  = False
     SubValue val1 val2 == SubValue val3 val4 = val1 == val3 && val2 == val4
+    SubValue{}         == _                  = False
     MulValue val1 val2 == MulValue val3 val4 = val1 == val3 && val2 == val4
+    MulValue{}         == _                  = False
     DivValue val1 val2 == DivValue val3 val4 = val1 == val3 && val2 == val4
+    DivValue{}         == _                  = False
     ChoiceValue cid1 == ChoiceValue cid2 = cid1 == cid2
+    ChoiceValue{}    == _                = False
     TimeIntervalStart == TimeIntervalStart = True
-    TimeIntervalEnd   == TimeIntervalEnd   = True
+    TimeIntervalStart == _                 = False
+    TimeIntervalEnd == TimeIntervalEnd = True
+    TimeIntervalEnd == _               = False
     UseValue val1 == UseValue val2 = val1 == val2
-    Cond obs1 thn1 els1 == Cond obs2 thn2 els2 =  obs1 == obs2 && thn1 == thn2 && els1 == els2
-    _ == _ = False
+    UseValue{}    == _             = False
+    Cond obs1 thn1 els1 == Cond obs2 thn2 els2 = obs1 == obs2 && thn1 == thn2 && els1 == els2
+    Cond{}              == _                   = False
 
 
 instance Eq Observation where
     {-# INLINABLE (==) #-}
     AndObs o1l o2l == AndObs o1r o2r           = o1l == o1r && o2l == o2r
+    AndObs{}       == _                        = False
     OrObs  o1l o2l == OrObs  o1r o2r           = o1l == o1r && o2l == o2r
+    OrObs{}        == _                        = False
     NotObs ol == NotObs or                     = ol == or
+    NotObs{}  == _                             = False
     ChoseSomething cid1 == ChoseSomething cid2 = cid1 == cid2
+    ChoseSomething _    == _                   = False
     ValueGE v1l v2l == ValueGE v1r v2r         = v1l == v1r && v2l == v2r
+    ValueGE{}       == _                       = False
     ValueGT v1l v2l == ValueGT v1r v2r         = v1l == v1r && v2l == v2r
+    ValueGT{}       == _                       = False
     ValueLT v1l v2l == ValueLT v1r v2r         = v1l == v1r && v2l == v2r
+    ValueLT{}       == _                       = False
     ValueLE v1l v2l == ValueLE v1r v2r         = v1l == v1r && v2l == v2r
+    ValueLE{}       == _                       = False
     ValueEQ v1l v2l == ValueEQ v1r v2r         = v1l == v1r && v2l == v2r
+    ValueEQ{}       == _                       = False
     TrueObs  == TrueObs                        = True
+    TrueObs  == _                              = False
     FalseObs == FalseObs                       = True
-    _ == _                                     = False
+    FalseObs == _                              = False
 
 
 instance Eq Action where
     {-# INLINABLE (==) #-}
     Deposit acc1 party1 tok1 val1 == Deposit acc2 party2 tok2 val2 =
         acc1 == acc2 && party1 == party2 && tok1 == tok2 && val1 == val2
+    Deposit{}       == _ = False
     Choice cid1 bounds1 == Choice cid2 bounds2 =
         cid1 == cid2 && length bounds1 == length bounds2 && let
             bounds = zip bounds1 bounds2
             checkBound (Bound low1 high1, Bound low2 high2) = low1 == low2 && high1 == high2
             in all checkBound bounds
+    Choice{}   == _ = False
     Notify obs1 == Notify obs2 = obs1 == obs2
-    _ == _ = False
+    Notify{} == _ = False
 
 
 instance Eq a => Eq (Case a) where
     {-# INLINABLE (==) #-}
     Case acl cl == Case acr cr                       = acl == acr && cl == cr
+    Case{}      == _                                 = False
     MerkleizedCase acl bsl == MerkleizedCase acr bsr = acl == acr && bsl == bsr
-    _ == _                                           = False
+    MerkleizedCase{}       == _                      = False
 
 
 instance Eq Contract where
     {-# INLINABLE (==) #-}
     Close == Close = True
+    Close == _ = False
     Pay acc1 payee1 tok1 value1 cont1 == Pay acc2 payee2 tok2 value2 cont2 =
         acc1 == acc2 && payee1 == payee2 && tok1 == tok2 && value1 == value2 && cont1 == cont2
+    Pay{} == _ = False
     If obs1 cont1 cont2 == If obs2 cont3 cont4 =
         obs1 == obs2 && cont1 == cont3 && cont2 == cont4
-    When cases1 timeout1 cont1 == When cases2 timeout2 cont2 =
+    If{} == _ = False
+    When cases1 timeout1 cont1 == When cases2 timeout2 cont2 =  -- The sequences of tests are ordered for efficiency.
         timeout1 == timeout2 && cont1 == cont2
         && length cases1 == length cases2
         && and (zipWith (==) cases1 cases2)
+    When{} == _ = False
     Let valId1 val1 cont1 == Let valId2 val2 cont2 =
         valId1 == valId2 && val1 == val2 && cont1 == cont2
+    Let{} == _ = False
     Assert obs1 cont1 == Assert obs2 cont2 = obs1 == obs2 && cont1 == cont2
-    _ == _ = False
+    Assert{}  == _ = False
 
 
 instance Eq State where
diff --git a/marlowe/src/Language/Marlowe/Scripts.hs b/marlowe/src/Language/Marlowe/Scripts.hs
index 6027202b5..aa397d5fa 100644
--- a/marlowe/src/Language/Marlowe/Scripts.hs
+++ b/marlowe/src/Language/Marlowe/Scripts.hs
@@ -47,7 +47,9 @@ module Language.Marlowe.Scripts
   , alternateMarloweValidator
   , alternateMarloweValidatorHash
   , marloweValidator
+  , marloweValidatorCompiled
   , marloweValidatorHash
+  , mkMarloweValidator
     -- * Payout Validator
   , TypedRolePayoutValidator
   , rolePayoutValidator
@@ -61,8 +63,9 @@ import GHC.Generics (Generic)
 import Language.Marlowe.Core.V1.Semantics as Semantics
 import Language.Marlowe.Core.V1.Semantics.Types as Semantics
 import Language.Marlowe.Pretty (Pretty(..))
+import Ledger.Typed.Scripts (unsafeMkTypedValidator)
 import qualified Plutus.Script.Utils.Typed as Scripts
-import Plutus.Script.Utils.V2.Typed.Scripts (mkTypedValidator, mkUntypedValidator)
+import Plutus.Script.Utils.V2.Typed.Scripts (mkTypedValidator)
 import qualified Plutus.Script.Utils.V2.Typed.Scripts as Scripts
 import qualified Plutus.V1.Ledger.Address as Address (scriptHashAddress)
 import qualified Plutus.V1.Ledger.Value as Val
@@ -92,11 +95,22 @@ import PlutusTx (makeIsDataIndexed, makeLift)
 import qualified PlutusTx
 import qualified PlutusTx.AssocMap as AssocMap
 import PlutusTx.Plugin ()
-import PlutusTx.Prelude as PlutusTxPrelude
+import PlutusTx.Prelude as PlutusTxPrelude hiding (traceError, traceIfFalse)
 import qualified Prelude as Haskell
 import Unsafe.Coerce (unsafeCoerce)
 
 
+-- Suppress traces, in order to save bytes.
+
+{-# INLINABLE traceError #-}
+traceError :: BuiltinString -> a
+traceError _ = error ()
+
+{-# INLINABLE traceIfFalse #-}
+traceIfFalse :: BuiltinString -> a -> a
+traceIfFalse _ = id
+
+
 -- | Input to a Marlowe transaction.
 type MarloweInput = [MarloweTxInput]
 
@@ -136,7 +150,7 @@ rolePayoutValidator = mkTypedValidator @TypedRolePayoutValidator
   $$(PlutusTx.compile [|| mkRolePayoutValidator ||])
   $$(PlutusTx.compile [|| wrap ||])
   where
-    wrap = Scripts.mkUntypedValidator @(CurrencySymbol, TokenName) @()
+    wrap = Scripts.mkUntypedValidator @_ @(CurrencySymbol, TokenName) @()
 
 
 {-# INLINABLE rolePayoutValidator #-}
@@ -147,7 +161,7 @@ mkRolePayoutValidator :: (CurrencySymbol, TokenName)  -- ^ The datum is the curr
                       -> Bool                         -- ^ Whether the transaction validated.
 mkRolePayoutValidator (currency, role) _ ctx =
     -- The role token for the correct currency must be present.
-    -- [Marlowe-Cardano Specification: "16. Payment authorized".]
+    -- [Marlowe-Cardano Specification: "17. Payment authorized".]
     Val.singleton currency role 1 `Val.leq` valueSpent (scriptContextTxInfo ctx)
 
 
@@ -188,12 +202,10 @@ mkMarloweValidator
             case closeInterval $ txInfoValidRange scriptContextTxInfo of
                 Just interval' -> interval'
                 Nothing        -> traceError "a"
-    -- The incoming balance of each account must be positive.
-    -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
-    let positiveBalances = traceIfFalse "b" $ validateBalances marloweState
 
     -- Find Contract continuation in TxInfo datums by hash or fail with error.
     let inputs = fmap marloweTxInputToInput marloweTxInputs
+
     {-  We do not check that a transaction contains exact input payments.
         We only require an evidence from a party, e.g. a signature for PubKey party,
         or a spend of a 'party role' token.  This gives huge flexibility by allowing
@@ -201,22 +213,19 @@ mkMarloweValidator
         Then, we check scriptOutput to be correct.
      -}
     let inputContents = fmap getInputContent inputs
+
     -- Check that the required signatures and role tokens are present.
     -- [Marlowe-Cardano Specification: "Constraint 14. Inputs authorized".]
-    let inputsOk = validateInputs inputContents
-
-    -- Since individual balances were validated to be positive,
-    -- the total balance is also positive.
-    let inputBalance = totalBalance (accounts marloweState)
+    let inputsOk = allInputsAreAuthorized inputContents
 
     -- [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
-    -- The total incoming balance must match the actual script value being spent.
-    let balancesOk = traceIfFalse "v" $ inputBalance == scriptInValue
-
-    let preconditionsOk = positiveBalances && balancesOk
+    -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
+    -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
+    -- Check that the initial state obeys the Semantic's invariants.
+    let preconditionsOk = checkState "i" scriptInValue marloweState
 
-    -- Package the inputs to be applied in the semantics.
     -- [Marlowe-Cardano Specification: "Constraint 0. Input to semantics".]
+    -- Package the inputs to be applied in the semantics.
     let txInput = TransactionInput {
             txInterval = interval,
             txInputs = inputs }
@@ -246,16 +255,25 @@ mkMarloweValidator
 
                 checkContinuation = case txOutContract of
                     -- [Marlowe-Cardano Specification: "Constraint 4. No output to script on close".]
-                    Close -> traceIfFalse "c" checkScriptOutputAny
+                    Close -> traceIfFalse "c" hasNoOutputToOwnScript
                     _ -> let
                         totalIncome = foldMap collectDeposits inputContents
                         totalPayouts = foldMap snd payoutsByParty
-                        finalBalance = inputBalance + totalIncome - totalPayouts
-                        -- The total account balance must be paid to a single output to the script.
-                        -- [Marlowe-Cardano Specification: "Constraint 3. Single Marlowe output".]
-                        -- [Marlowe-Cardano Specification: "Constraint 6. Output value to script."]
-                        in checkOwnOutputConstraint marloweData finalBalance
+                        finalBalance = scriptInValue + totalIncome - totalPayouts
+                        in
+                             -- [Marlowe-Cardano Specification: "Constraint 3. Single Marlowe output".]
+                             -- [Marlowe-Cardano Specification: "Constraint 6. Output value to script."]
+                             -- Check that the single Marlowe output has the correct datum and value.
+                             checkOwnOutputConstraint marloweData finalBalance
+                             -- [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
+                             -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
+                             -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
+                             -- Check that the final state obeys the Semantic's invariants.
+                          && checkState "o" finalBalance txOutState
             preconditionsOk && inputsOk && payoutsOk && checkContinuation
+              -- [Marlowe-Cardano Specification: "20. Single satsifaction".]
+              -- Either there must be no payouts, or there must be no other validators.
+              && traceIfFalse "z" (null payoutsByParty || noOthers)
         Error TEAmbiguousTimeIntervalError -> traceError "i"
         Error TEApplyNoMatchError -> traceError "n"
         Error (TEIntervalError (InvalidInterval _)) -> traceError "j"
@@ -274,24 +292,73 @@ mkMarloweValidator
         find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
     findOwnInput _ = Nothing
 
-    -- The inputs being spent by this script.
     -- [Marlowe-Cardano Specification: "2. Single Marlowe script input".]
+    -- The inputs being spent by this script, and whether other validators are present.
     ownInput :: TxInInfo
-    ownInput@TxInInfo{txInInfoResolved=TxOut{txOutAddress=ownAddress}} =
+    noOthers :: Bool
+    (ownInput@TxInInfo{txInInfoResolved=TxOut{txOutAddress=ownAddress}}, noOthers) =
         case findOwnInput ctx of
-            Just ownTxInInfo ->
-                case filter (sameValidatorHash ownTxInInfo) (txInfoInputs scriptContextTxInfo) of
-                    [i] -> i
-                    _   -> traceError "w" -- Multiple Marlowe contract inputs with the same address are forbidden.
+            Just ownTxInInfo -> examineScripts (sameValidatorHash ownTxInInfo) Nothing True (txInfoInputs scriptContextTxInfo)
             _ -> traceError "x" -- Input to be validated was not found.
 
+    -- Check for the presence of multiple Marlowe validators or other Plutus validators.
+    examineScripts
+      :: (ValidatorHash -> Bool)  -- Test for this validator.
+      -> Maybe TxInInfo           -- The input for this validator, if found so far.
+      -> Bool                     -- Whether no other validator has been found so far.
+      -> [TxInInfo]               -- The inputs remaining to be examined.
+      -> (TxInInfo, Bool)         -- The input for this validator and whehter no other validators are present.
+    -- This validator has not been found.
+    examineScripts _ Nothing _ [] = traceError "x"
+    -- This validator has been found, and other validators may have been found.
+    examineScripts _ (Just self) noOthers [] = (self, noOthers)
+    -- Found both this validator and another script, so we short-cut.
+    examineScripts _ (Just self) False _ = (self, False)
+     -- Found one script.
+    examineScripts f mSelf noOthers (tx@TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh) _}} : txs)
+      -- The script is this validator.
+      | f vh = case mSelf of
+                 -- We hadn't found it before, so we save it in `mSelf`.
+                 Nothing -> examineScripts f (Just tx) noOthers txs
+                 -- We already had found this validator before
+                 Just _ -> traceError "w"
+      -- The script is something else, so we set `noOther` to `False`.
+      | otherwise = examineScripts f mSelf False txs
+    -- An input without a validator is encountered.
+    examineScripts f self others (_ : txs) = examineScripts f self others txs
+
     -- Check if inputs are being spent from the same script.
-    sameValidatorHash:: TxInInfo -> TxInInfo -> Bool
-    sameValidatorHash
-        TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh1) _}}
-        TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh2) _}} = vh1 == vh2
+    sameValidatorHash:: TxInInfo -> ValidatorHash -> Bool
+    sameValidatorHash TxInInfo{txInInfoResolved=TxOut{txOutAddress=Ledger.Address (ScriptCredential vh1) _}} vh2 = vh1 == vh2
     sameValidatorHash _ _ = False
 
+    -- Check a state for the correct value, positive accounts, and no duplicates.
+    checkState :: BuiltinString -> Val.Value -> State -> Bool
+    checkState tag expected State{..} =
+      let
+        positiveBalance :: (a, Integer) -> Bool
+        positiveBalance (_, balance) = balance > 0
+        noDuplicates :: Eq k => AssocMap.Map k v -> Bool
+        noDuplicates am =
+          let
+            test [] = True           -- An empty list has no duplicates.
+            test (x : xs)            -- Look for a duplicate of the head in the tail.
+              | elem x xs = False    -- A duplicate is present.
+              | otherwise = test xs  -- Continue searching for a duplicate.
+          in
+            test $ AssocMap.keys am
+      in
+           -- [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
+           -- and/or
+           -- [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
+           traceIfFalse ("v"  <> tag) (totalBalance accounts == expected)
+           -- [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
+        && traceIfFalse ("b"  <> tag) (all positiveBalance $ AssocMap.toList accounts)
+           -- [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
+        && traceIfFalse ("ea" <> tag) (noDuplicates accounts)
+        && traceIfFalse ("ec" <> tag) (noDuplicates choices)
+        && traceIfFalse ("eb" <> tag) (noDuplicates boundValues)
+
     -- Look up the Datum hash for specific data.
     findDatumHash' :: PlutusTx.ToData o => o -> Maybe DatumHash
     findDatumHash' datum = findDatumHash (Datum $ PlutusTx.toBuiltinData datum) scriptContextTxInfo
@@ -301,7 +368,7 @@ mkMarloweValidator
     checkOwnOutputConstraint ocDatum ocValue =
         let hsh = findDatumHash' ocDatum
         in traceIfFalse "d" -- "Output constraint"
-        $ checkScriptOutput ownAddress hsh ocValue getContinuingOutput
+        $ checkScriptOutput (==) ownAddress hsh ocValue getContinuingOutput
 
     getContinuingOutput :: TxOut
     getContinuingOutput = case filter (\TxOut{txOutAddress} -> ownAddress == txOutAddress) allOutputs of
@@ -309,20 +376,14 @@ mkMarloweValidator
         _     -> traceError "o" -- No continuation or multiple Marlowe contract outputs is forbidden.
 
     -- Check that address, value, and datum match the specified.
-    checkScriptOutput :: Ledger.Address -> Maybe DatumHash -> Val.Value -> TxOut -> Bool
-    checkScriptOutput addr hsh value TxOut{txOutAddress, txOutValue, txOutDatum=OutputDatumHash svh} =
-                    txOutValue == value && hsh == Just svh && txOutAddress == addr
-    checkScriptOutput _ _ _ _ = False
-
-    -- Check that address and datum match the specified, and that value is at least that required.
-    checkScriptOutputRelaxed :: Ledger.Address -> Maybe DatumHash -> Val.Value -> TxOut -> Bool
-    checkScriptOutputRelaxed addr hsh value TxOut{txOutAddress, txOutValue, txOutDatum=OutputDatumHash svh} =
-                    txOutValue `Val.geq` value && hsh == Just svh && txOutAddress == addr
-    checkScriptOutputRelaxed _ _ _ _ = False
+    checkScriptOutput :: (Val.Value -> Val.Value -> Bool) -> Ledger.Address -> Maybe DatumHash -> Val.Value -> TxOut -> Bool
+    checkScriptOutput comparison addr hsh value TxOut{txOutAddress, txOutValue, txOutDatum=OutputDatumHash svh} =
+                    txOutValue `comparison` value && hsh == Just svh && txOutAddress == addr
+    checkScriptOutput _ _ _ _ _ = False
 
     -- Check for any output to the script address.
-    checkScriptOutputAny :: Bool
-    checkScriptOutputAny = all ((/= ownAddress) . txOutAddress) allOutputs
+    hasNoOutputToOwnScript :: Bool
+    hasNoOutputToOwnScript = all ((/= ownAddress) . txOutAddress) allOutputs
 
     -- All of the script outputs.
     allOutputs :: [TxOut]
@@ -339,8 +400,8 @@ mkMarloweValidator
     marloweTxInputToInput (Input input) = NormalInput input
 
     -- Check that inputs are authorized.
-    validateInputs :: [InputContent] -> Bool
-    validateInputs = all validateInputWitness
+    allInputsAreAuthorized :: [InputContent] -> Bool
+    allInputsAreAuthorized = all validateInputWitness
       where
         validateInputWitness :: InputContent -> Bool
         validateInputWitness input =
@@ -356,8 +417,10 @@ mkMarloweValidator
 
     -- Tally the deposits in the input.
     collectDeposits :: InputContent -> Val.Value
-    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
-    collectDeposits _                                     = zero
+    collectDeposits (IDeposit _ _ (Token cur tok) amount)
+      | amount > 0    = Val.singleton cur tok amount  -- SCP-5123: Semantically negative deposits
+      | otherwise     = zero                          -- do not remove funds from the script's UTxO.
+    collectDeposits _ = zero
 
     -- Extract the payout to a party.
     payoutByParty :: Payment -> AssocMap.Map Party Val.Value
@@ -374,12 +437,17 @@ mkMarloweValidator
       where
         payoutToTxOut :: (Party, Val.Value) -> Bool
         payoutToTxOut (party, value) = case party of
+            -- [Marlowe-Cardano Specification: "Constraint 15. Sufficient Payment".]
+            -- SCP-5128: Note that the payment to an address may be split into several outputs but the payment to a role must be
+            -- a single output. The flexibily of multiple outputs accommodates wallet-related practicalities such as the change and
+            -- the return of the role token being in separate UTxOs in situations where a contract is also paying to the address
+            -- where that change and that role token are sent.
             Address _ address  -> traceIfFalse "p" $ value `Val.leq` valuePaidToAddress address  -- At least sufficient value paid.
             Role role -> let
                 hsh = findDatumHash' (rolesCurrency, role)
                 addr = Address.scriptHashAddress rolePayoutValidatorHash
                 -- Some output must have the correct value and datum to the role-payout address.
-                in traceIfFalse "r" $ any (checkScriptOutputRelaxed addr hsh value) allOutputs
+                in traceIfFalse "r" $ any (checkScriptOutput Val.geq addr hsh value) allOutputs
 
     -- The key for the address must have signed.
     txSignedByAddress :: Ledger.Address -> Bool
@@ -402,7 +470,7 @@ marloweValidator :: Scripts.TypedValidator TypedMarloweValidator
 marloweValidator =
   let
     mkUntypedMarloweValidator :: ValidatorHash -> BuiltinData -> BuiltinData -> BuiltinData -> ()
-    mkUntypedMarloweValidator rp = mkUntypedValidator (mkMarloweValidator rp)
+    mkUntypedMarloweValidator rp = Scripts.mkUntypedValidator (mkMarloweValidator rp)
 
     untypedValidator :: Scripts.Validator
     untypedValidator = mkValidatorScript $
@@ -410,10 +478,20 @@ marloweValidator =
         `PlutusTx.applyCode` PlutusTx.liftCode rolePayoutValidatorHash
 
     typedValidator :: Scripts.TypedValidator Scripts.Any
-    typedValidator = Scripts.unsafeMkTypedValidator untypedValidator
+    typedValidator = unsafeMkTypedValidator (Scripts.Versioned untypedValidator Scripts.PlutusV2)
   in
     unsafeCoerce typedValidator
 
+
+marloweValidatorCompiled :: PlutusTx.CompiledCode (ValidatorHash -> PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> ())
+marloweValidatorCompiled =
+  let
+    mkUntypedMarloweValidator :: ValidatorHash -> PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> PlutusTx.BuiltinData -> ()
+    mkUntypedMarloweValidator rp = Scripts.mkUntypedValidator (mkMarloweValidator rp)
+  in
+    $$(PlutusTx.compile [|| mkUntypedMarloweValidator ||])
+
+
 -- | The hash of the Marlowe semantics validator.
 marloweValidatorHash :: ValidatorHash
 marloweValidatorHash = Scripts.validatorHash marloweValidator
@@ -432,7 +510,7 @@ alternateMarloweValidator = Scripts.mkTypedValidator
           $$(PlutusTx.compile [|| mkMarloweValidator ||])
             `PlutusTx.applyCode`
               PlutusTx.liftCode rolePayoutValidatorHash
-        mkArgsValidator = mkUntypedValidator @MarloweData @MarloweInput
+        mkArgsValidator = Scripts.mkUntypedValidator @_ @MarloweData @MarloweInput
         compiledArgsValidator =
           $$(PlutusTx.compile [|| mkArgsValidator ||])
```


### Post-Audit Changes in Property-Based Tests for Marlowe Validator

```bash
git diff 523f3d56f22bf992ddb0b0c8a52bb7a5a188f9e9 69468d6623e24a4ccd6659e378ae012c38ca01ce marlowe-test/src/
```

```diff
diff --git a/marlowe-test/src/Data/Jsonable.hs b/marlowe-test/src/Data/Jsonable.hs
new file mode 100644
index 000000000..b16e3e044
--- /dev/null
+++ b/marlowe-test/src/Data/Jsonable.hs
@@ -0,0 +1,126 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Wrapping values that can be converted to and from JSON.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE ExistentialQuantification #-}
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
+{-# LANGUAGE ScopedTypeVariables #-}
+
+
+module Data.Jsonable
+  ( -- * Types
+    Jsonable(..)
+  , JsonableType(..)
+  , KnownJsonable
+    -- * Conversion
+  , fromJsonable
+  , isKnownJson
+  , toJsonable
+    -- * Testing
+  , arbitraryJsonable
+  , checkRoundTripJsonable
+  , generateJsonable
+  , roundTripJsonable
+  ) where
+
+
+import Data.Aeson (FromJSON(..), Result(..), ToJSON(..), Value, fromJSON)
+import Data.Proxy (Proxy(..))
+import Test.Tasty.QuickCheck (Arbitrary(..), Gen)
+
+
+-- | A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+type KnownJsonable = [JsonableType]
+
+
+-- | A type with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+data JsonableType = forall a. (ToJSON a, FromJSON a, Arbitrary a) => JsonableType {typeKey :: String, typeValue :: Proxy a}
+
+
+-- | A value with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+data Jsonable = forall a . (ToJSON a, FromJSON a, Arbitrary a) => Jsonable {jsonableType :: String, jsonableValue :: a}
+
+
+-- | Deserialize a JSON value.
+toJsonable
+  :: KnownJsonable  -- ^ A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+  -> String   -- ^ The key for the type.
+  -> Value  -- ^ The JSON value.
+  -> Either String Jsonable  -- ^ The deserialized value, or an error message.
+toJsonable known s v =
+  let
+    fromJson' :: forall a . FromJSON a => Proxy a -> Either String a
+    fromJson' _ =
+      case fromJSON v :: Result a of
+        Success x -> Right x
+        Error msg -> Left msg
+  in
+    case filter ((s ==) . typeKey) known of
+      [JsonableType{..}] -> Jsonable typeKey <$> fromJson' typeValue
+      _                  -> Left $ "JSON serialization not supported for " <> s <> "."
+
+
+-- | Check for a known JSON type.
+isKnownJson
+  :: KnownJsonable  -- ^ A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+  -> String   -- ^ The key for the type.
+  -> Bool  -- ^ Whether the type is in the list of known JSON types.
+isKnownJson known s = length (filter ((s ==) . typeKey) known) == 1
+
+
+-- | Serialize a JSON value.
+fromJsonable
+  :: Jsonable  -- ^ The value.
+  -> Value  -- ^ The JSON.
+fromJsonable Jsonable{..} = toJSON jsonableValue
+
+
+-- | Peform round-trip deserialization and serialization of a JSON value.
+roundTripJsonable
+  :: KnownJsonable  -- ^ A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+  -> String  -- ^ The key for the type.
+  -> Value  -- ^ The JSON value.
+  -> Either String Value  -- ^ There the re-serialized value, or an error message.
+roundTripJsonable known = (fmap fromJsonable .) . toJsonable known
+
+
+-- | Check that round-trip re-serialization doesn't alter a JSON value.
+checkRoundTripJsonable
+  :: KnownJsonable  -- ^ A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+  -> String  -- ^ The key for the type.
+  -> Value  -- ^ The JSON value.
+  -> Bool  -- ^ Whether the JSON value is unchanged.
+checkRoundTripJsonable known s v = roundTripJsonable known s v == Right v
+
+
+-- | Generate an arbitrary value.
+arbitraryJsonable
+  :: JsonableType  -- ^ The type to generate.
+  -> Gen Jsonable  -- ^ The generator.
+arbitraryJsonable JsonableType{..} =
+  let
+    gen :: Arbitrary a => Proxy a -> Gen a
+    gen _ = arbitrary
+  in
+    Jsonable typeKey <$> gen typeValue
+
+
+-- | Generate an arbitrary value.
+generateJsonable
+  :: KnownJsonable  -- ^ A list of known types with `FromJSON`, `ToJSON`, and `Arbitrary` instances.
+  -> String  -- ^ The key for the type.
+  -> Either String (Gen Value)  -- ^ The JSON value.
+generateJsonable known s =
+  case filter ((s ==) . typeKey) known of
+    [jt] -> Right . fmap fromJsonable $ arbitraryJsonable jt
+    _    -> Left $ "JSON serialization not supported for " <> s <> "."
diff --git a/marlowe-test/src/Spec/Marlowe/Common.hs b/marlowe-test/src/Spec/Marlowe/Common.hs
index f52715b5f..77f7ef7cd 100644
--- a/marlowe-test/src/Spec/Marlowe/Common.hs
+++ b/marlowe-test/src/Spec/Marlowe/Common.hs
@@ -12,7 +12,6 @@
 
 
 {-# LANGUAGE DataKinds #-}
-{-# LANGUAGE NamedFieldPuns #-}
 {-# LANGUAGE OverloadedStrings #-}
 {-# LANGUAGE ScopedTypeVariables #-}
 
@@ -490,5 +489,3 @@ pangramContract = let
                 Close)
         , Case (Notify (AndObs (TimeIntervalStart `ValueLT` TimeIntervalEnd) TrueObs)) Close
         ] (Ledger.POSIXTime 100) Close
-
-
diff --git a/marlowe-test/src/Spec/Marlowe/Marlowe.hs b/marlowe-test/src/Spec/Marlowe/Marlowe.hs
index f98e1c899..264b1da93 100644
--- a/marlowe-test/src/Spec/Marlowe/Marlowe.hs
+++ b/marlowe-test/src/Spec/Marlowe/Marlowe.hs
@@ -29,7 +29,6 @@ module Spec.Marlowe.Marlowe
   ) where
 
 
-
 import Control.Exception (SomeException, catch)
 import Control.Monad (when)
 import Data.Aeson (decode, eitherDecode, encode)
@@ -151,14 +150,14 @@ alternateMarloweValidatorSize :: IO ()
 alternateMarloweValidatorSize = do
     let validator = Scripts.validatorScript alternateMarloweValidator
     let vsize = SBS.length . SBS.toShort . LB.toStrict $ Serialise.serialise validator
-    assertBool ("alternateMarloweValidator is too large " <> show vsize) (vsize < 15030)
+    assertBool ("alternateMarloweValidator is too large " <> show vsize) (vsize <= 14821)
 
 -- | Test that the untyped validator is not too large.
 marloweValidatorSize :: IO ()
 marloweValidatorSize = do
     let validator = Scripts.validatorScript marloweValidator
     let vsize = SBS.length . SBS.toShort . LB.toStrict $ Serialise.serialise validator
-    assertBool ("marloweValidator is too large " <> show vsize) (vsize < 12510)
+    assertBool ("marloweValidator is too large " <> show vsize) (vsize <= 12296)
 
 
 -- | Test `extractNonMerkleizedContractRoles`.
diff --git a/marlowe-test/src/Spec/Marlowe/Plutus.hs b/marlowe-test/src/Spec/Marlowe/Plutus.hs
index f1a44eaea..ccccdf3c1 100644
--- a/marlowe-test/src/Spec/Marlowe/Plutus.hs
+++ b/marlowe-test/src/Spec/Marlowe/Plutus.hs
@@ -17,9 +17,11 @@ module Spec.Marlowe.Plutus
   ) where
 
 
+import Spec.Marlowe.Reference (ReferencePath)
 import Test.Tasty (TestTree, testGroup)
 
 import qualified Spec.Marlowe.Plutus.AssocMap (tests)
+import qualified Spec.Marlowe.Plutus.MList (tests)
 import qualified Spec.Marlowe.Plutus.Prelude (tests)
 import qualified Spec.Marlowe.Plutus.ScriptContext (tests)
 import qualified Spec.Marlowe.Plutus.Specification (tests)
@@ -27,14 +29,14 @@ import qualified Spec.Marlowe.Plutus.Value (tests)
 
 
 -- | Run tests.
-tests :: TestTree
-tests =
+tests :: [ReferencePath] -> TestTree
+tests referencePaths =
   testGroup "Plutus"
     [
       Spec.Marlowe.Plutus.Prelude.tests
     , Spec.Marlowe.Plutus.AssocMap.tests
+    , Spec.Marlowe.Plutus.MList.tests
     , Spec.Marlowe.Plutus.Value.tests
     , Spec.Marlowe.Plutus.ScriptContext.tests
-    , Spec.Marlowe.Plutus.Specification.tests
+    , Spec.Marlowe.Plutus.Specification.tests referencePaths
     ]
-
diff --git a/marlowe-test/src/Spec/Marlowe/Plutus/MList.hs b/marlowe-test/src/Spec/Marlowe/Plutus/MList.hs
new file mode 100644
index 000000000..7edb3424e
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Plutus/MList.hs
@@ -0,0 +1,312 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Compare the `PlutusTx.AssocMap` to Isabelle's `MList`.
+--
+-----------------------------------------------------------------------------
+
+
+module Spec.Marlowe.Plutus.MList
+  ( -- * Testing
+    tests
+  ) where
+
+
+import Data.Function (on)
+import Data.List (nubBy, sortBy)
+import Data.Maybe (fromMaybe, isJust)
+import Prelude hiding (lookup)
+import Test.Tasty (TestTree, testGroup)
+import Test.Tasty.HUnit (Assertion, assertBool, testCase)
+import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property, elements, forAll, property, testProperty)
+
+import qualified PlutusTx.AssocMap as AM
+  (Map, delete, empty, fromList, insert, lookup, member, null, singleton, toList, unionWith)
+import qualified PlutusTx.Eq as P (Eq)
+
+
+-- | An association list in Isabelle.
+type MList a b = [(a, b)]
+
+
+-- | Empty Isabelle `MList`.
+--
+-- @
+-- definition empty :: "('a::linorder \<times> 'b) list" where
+--   "empty = Nil"
+-- @
+empty :: MList a b
+empty = []
+
+
+{-# ANN insert "HLint: ignore Use guards" #-}
+{-# ANN insert "HLint: ignore Use list literal" #-}
+
+-- | Insert into Isabelle `MList`.
+--
+-- @
+-- fun insert :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
+--   "insert a b Nil = Cons (a, b) Nil" |
+--   "insert a b (Cons (x, y) z) =
+--     (if a < x
+--      then (Cons (a, b) (Cons (x, y) z))
+--      else (if a > x
+--            then (Cons (x, y) (insert a b z))
+--            else (Cons (x, b) z)))"
+-- @
+insert :: Ord a => a -> b -> MList a b -> MList a b
+insert a b [] = (a, b) : []
+insert a b ((x, y) : z) =
+  if a < x
+    then (a, b) : (x, y) : z
+    else if a > x
+      then (x, y) : insert a b z
+      else (x, b) : z
+
+
+{-# ANN delete "HLint: ignore Use guards" #-}
+
+-- | Delete from Isabelle `MList`.
+--
+-- @
+-- fun delete :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
+--   "delete a Nil = Nil" |
+--   "delete a (Cons (x, y) z) =
+--     (if a = x
+--      then z
+--      else (if a > x
+--            then (Cons (x, y) (delete a z))
+--            else (Cons (x, y) z)))"
+-- @
+delete :: Ord a => a -> MList a b -> MList a b
+delete _a [] = []
+delete a ((x, y) : z) =
+  if a == x
+    then z
+    else if a > x
+      then (x, y) : delete a z
+      else (x, y) : z
+
+
+{-# ANN lookup "HLint: ignore Use guards" #-}
+
+-- | Lookup in Isabelle `MList`.
+--
+-- @
+-- fun lookup :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
+--   "lookup a Nil = None" |
+--   "lookup a (Cons (x, y) z) =
+--     (if a = x
+--      then Some y
+--      else (if a > x
+--            then lookup a z
+--            else None))"
+-- @
+lookup :: Ord a => a -> MList a b -> Maybe b
+lookup _a [] = Nothing
+lookup a ((x, y) : z) =
+  if a == x
+    then Just y
+    else if a > x
+      then lookup a z
+      else Nothing
+
+
+{-# ANN unionWith "HLint: ignore Use guards" #-}
+
+-- | Union with Isabelle `MList`.
+--
+-- @
+-- fun unionWith :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow>
+--                   ('a \<times> 'b) list \<Rightarrow> (('a::linorder) \<times> 'b) list" where
+--   "unionWith f (Cons (x, y) t) (Cons (x2, y2) t2) =
+--     (if x < x2
+--      then Cons (x, y) (unionWith f t (Cons (x2, y2) t2))
+--      else (if x > x2
+--            then Cons (x2, y2) (unionWith f (Cons (x, y) t) t2)
+--            else Cons (x, f y y2) (unionWith f t t2)))" |
+--   "unionWith f Nil l = l" |
+--   "unionWith f l Nil = l"
+-- @
+unionWith :: Ord a => (b -> b -> b) -> MList a b -> MList a b -> MList a b
+unionWith f ((x, y) : t) ((x2, y2) : t2) =
+  if x < x2
+    then (x, y) : unionWith f t ((x2, y2) : t2)
+    else if x > x2
+      then (x2, y2) : unionWith f ((x, y) : t) t2
+      else (x, f y y2) : unionWith f t t2
+unionWith _f [] l = l
+unionWith _f l [] = l
+
+
+-- | Find with default for Isabelle `MList`.
+--
+-- @
+-- fun findWithDefault :: "'b \<Rightarrow> 'a \<Rightarrow> (('a::linorder) \<times> 'b) list \<Rightarrow> 'b" where
+--   "findWithDefault d k l = (case lookup k l of
+--                               None \<Rightarrow> d
+--                             | Some x \<Rightarrow> x)"
+-- @
+findWithDefault :: Ord a => b -> a -> MList a b -> b
+findWithDefault d k l =
+  case lookup k l of
+    Nothing -> d
+    Just x -> x
+
+
+-- | Run tests.
+tests :: TestTree
+tests =
+  testGroup "MList vs AssocMap"
+    [
+      testCase     "`empty` is equivalent"           checkEmpty
+    , testProperty "`null` is equivalent"            checkNull
+    , testProperty "`singleton` is equivalent"       checkSingleton
+    , testProperty "`insert` is equivalent"          checkInsert
+    , testProperty "`delete` is equivalent"          checkDelete
+    , testProperty "`lookup` is equivalent"          checkLookup
+    , testProperty "`member` is equivalent"          checkMember
+    , testProperty "`unionWith` is equivalent"       checkUnionWith
+    , testProperty "`findWithDefault` is equivalent" checkFindWithDefault
+    ]
+
+
+-- | Key type for testing.
+type Key = Integer
+
+
+-- | Value type for testing.
+type Value = [()]
+
+
+-- | Generate a sorted `MList` with no duplicate keys.
+arbitraryMList :: Gen (MList Key Value, AM.Map Key Value)
+arbitraryMList =
+  do
+    items <- nubBy ((==) `on` fst) <$> arbitrary
+    pure (sortBy (compare `on` fst) items, AM.fromList items)
+
+
+-- | Compare an `MList` to an `AssocMap`, ignoring ordering.
+equivalent :: Ord a => P.Eq a => Eq b => MList a b -> AM.Map a b -> Bool
+equivalent mlist assocmap =
+  mlist == sortBy (compare `on` fst) (AM.toList assocmap)
+    && and [AM.lookup a assocmap == Just b | (a, b) <- mlist]
+    && and [lookup a mlist == Just b | (a, b) <- AM.toList assocmap]
+
+
+-- | Compare `empty` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkEmpty :: Assertion
+checkEmpty = assertBool "Empty MList and AssocMap" $ (empty :: MList Key Value) `equivalent` AM.empty
+
+
+-- | Compare `null` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkNull :: Property
+checkNull = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      pure (mlist, assocmap)
+  forAll gen
+    $ \(mlist, assocmap) -> (== empty) mlist == AM.null assocmap
+
+
+-- | Compare `singleton` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkSingleton :: Property
+checkSingleton = property $ do
+  let
+    gen = do
+      a <- arbitrary :: Gen Key
+      b <- arbitrary :: Gen Value
+      pure (a, b)
+  forAll gen
+    $ \(a, b) -> [(a, b)] `equivalent` AM.singleton a b
+
+
+-- | Compare `insert` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkInsert :: Property
+checkInsert = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      a <- arbitrary
+      b <- arbitrary
+      pure (mlist, assocmap, a, b)
+  forAll gen
+    $ \(mlist, assocmap, a, b) -> insert a b mlist `equivalent` AM.insert a b assocmap
+
+
+-- | Compare `delete` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkDelete :: Property
+checkDelete = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      a <- arbitrary
+      pure (mlist, assocmap, a)
+  forAll gen
+    $ \(mlist, assocmap, a) -> delete a mlist `equivalent` AM.delete a assocmap
+
+
+-- | Compare `lookup` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkLookup :: Property
+checkLookup = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      a <- arbitrary
+      pure (mlist, assocmap, a)
+  forAll gen
+    $ \(mlist, assocmap, a) -> lookup a mlist == AM.lookup a assocmap
+
+
+-- | Compare `member` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkMember :: Property
+checkMember = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      a <- arbitrary
+      pure (mlist, assocmap, a)
+  forAll gen
+    $ \(mlist, assocmap, a) -> isJust (lookup a mlist) == AM.member a assocmap
+
+
+-- | Compare `unionWith` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkUnionWith :: Property
+checkUnionWith = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      (mlist', assocmap') <- arbitraryMList
+      function <- elements ["concat", "shortest", "longest", "first", "second"]
+      pure (mlist, assocmap, mlist', assocmap', function)
+  forAll gen
+    $ \(mlist, assocmap, mlist', assocmap', function) ->
+      let
+        f = case function of
+              "shortest" -> \x y -> if length x < length y then x else y
+              "longest"  -> \x y -> if length x > length y then x else y
+              "first"    -> const
+              "second"   -> const id
+              _          -> (<>)
+      in
+        unionWith f mlist mlist' `equivalent` AM.unionWith f assocmap assocmap'
+
+
+-- | Compare `findWithDefault` for `MList` and `AssocMap`, provided the `MList` is sorted and neither contains duplicate keys.
+checkFindWithDefault :: Property
+checkFindWithDefault = property $ do
+  let
+    gen = do
+      (mlist, assocmap) <- arbitraryMList
+      a <- arbitrary
+      b <- arbitrary
+      pure (mlist, assocmap, a, b)
+  forAll gen
+    $ \(mlist, assocmap, a, b) -> findWithDefault b a mlist == fromMaybe b (AM.lookup a assocmap)
diff --git a/marlowe-test/src/Spec/Marlowe/Plutus/Script.hs b/marlowe-test/src/Spec/Marlowe/Plutus/Script.hs
index ccfab1c9a..9ced8d81e 100644
--- a/marlowe-test/src/Spec/Marlowe/Plutus/Script.hs
+++ b/marlowe-test/src/Spec/Marlowe/Plutus/Script.hs
@@ -11,7 +11,9 @@
 -----------------------------------------------------------------------------
 
 
+{-# LANGUAGE NumericUnderscores #-}
 {-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
 
 
 module Spec.Marlowe.Plutus.Script
@@ -53,6 +55,7 @@ import Plutus.V2.Ledger.Api
   , Data
   , Datum(Datum)
   , DatumHash
+  , ExBudget(..)
   , ToData(toBuiltinData)
   , TokenName
   , Validator(getValidator)
@@ -64,6 +67,11 @@ import qualified Data.ByteString.Short as SBS (ShortByteString, toShort)
 import qualified Data.Map.Strict as M (fromList)
 
 
+-- | Check the Plutus execution budget.
+enforceBudget :: Bool
+enforceBudget = False
+
+
 -- | Run the Plutus evaluator on the Marlowe semantics validator.
 evaluateSemantics :: Data                    -- ^ The datum.
                   -> Data                    -- ^ The redeemer.
@@ -72,9 +80,11 @@ evaluateSemantics :: Data                    -- ^ The datum.
 evaluateSemantics datum redeemer context =
   case evaluationContext of
     Left message -> This message
-    Right ec     -> case evaluateScriptCounting PlutusV2 (ProtocolVersion 7 0) Verbose ec serialiseSemanticsValidator [datum, redeemer, context] of
-                      (logOutput, Right _     ) -> That logOutput
-                      (logOutput, Left message) -> These (show message) logOutput
+    Right ec     -> case evaluateScriptCounting PlutusV2 (ProtocolVersion 8 0) Verbose ec serialiseSemanticsValidator [datum, redeemer, context] of
+                      (logOutput, Right ex@ExBudget{..}) -> if enforceBudget && (exBudgetCPU > 10_000_000_000 || exBudgetMemory > 14_000_000)
+                                                              then These ("Exceeded Plutus budget: " <> show ex) logOutput
+                                                              else That logOutput
+                      (logOutput, Left message         ) -> These (show message) logOutput
 
 
 -- | Run the Plutus evaluator on the Marlowe payout validator.
@@ -321,12 +331,12 @@ costModel =
     , ("unListData-memory-arguments", 32)
     , ("unMapData-cpu-arguments", 38314)
     , ("unMapData-memory-arguments", 32)
-    , ("verifyEcdsaSecp256k1Signature-cpu-arguments", 20000000000)
-    , ("verifyEcdsaSecp256k1Signature-memory-arguments", 20000000000)
-    , ("verifyEd25519Signature-cpu-arguments-intercept", 9462713)
-    , ("verifyEd25519Signature-cpu-arguments-slope", 1021)
+    , ("verifyEcdsaSecp256k1Signature-cpu-arguments", 35892428)
+    , ("verifyEcdsaSecp256k1Signature-memory-arguments", 10)
+    , ("verifyEd25519Signature-cpu-arguments-intercept", 57996947)
+    , ("verifyEd25519Signature-cpu-arguments-slope", 18975)
     , ("verifyEd25519Signature-memory-arguments", 10)
-    , ("verifySchnorrSecp256k1Signature-cpu-arguments-intercept", 20000000000)
-    , ("verifySchnorrSecp256k1Signature-cpu-arguments-slope", 0)
-    , ("verifySchnorrSecp256k1Signature-memory-arguments", 20000000000)
+    , ("verifySchnorrSecp256k1Signature-cpu-arguments-intercept", 38887044)
+    , ("verifySchnorrSecp256k1Signature-cpu-arguments-slope", 32947)
+    , ("verifySchnorrSecp256k1Signature-memory-arguments", 10)
     ]
diff --git a/marlowe-test/src/Spec/Marlowe/Plutus/Specification.hs b/marlowe-test/src/Spec/Marlowe/Plutus/Specification.hs
index e02c42079..fc8d92b8f 100644
--- a/marlowe-test/src/Spec/Marlowe/Plutus/Specification.hs
+++ b/marlowe-test/src/Spec/Marlowe/Plutus/Specification.hs
@@ -23,9 +23,10 @@ module Spec.Marlowe.Plutus.Specification
   ) where
 
 
-import Control.Lens (use, uses, (%=), (<>=), (^.))
+import Control.Lens (use, uses, (%=), (<>=), (<~), (^.))
 import Control.Monad.State (lift)
 import Data.Bifunctor (bimap)
+import Data.List (nub)
 import Data.Maybe (maybeToList)
 import Data.Proxy (Proxy(..))
 import Data.These (These(That, These, This))
@@ -35,6 +36,7 @@ import Language.Marlowe.Core.V1.Semantics
   , Payment(Payment)
   , TransactionInput(..)
   , TransactionOutput(txOutContract, txOutPayments, txOutState)
+  , totalBalance
   )
 import Language.Marlowe.Core.V1.Semantics.Types
   ( ChoiceId(ChoiceId)
@@ -54,7 +56,7 @@ import Plutus.V2.Ledger.Api
   , BuiltinData(BuiltinData)
   , Credential(PubKeyCredential)
   , Data(B, Constr, List)
-  , Datum(Datum)
+  , Datum(..)
   , DatumHash(DatumHash)
   , FromData(..)
   , OutputDatum(..)
@@ -71,12 +73,14 @@ import Plutus.V2.Ledger.Api
   , singleton
   , toData
   )
+import Spec.Marlowe.Plutus.Lens ((<><~))
 import Spec.Marlowe.Plutus.Script
   (evaluatePayout, evaluateSemantics, payoutAddress, payoutScriptHash, semanticsAddress, semanticsScriptHash)
 import Spec.Marlowe.Plutus.Transaction
   ( ArbitraryTransaction
   , arbitraryPayoutTransaction
   , arbitrarySemanticsTransaction
+  , isScriptTxIn
   , merkleize
   , noModify
   , noVeto
@@ -97,26 +101,41 @@ import Spec.Marlowe.Plutus.Types
   , output
   , role
   )
+import Spec.Marlowe.Reference (ReferencePath)
 import Spec.Marlowe.Semantics.Arbitrary (arbitraryPositiveInteger)
 import Test.Tasty (TestTree, testGroup)
-import Test.Tasty.QuickCheck (Arbitrary(..), Gen, Property, forAll, property, suchThat, testProperty, (===))
+import Test.Tasty.QuickCheck
+  ( Arbitrary(..)
+  , Gen
+  , Property
+  , chooseInteger
+  , elements
+  , forAll
+  , listOf1
+  , oneof
+  , property
+  , suchThat
+  , testProperty
+  , (===)
+  )
 
 import qualified Language.Marlowe.Core.V1.Semantics as M (MarloweData(marloweParams))
-import qualified Language.Marlowe.Core.V1.Semantics.Types as M (Party(Address))
-import qualified PlutusTx.AssocMap as AM (fromList, insert, toList)
+import qualified Language.Marlowe.Core.V1.Semantics.Types as M (Party(Address), State(..))
+import qualified PlutusTx.AssocMap as AM (Map, fromList, insert, keys, null, toList)
+import qualified Test.Tasty.QuickCheck as Q (shuffle)
 
 
 -- | Run tests.
-tests :: TestTree
-tests =
+tests :: [ReferencePath] -> TestTree
+tests referencePaths =
   testGroup "Marlowe On-Chain Specification"
     [
       testGroup "Semantics Validator"
         [
           testGroup "Valid transaction succeeds"
             [
-              testProperty "Noiseless" $ checkSemanticsTransaction noModify noModify noVeto True False
-            , testProperty "Noisy"     $ checkSemanticsTransaction noModify noModify noVeto True True
+              testProperty "Noiseless" $ checkSemanticsTransaction referencePaths noModify noModify noVeto True False True
+            , testProperty "Noisy"     $ checkSemanticsTransaction referencePaths noModify noModify noVeto True True  True
             ]
         , testGroup "Constraint 1. Typed validation"
             [
@@ -129,23 +148,23 @@ tests =
             ]
         , testGroup "Constraint 2. Single Marlowe script input"
             [
-              testProperty "Invalid attempt to run two Marlowe scripts" checkDoubleInput
+              testProperty "Invalid attempt to run two Marlowe scripts" $ checkDoubleInput referencePaths
             ]
         , testGroup "Constraint 3. Single Marlowe output"
             [
-              testProperty "Invalid attempt to split Marlowe output" checkMultipleOutput
+              testProperty "Invalid attempt to split Marlowe output" $ checkMultipleOutput referencePaths
             ]
         , testGroup "Constraint 4. No output to script on close"
             [
-              testProperty "Invalid attempt to output to Marlowe on close" checkCloseOutput
+              testProperty "Invalid attempt to output to Marlowe on close" $ checkCloseOutput referencePaths
             ]
         , testGroup "Constraint 5. Input value from script"
             [
-              testProperty "Invalid mismatch between state and script input" checkValueInput
+              testProperty "Invalid mismatch between state and script input" $ checkValueInput referencePaths
             ]
         , testGroup "Constraint 6. Output value to script"
             [
-              testProperty "Invalid mismatch between state and script input" checkValueOutput
+              testProperty "Invalid mismatch between expected and actual output to script" $ checkValueOutput referencePaths
             ]
         , testGroup "Constraint 7. Input state"
             [
@@ -157,39 +176,53 @@ tests =
             ]
         , testGroup "Constraint 9. Marlowe parameters"
             [
-              testProperty "Invalid alteration of parameters." checkParamsOutput
+              testProperty "Invalid alteration of parameters" $ checkParamsOutput referencePaths
             ]
         , testGroup "Constraint 10. Output state"
             [
-              testProperty "Invalid mismatch between state and script output" checkStateOutput
+              testProperty "Invalid mismatch between state and script output's state" $ checkStateOutput referencePaths
             ]
         , testGroup "Constraint 11. Output contract"
             [
-              testProperty "Invalid mismatch between contract and script output" checkContractOutput
+              testProperty "Invalid mismatch between contract and script output" $ checkContractOutput referencePaths
             ]
         , testGroup "Constraint 12. Merkleized continuations"
             [
-              testProperty "Valid merkleization"   $ checkMerkleization True
-            , testProperty "Invalid merkleization" $ checkMerkleization False
+              testProperty "Valid merkleization"   $ checkMerkleization referencePaths True
+            , testProperty "Invalid merkleization" $ checkMerkleization referencePaths False
             ]
         , testGroup "Constraint 13. Positive balances"
             [
-              testProperty "Invalid non-positive balance" checkPositiveAccounts
+              testProperty "Invalid non-positive balance" $ checkPositiveAccounts referencePaths
+              -- TODO: This test on the output state requires instrumenting the Plutus script. For now, this constraint is enforced manually by code inspection.
             ]
         , testGroup "Constraint 14. Inputs authorized"
             [
-              testProperty "Invalid missing authorization" checkAuthorization
+              testProperty "Invalid missing authorization" $ checkAuthorization referencePaths
             ]
         , testGroup "Constraint 15. Sufficient payment"
             [
-              testProperty "Invalid insufficient payment" checkPayment
+              testProperty "Invalid insufficient payment" $ checkPayment referencePaths
+            ]
+        , testGroup "Constraint 18. Final balance"
+            [
+              testProperty "Invalid mismatch between output value and state" $ checkOutputConsistency referencePaths
+            ]
+        , testGroup "Constraint 19. No duplicates"
+            [
+              testProperty "Invalid duplicate accounts in input state" $ checkInputDuplicates referencePaths
+              -- TODO: This test on the output state requires instrumenting the Plutus script. For now, this constraint is enforced manually by code inspection.
+            ]
+        , testGroup "Constraint 20. Single satisfaction"
+            [
+              testProperty "Invalid other validators during payment" $ checkOtherValidators referencePaths
             ]
         , testProperty "Script hash matches reference hash"
             $ checkValidatorHash semanticsScriptHash
               -- DO NOT ALTER THE FOLLOWING VALUE UNLESS YOU ARE COMMITTING
               -- APPROVED CHANGES TO MARLOWE'S SEMANTICS VALIDATOR. THIS HASH
               -- HAS IMPLICATIONS FOR VERSIONING, AUDIT, AND CONTRACT DISCOVERY.
-              "6a9391d6aa51af28dd876ebb5565b69d1e83e5ac7861506bd29b56b0"
+              "2ed2631dbb277c84334453c5c437b86325d371f0835a28b910a91a6e"
         ]
     , testGroup "Payout Validator"
         [
@@ -217,7 +250,7 @@ tests =
               -- DO NOT ALTER THE FOLLOWING VALUE UNLESS YOU ARE COMMITTING
               -- APPROVED CHANGES TO MARLOWE'S ROLE VALIDATOR. THIS HASH HAS
               -- IMPLICATIONS FOR VERSIONING, AUDIT, AND CONTRACT DISCOVERY.
-              "49076eab20243dc9462511fb98a9cfb719f86e9692288139b7c91df3"
+              "e165610232235bbbbeff5b998b233daae42979dec92a6722d9cda989"
         ]
     ]
 
@@ -260,19 +293,21 @@ check1Invalid _ allowEmptyList allowByteString allowUnit =
 
 
 -- | Check that a semantics transaction succeeds.
-checkSemanticsTransaction :: ArbitraryTransaction SemanticsTransaction ()      -- ^ Modifications to make before building the valid transaction.
+checkSemanticsTransaction :: [ReferencePath]                                   -- ^ The reference execution paths from which to choose.
+                          -> ArbitraryTransaction SemanticsTransaction ()      -- ^ Modifications to make before building the valid transaction.
                           -> ArbitraryTransaction SemanticsTransaction ()      -- ^ Modifications to make after building the valid transaction.
                           -> (PlutusTransaction SemanticsTransaction -> Bool)  -- ^ Whether to discard the transaction from the testing.
                           -> Bool                                              -- ^ Whether the transaction should test as valid.
                           -> Bool                                              -- ^ Whether to add noise to the script context.
+                          -> Bool                                              -- ^ Whether to allow merkleization.
                           -> Property                                          -- ^ The test property.
-checkSemanticsTransaction modifyBefore modifyAfter condition valid noisy =
+checkSemanticsTransaction referencePaths modifyBefore modifyAfter condition valid noisy allowMerkleization =
   property
-    . forAll (arbitrarySemanticsTransaction modifyBefore modifyAfter noisy `suchThat` condition)
+    . forAll (arbitrarySemanticsTransaction referencePaths modifyBefore modifyAfter noisy allowMerkleization `suchThat` condition)
     $ \PlutusTransaction{..} ->
       case evaluateSemantics (toData _datum) (toData _redeemer) (toData _scriptContext) of
-        This  e   -> not valid || (error $ show e)
-        These e l -> not valid || (error $ show e <> ": " <> show l)
+        This  e   -> not valid || error (show e)
+        These e l -> not valid || error (show e <> ": " <> show l)
         That    _ -> valid
 
 
@@ -288,14 +323,14 @@ checkPayoutTransaction modifyBefore modifyAfter condition valid noisy =
     . forAll (arbitraryPayoutTransaction modifyBefore modifyAfter noisy `suchThat` condition)
     $ \PlutusTransaction{..} ->
       case evaluatePayout (toData _datum) (toData _redeemer) (toData _scriptContext) of
-        This  e   -> not valid || (error $ show e)
-        These e l -> not valid || (error $ show e <> ": " <> show l)
+        This  e   -> not valid || error (show e)
+        These e l -> not valid || error (show e <> ": " <> show l)
         That    _ -> valid
 
 
 -- | Check that validation fails if two Marlowe scripts are run.
-checkDoubleInput :: Property
-checkDoubleInput =
+checkDoubleInput :: [ReferencePath] -> Property
+checkDoubleInput referencePaths =
   let
     modifyAfter =
       do
@@ -313,7 +348,7 @@ checkDoubleInput =
         infoData <>= AM.fromList [(inDatumHash, inDatum)]
         shuffle
   in
-    checkSemanticsTransaction noModify modifyAfter noVeto False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter noVeto False False False
 
 
 -- | Split a value in half.
@@ -341,9 +376,19 @@ notCloses :: PlutusTransaction SemanticsTransaction -> Bool
 notCloses = not . doesClose
 
 
+-- | Ensure that the contract makes payments.
+hasPayouts :: PlutusTransaction SemanticsTransaction -> Bool
+hasPayouts =
+  let
+    isPayout (Payment _ (Party _) _ i) = i > 0
+    isPayout _ = False
+  in
+    any isPayout . txOutPayments . (^. output)
+
+
 -- | Check that validation fails if there is more than one Marlowe output.
-checkMultipleOutput :: Property
-checkMultipleOutput =
+checkMultipleOutput :: [ReferencePath] -> Property
+checkMultipleOutput referencePaths =
   let
     modifyAfter =
       do
@@ -356,12 +401,12 @@ checkMultipleOutput =
         infoOutputs %= concatMap splitOwnOutput
         shuffle
   in
-    checkSemanticsTransaction noModify modifyAfter notCloses False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter notCloses False False False
 
 
 -- | Check that validation fails if there is one Marlowe output upon close.
-checkCloseOutput :: Property
-checkCloseOutput =
+checkCloseOutput :: [ReferencePath] -> Property
+checkCloseOutput referencePaths =
   let
     modifyAfter =
       do
@@ -374,12 +419,12 @@ checkCloseOutput =
         infoOutputs <>= (txInInfoResolved <$> inScript)
         shuffle
   in
-    checkSemanticsTransaction noModify modifyAfter doesClose False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter doesClose False False False
 
 
 -- | Check that value input to a script matches its input state.
-checkValueInput :: Property
-checkValueInput =
+checkValueInput :: [ReferencePath] -> Property
+checkValueInput referencePaths =
   let
     modifyAfter =
       do
@@ -391,29 +436,90 @@ checkValueInput =
         -- Update the inputs with the incremented script input.
         infoInputs %= fmap incrementOwnInput
     in
-      checkSemanticsTransaction noModify modifyAfter noVeto False False
+      checkSemanticsTransaction referencePaths noModify modifyAfter noVeto False False False
 
 
--- | Check that value output to a script matches its output state.
-checkValueOutput :: Property
-checkValueOutput =
+-- | Check that value output to a script matches its expectation.
+checkValueOutput :: [ReferencePath] -> Property
+checkValueOutput referencePaths =
   let
     modifyAfter =
       do
+        delta <- lift $ oneof [chooseInteger (-5, -1), chooseInteger (1, 5), arbitrary `suchThat` (/= 0)]  -- Ensure small non-zero integers.
         let
-          -- Add one lovelace to the output to the script.
+          -- Add or subtract some lovelace to the output to the script.
           incrementOwnOutput txOut@(TxOut address value _ _)
-            | address == semanticsAddress = txOut {txOutValue = value <> singleton adaSymbol adaToken 1}
-            | otherwise                  = txOut
+            | address == semanticsAddress = txOut {txOutValue = value <> singleton adaSymbol adaToken delta}
+            | otherwise                   = txOut
         -- Update the outputs with the incremented script output.
         infoOutputs %= fmap incrementOwnOutput
   in
-    checkSemanticsTransaction noModify modifyAfter notCloses False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter notCloses False False False
+
+
+-- | Check the consistency of the output value with the output state.
+checkOutputConsistency :: [ReferencePath] -> Property
+checkOutputConsistency referencePaths =
+  property
+    . forAll (arbitrarySemanticsTransaction referencePaths noModify noModify False True)
+    $ \tx ->
+      let
+        findOwnOutput (TxOut address value _ _)
+          | address == semanticsAddress = value
+          | otherwise                   = mempty
+        outValue = foldMap findOwnOutput $ tx ^. infoOutputs
+        finalBalance = totalBalance . accounts . txOutState $ tx ^. output
+        valid = outValue == finalBalance
+      in
+        checkSemanticsTransaction referencePaths noModify noModify notCloses valid False False
+
+
+-- | Add a duplicate entry to an assocation list.
+addDuplicate :: Arbitrary v => AM.Map k v -> Gen (AM.Map k v)
+addDuplicate am =
+  do
+    let
+      am' = AM.toList am
+    key <- elements $ fst <$> am'
+    value <- arbitrary
+    AM.fromList <$> Q.shuffle ((key, value) : am')
+
+
+-- | Check for the detection of duplicates in input state
+checkInputDuplicates :: [ReferencePath] -> Property
+checkInputDuplicates referencePaths =
+  let
+    hasDuplicates tx =
+      let
+        hasDuplicate am = length (AM.keys am) /= length (nub $ AM.keys am)
+        M.State{..} = tx ^. inputState
+      in
+           hasDuplicate accounts
+        || hasDuplicate choices
+        || hasDuplicate boundValues
+    makeDuplicates am =
+      if AM.null am
+        then pure am
+        else oneof [pure am, addDuplicate am]
+    modifyBefore =
+      do
+        M.State{..} <- use inputState
+        inputState <~
+          lift
+            (
+              M.State
+                <$> makeDuplicates accounts
+                <*> makeDuplicates choices
+                <*> makeDuplicates boundValues
+                <*> pure minTime
+            )
+  in
+    checkSemanticsTransaction referencePaths modifyBefore noModify hasDuplicates False False False
 
 
 -- | Check that output datum to a script matches its semantic output.
-checkDatumOutput :: (MarloweData -> Gen MarloweData) -> Property
-checkDatumOutput perturb =
+checkDatumOutput :: [ReferencePath] -> (MarloweData -> Gen MarloweData) -> Property
+checkDatumOutput referencePaths perturb =
   let
     modifyAfter =
       do
@@ -432,13 +538,24 @@ checkDatumOutput perturb =
         -- Update the data with the modification.
         infoData %= AM.fromList . fmap perturbOwnOutputDatum . AM.toList
   in
-    checkSemanticsTransaction noModify modifyAfter notCloses False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter notCloses False False False
+
+
+-- | Check that other validators are forbidden during payments.
+checkOtherValidators :: [ReferencePath] -> Property
+checkOtherValidators referencePaths =
+  let
+    modifyAfter =
+      -- Add an extra script input.
+      infoInputs <><~ lift (listOf1 $ arbitrary `suchThat` isScriptTxIn)
+  in
+    checkSemanticsTransaction referencePaths noModify modifyAfter hasPayouts False False False
 
 
 -- | Check that parameters in the datum are not changed by the transaction.
-checkParamsOutput :: Property
-checkParamsOutput =
-  checkDatumOutput
+checkParamsOutput :: [ReferencePath] -> Property
+checkParamsOutput referencePaths =
+  checkDatumOutput referencePaths
     $ \marloweData ->
       do
         -- Replace the output parameters with a random one.
@@ -448,9 +565,9 @@ checkParamsOutput =
 
 
 -- | Check that state output to a script matches its semantic output.
-checkStateOutput :: Property
-checkStateOutput =
-  checkDatumOutput
+checkStateOutput :: [ReferencePath] -> Property
+checkStateOutput referencePaths =
+  checkDatumOutput referencePaths
     $ \marloweData ->
       do
         -- Replace the output state with a random one.
@@ -460,9 +577,9 @@ checkStateOutput =
 
 
 -- | Check that contract output to a script matches its semantic output.
-checkContractOutput :: Property
-checkContractOutput =
-  checkDatumOutput
+checkContractOutput :: [ReferencePath] -> Property
+checkContractOutput referencePaths =
+  checkDatumOutput referencePaths
     $ \marloweData ->
       do
         -- Replace the output ccontact with a random one.
@@ -482,8 +599,8 @@ hasMerkleizedInput =
 
 
 -- | Check than an invalid merkleization is rejected.
-checkMerkleization :: Bool -> Property
-checkMerkleization valid =
+checkMerkleization :: [ReferencePath] -> Bool -> Property
+checkMerkleization referencePaths valid =
   let
     -- Merkleizedd the contract and its input.
     modifyBefore = merkleize
@@ -499,12 +616,12 @@ checkMerkleization valid =
                hashes <- input `uses` (concatMap merkleHash . txInputs)
                infoData %= (AM.fromList . filter ((`notElem` hashes) . fst) . AM.toList)
   in
-    checkSemanticsTransaction modifyBefore modifyAfter hasMerkleizedInput valid False
+    checkSemanticsTransaction referencePaths modifyBefore modifyAfter hasMerkleizedInput valid False False
 
 
 -- | Check that non-positive accounts are rejected.
-checkPositiveAccounts :: Property
-checkPositiveAccounts =
+checkPositiveAccounts :: [ReferencePath] -> Property
+checkPositiveAccounts referencePaths =
   let
     modifyBefore =
       do
@@ -515,7 +632,7 @@ checkPositiveAccounts =
         -- Add the non-positive entry to the accounts.
         inputState %= (\state -> state {accounts = AM.insert (account, token) amount' $ accounts state})
   in
-    checkSemanticsTransaction modifyBefore noModify noVeto False False
+    checkSemanticsTransaction referencePaths modifyBefore noModify noVeto False False False
 
 
 -- | Compute the authorization for an input.
@@ -547,8 +664,8 @@ deleteFirst f z =
 
 
 -- | Check that a missing authorization causes failure.
-checkAuthorization :: Property
-checkAuthorization =
+checkAuthorization :: [ReferencePath] -> Property
+checkAuthorization referencePaths =
   let
     modifyAfter =
       do
@@ -565,7 +682,7 @@ checkAuthorization =
         -- Remove the first PKH signatory.
         infoSignatories %= deleteFirst matchPkh
   in
-    checkSemanticsTransaction noModify modifyAfter hasAuthorizations False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter hasAuthorizations False False False
 
 
 -- | Determine whether there are any external payments in a transaction.
@@ -585,8 +702,8 @@ decrementValue = foldMap (\(c, n, i) -> singleton c n (i - 1)) . flattenValue
 
 
 -- | Check that an insufficient payment causes failure.
-checkPayment :: Property
-checkPayment =
+checkPayment :: [ReferencePath] -> Property
+checkPayment referencePaths =
   let
     modifyAfter =
       do
@@ -600,7 +717,7 @@ checkPayment =
         -- Update the outputs.
         infoOutputs %= fmap decrementPayment
   in
-    checkSemanticsTransaction noModify modifyAfter hasExternalPayments False False
+    checkSemanticsTransaction referencePaths noModify modifyAfter hasExternalPayments False False False
 
 
 -- | Remove a role input UTxOs from the transaction.
diff --git a/marlowe-test/src/Spec/Marlowe/Plutus/Transaction.hs b/marlowe-test/src/Spec/Marlowe/Plutus/Transaction.hs
index 9141d071f..88201e361 100644
--- a/marlowe-test/src/Spec/Marlowe/Plutus/Transaction.hs
+++ b/marlowe-test/src/Spec/Marlowe/Plutus/Transaction.hs
@@ -27,6 +27,7 @@ module Spec.Marlowe.Plutus.Transaction
   , noModify
   , shuffle
     -- * Conditions
+  , isScriptTxIn
   , noVeto
   ) where
 
@@ -61,7 +62,7 @@ import Plutus.Script.Utils.Scripts (datumHash)
 import Plutus.V1.Ledger.Value (gt)
 import Plutus.V2.Ledger.Api
   ( Address(Address)
-  , Credential(PubKeyCredential)
+  , Credential(..)
   , CurrencySymbol
   , Datum(..)
   , DatumHash(..)
@@ -76,7 +77,7 @@ import Plutus.V2.Ledger.Api
   , ToData(toBuiltinData)
   , TxInInfo(..)
   , TxInfo(..)
-  , TxOut(TxOut)
+  , TxOut(TxOut, txOutAddress)
   , UpperBound(UpperBound)
   , Value
   )
@@ -105,10 +106,11 @@ import Spec.Marlowe.Plutus.Types
   , role
   , scriptPurpose
   )
+import Spec.Marlowe.Reference (ReferencePath, arbitraryReferenceTransaction)
 import Spec.Marlowe.Semantics.Arbitrary (arbitraryGoldenTransaction, arbitraryPositiveInteger)
 import Spec.Marlowe.Semantics.Golden (GoldenTransaction)
 import Spec.Marlowe.Semantics.Merkle (deepMerkleize, merkleizeInputs)
-import Test.Tasty.QuickCheck (Arbitrary(..), Gen, elements, suchThat)
+import Test.Tasty.QuickCheck (Arbitrary(..), Gen, elements, frequency, listOf, suchThat)
 
 import qualified Language.Marlowe.Core.V1.Semantics.Types as M (Party(Address))
 import qualified Plutus.V1.Ledger.Value as V (adaSymbol, adaToken, singleton)
@@ -185,11 +187,15 @@ makeDeposit :: Input
 makeDeposit input' =
   do
     ref <- lift arbitrary
-    address' <- lift arbitrary
+    address' <- lift $ arbitrary `suchThat` notScriptAddress
     pure
       $ case getInputContent input' of
-          IDeposit _ (M.Address _ address) (Token c n) i -> pure . TxInInfo ref $ TxOut address  (V.singleton c n i) NoOutputDatum  Nothing
-          IDeposit _ (Role _             ) (Token c n) i -> pure . TxInInfo ref $ TxOut address' (V.singleton c n i) NoOutputDatum  Nothing
+          IDeposit _ (M.Address _ address) (Token c n) i -> if i > 0
+                                                              then pure . TxInInfo ref $ TxOut address  (V.singleton c n i) NoOutputDatum  Nothing
+                                                              else mempty
+          IDeposit _ (Role _             ) (Token c n) i -> if i > 0
+                                                              then pure . TxInInfo ref $ TxOut address' (V.singleton c n i) NoOutputDatum  Nothing
+                                                              else mempty
           _                                              -> mempty
 
 -- | Create role input for a Marlowe semantics transaction.
@@ -199,7 +205,7 @@ makeRoleIn input' =
   do
     MarloweParams currencySymbol <- use marloweParams
     ref <- lift arbitrary
-    address  <- lift arbitrary
+    address  <- lift $ arbitrary `suchThat` notScriptAddress
     pure
       $ case getInputContent input' of
           IDeposit _ (Role role') _ _         -> pure . TxInInfo ref $ TxOut address (V.singleton currencySymbol role' 1) NoOutputDatum Nothing
@@ -276,6 +282,21 @@ makeSpendSignatory (TxInInfo _ (TxOut (Address (PubKeyCredential pkh) _) _ _ _))
 makeSpendSignatory _                                                             = mempty
 
 
+-- | Combine payments with the same address and hash.
+consolidatePayments :: [TxOut] -> [TxOut]
+consolidatePayments ps =
+  let
+    extractAddressHash (TxOut address _ hash _) = (address, hash)
+    extractValue (TxOut _ value _ _) = value
+  in
+    [
+      TxOut address value hash Nothing
+    |
+      ah@(address, hash) <- nub $ extractAddressHash <$> ps
+    , let value = foldMap extractValue $ filter ((== ah) . extractAddressHash) ps
+    ]
+
+
 -- | Generate a valid Marlowe semantics transaction.
 validSemanticsTransaction :: Bool                                          -- ^ Whether to add noise to the script context.
                           -> ArbitraryTransaction SemanticsTransaction ()  -- ^ The generator.
@@ -313,7 +334,7 @@ validSemanticsTransaction noisy =
     MarloweParams currencySymbol <- use marloweParams
     -- Add the payments.
     (payments, paymentData) <- fmap (bimap mconcat mconcat . unzip) . mapM (makePayment currencySymbol) =<< (output `uses` txOutPayments)
-    infoOutputs <>= payments
+    infoOutputs <>= consolidatePayments payments
     infoData <>= AM.fromList paymentData
 
     -- Add the signatories.
@@ -336,13 +357,20 @@ validSemanticsTransaction noisy =
 
 
 -- | Generate an arbitrary, valid Marlowe semantics transaction: datum, redeemer, and script context.
-arbitrarySemanticsTransaction :: ArbitraryTransaction SemanticsTransaction ()  -- ^ Modifications to make before building the valid transaction.
+arbitrarySemanticsTransaction :: [ReferencePath]                               -- ^ The reference execution paths from which to choose.
+                              -> ArbitraryTransaction SemanticsTransaction ()  -- ^ Modifications to make before building the valid transaction.
                               -> ArbitraryTransaction SemanticsTransaction ()  -- ^ Modifications to make after building the valid transaction.
                               -> Bool                                          -- ^ Whether to add noise to the script context.
+                              -> Bool                                          -- ^ Whether to allow merkleization.
                               -> Gen (PlutusTransaction SemanticsTransaction)  -- ^ The generator.
-arbitrarySemanticsTransaction modifyBefore modifyAfter noisy =
+arbitrarySemanticsTransaction referencePaths modifyBefore modifyAfter noisy allowMerkleization =
   do
-    golden <- arbitraryGoldenTransaction
+    golden <-
+      frequency
+        [
+          (1, arbitraryGoldenTransaction allowMerkleization)  -- Manually vetted transactions.
+        , (5, arbitraryReferenceTransaction referencePaths)   -- Transactions generated using `getAllInputs` and `computeTransaction`.
+        ]
     start <- bareSemanticsTransaction golden
     (modifyBefore >> validSemanticsTransaction noisy >> modifyAfter)
       `execStateT` start
@@ -377,7 +405,7 @@ makePayoutRoleIn :: ArbitraryTransaction PayoutTransaction TxInInfo
 makePayoutRoleIn =
   do
     ref <- lift arbitrary
-    address <- lift arbitrary
+    address <- lift $ arbitrary `suchThat` notScriptAddress
     value <- V.singleton <$> marloweParamsPayout `uses` rolesCurrency <*> use role <*> pure 1
     pure
       . TxInInfo ref
@@ -445,15 +473,50 @@ validPayoutTransaction noisy =
     infoFee <~ V.singleton V.adaSymbol V.adaToken <$> lift arbitraryPositiveInteger
 
     -- Add noise.
-    when noisy addNoise
+    when noisy addNoise'
 
     -- Shuffle.
     shuffle
 
 
+-- | Check that an address is not for a script.
+notScriptAddress :: Address -> Bool
+notScriptAddress (Address (ScriptCredential _) _) = False
+notScriptAddress _ = True
+
+
+-- | Check that an input is not from a script.
+notScriptTxIn :: TxInInfo -> Bool
+notScriptTxIn = not . isScriptTxIn
+
+
+-- | Check that an input is from a script.
+isScriptTxIn :: TxInInfo -> Bool
+isScriptTxIn TxInInfo{txInInfoResolved=TxOut{txOutAddress=Address (ScriptCredential _) _}} = True
+isScriptTxIn _ = False
+
+
 -- | Add noise to the inputs, outputs, and data in a Plutus transaction.
-addNoise :: ArbitraryTransaction a ()
+addNoise :: ArbitraryTransaction SemanticsTransaction ()
 addNoise =
+  do
+    let
+      isPayout (Payment _ (Party _) _ i) = i > 0
+      isPayout _ = False
+    hasPayments <- any isPayout . txOutPayments <$> use output
+    let
+      arbitraryInput =
+        if hasPayments
+          then arbitrary `suchThat` notScriptTxIn
+          else arbitrary
+    infoInputs  <><~ lift (listOf arbitraryInput `suchThat` ((< 5) . length))
+    infoOutputs <><~ lift (arbitrary `suchThat` ((< 5) . length))
+    infoData    <><~ lift (fmap AM.fromList $ arbitrary `suchThat` ((< 5) . length))
+
+
+-- | Add noise to the inputs, outputs, and data in a Plutus transaction.
+addNoise' :: ArbitraryTransaction PayoutTransaction ()
+addNoise' =
   do
     infoInputs  <><~ lift (arbitrary `suchThat` ((< 5) . length))
     infoOutputs <><~ lift (arbitrary `suchThat` ((< 5) . length))
diff --git a/marlowe-test/src/Spec/Marlowe/Reference.hs b/marlowe-test/src/Spec/Marlowe/Reference.hs
new file mode 100644
index 000000000..4c3291e6a
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Reference.hs
@@ -0,0 +1,156 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Function to generate all valid transactions for contracts in JSON files.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE DeriveGeneric #-}
+{-# LANGUAGE FlexibleContexts #-}
+{-# LANGUAGE LambdaCase #-}
+{-# LANGUAGE NumericUnderscores #-}
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
+
+
+module Spec.Marlowe.Reference
+  ( -- * Types
+    ReferencePath(..)
+  , ReferenceTransaction(..)
+    -- * Analysis
+  , processContract
+    -- * Testing
+  , arbitraryReferenceTransaction
+  , readReferencePaths
+  , referenceFolder
+  ) where
+
+
+import Control.Monad (forM)
+import Control.Monad.Except (ExceptT(..), lift, throwError)
+import Data.Aeson (FromJSON, ToJSON, eitherDecodeFileStrict, encodeFile)
+import Data.Bifunctor (first)
+import Data.List (isSuffixOf)
+import GHC.Generics (Generic)
+import Language.Marlowe.Core.V1.Semantics (TransactionInput, TransactionOutput(..), computeTransaction)
+import Language.Marlowe.Core.V1.Semantics.Types (Contract, Party(Role), State(..), Token(..))
+import Language.Marlowe.FindInputs (getAllInputs)
+import Plutus.V2.Ledger.Api (POSIXTime)
+import Spec.Marlowe.Semantics.Golden (GoldenTransaction)
+import System.Directory (listDirectory)
+import System.FilePath ((</>))
+import Test.Tasty.QuickCheck (Gen, elements)
+
+import qualified PlutusTx.AssocMap as AM (empty, singleton)
+
+
+referenceFolder :: FilePath
+referenceFolder = "reference" </> "data"
+
+
+readReferencePaths :: IO [ReferencePath]
+readReferencePaths =
+  do
+    pathFiles <- fmap (referenceFolder </>) . filter (".paths" `isSuffixOf`) <$> listDirectory referenceFolder
+    fmap concat
+      . forM pathFiles
+      $ \pathFile ->
+        eitherDecodeFileStrict pathFile
+          >>= \case
+            Right paths -> pure $ filter (not . null . transactions) paths
+            Left msg -> error $ "Failed parsing " <> pathFile <> ": " <> msg <> "."
+
+
+arbitraryReferenceTransaction :: [ReferencePath] -> Gen GoldenTransaction
+arbitraryReferenceTransaction paths =
+  do
+    ReferencePath{..} <- elements paths
+    if length transactions > 1
+      then do
+             (ReferenceTransaction _ prior, ReferenceTransaction{..}) <- elements $ zip (init transactions) (tail transactions)
+             pure (txOutState prior, txOutContract prior, input, output)
+      else let
+             ReferenceTransaction{..} = head transactions
+            in
+              pure (state, contract, input, output)
+
+
+data ReferencePath =
+  ReferencePath
+  {
+    contract :: Contract
+  , state :: State
+  , transactions :: [ReferenceTransaction]
+  }
+    deriving (Generic, Show)
+
+instance FromJSON ReferencePath
+
+instance ToJSON ReferencePath
+
+
+data ReferenceTransaction =
+  ReferenceTransaction
+  {
+    input :: TransactionInput
+  , output :: TransactionOutput
+  }
+    deriving (Generic, Show)
+
+instance FromJSON ReferenceTransaction
+
+instance ToJSON ReferenceTransaction
+
+
+processContract
+  :: FilePath
+  -> FilePath
+  -> ExceptT String IO ()
+processContract contractFile pathsFile =
+  do
+    contract <- ExceptT $ first show <$> eitherDecodeFileStrict contractFile
+    traces <- ExceptT $ first show <$> getAllInputs contract
+    paths <- runTransactions contract `mapM` traces
+    lift $ encodeFile pathsFile paths
+
+
+runTransactions
+  :: Contract
+  -> (POSIXTime, [TransactionInput])
+  -> ExceptT String IO ReferencePath
+runTransactions contract (startTime, inputs) =
+  do
+    let
+      state = makeState startTime
+    transactions <- runTransaction contract state inputs
+    pure ReferencePath{..}
+
+
+runTransaction
+  :: Contract
+  -> State
+  -> [TransactionInput]
+  -> ExceptT String IO [ReferenceTransaction]
+runTransaction _ _ [] = pure []
+runTransaction contract state (input : inputs) =
+  case computeTransaction input state contract of
+    Error err -> throwError $ show err
+    output@TransactionOutput{..} -> (ReferenceTransaction{..} :) <$> runTransaction txOutContract txOutState inputs
+
+
+makeState
+  :: POSIXTime
+  -> State
+makeState minTime =
+  let
+    accounts = AM.singleton (Role "", Token "" "") 30_000_000  -- Note that 30 ada exceeds min-UTxO for current protocol parameters.
+    choices = AM.empty
+    boundValues = AM.empty
+  in
+    State{..}
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics.hs b/marlowe-test/src/Spec/Marlowe/Semantics.hs
index dfd167f53..a15face41 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics.hs
@@ -24,6 +24,7 @@ import qualified Spec.Marlowe.Semantics.Entropy (tests)
 import qualified Spec.Marlowe.Semantics.Functions (tests)
 import qualified Spec.Marlowe.Semantics.Golden (tests)
 
+
 -- | Run the tests.
 tests :: TestTree
 tests =
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Arbitrary.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Arbitrary.hs
index b05563b29..3ab7ab9df 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Arbitrary.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Arbitrary.hs
@@ -22,7 +22,8 @@
 
 module Spec.Marlowe.Semantics.Arbitrary
   ( -- * Types
-    IsValid(..)
+    Context
+  , IsValid(..)
   , SemiArbitrary(..)
     -- * Generators
   , arbitraryAssocMap
@@ -30,6 +31,7 @@ module Spec.Marlowe.Semantics.Arbitrary
   , arbitraryContractWeighted
   , arbitraryFibonacci
   , arbitraryGoldenTransaction
+  , arbitraryNonnegativeInteger
   , arbitraryPositiveInteger
   , arbitraryTimeIntervalAround
   , arbitraryValidInput
@@ -54,7 +56,15 @@ import Control.Monad (replicateM)
 import Data.Function (on)
 import Data.List (nub, nubBy)
 import Language.Marlowe.Core.V1.Semantics
-  (TransactionInput(..), TransactionOutput(..), computeTransaction, evalObservation, evalValue)
+  ( Payment(..)
+  , TransactionError(..)
+  , TransactionInput(..)
+  , TransactionOutput(..)
+  , TransactionWarning(..)
+  , computeTransaction
+  , evalObservation
+  , evalValue
+  )
 import Language.Marlowe.Core.V1.Semantics.Types
   ( Accounts
   , Action(..)
@@ -67,6 +77,7 @@ import Language.Marlowe.Core.V1.Semantics.Types
   , Environment(..)
   , Input(..)
   , InputContent(..)
+  , IntervalError(..)
   , Observation(..)
   , Party(..)
   , Payee(..)
@@ -77,6 +88,7 @@ import Language.Marlowe.Core.V1.Semantics.Types
   , ValueId(..)
   , getAction
   )
+import Plutus.Script.Utils.Scripts (dataHash)
 import Plutus.V2.Ledger.Api
   ( Credential(..)
   , CurrencySymbol(..)
@@ -87,11 +99,13 @@ import Plutus.V2.Ledger.Api
   , ValidatorHash(..)
   , adaSymbol
   , adaToken
+  , toBuiltinData
   )
 import PlutusTx.Builtins (BuiltinByteString, appendByteString, lengthOfByteString, sliceByteString)
 import Spec.Marlowe.Semantics.Golden (GoldenTransaction, goldenContracts, goldenTransactions)
+import Spec.Marlowe.Semantics.Merkle (merkleizeInputs, shallowMerkleize)
 import Test.Tasty.QuickCheck
-  (Arbitrary(..), Gen, chooseInteger, elements, frequency, listOf, shrinkList, sized, suchThat, vectorOf)
+  (Arbitrary(..), Gen, chooseInteger, elements, frequency, listOf, oneof, shrinkList, sized, suchThat, vectorOf)
 
 import qualified Plutus.V2.Ledger.Api as Ledger (Address(..))
 import qualified PlutusTx.AssocMap as AM (Map, delete, empty, fromList, keys, toList)
@@ -880,11 +894,11 @@ goldenContract = (,) <$> elements goldenContracts <*> pure (State AM.empty AM.em
 
 instance Arbitrary Contract where
   arbitrary = frequency [(95, semiArbitrary =<< arbitrary), (5, fst <$> goldenContract)]
-  shrink (Pay a p t x c) = [Pay a' p t x c | a' <- shrink a] ++ [Pay a p' t x c | p' <- shrink p] ++ [Pay a p t' x c | t' <- shrink t] ++ [Pay a p t x' c | x' <- shrink x] ++ [Pay a p t x c' | c' <- shrink c]
-  shrink (If o x y) = [If o' x y | o' <- shrink o] ++ [If o x' y | x' <- shrink x] ++ [If o x y' | y' <- shrink y]
-  shrink (When a t c) = [When a' t c | a' <- shrink a] ++ [When a t' c | t' <- shrink t] ++ [When a t c' | c' <- shrink c]
-  shrink (Let v x c) = [Let v' x c | v' <- shrink v] ++ [Let v x' c | x' <- shrink x] ++ [Let v x c' | c' <- shrink c]
-  shrink (Assert o c) = [Assert o' c | o' <- shrink o] ++ [Assert o c' | c' <- shrink c]
+  shrink (Pay a p t x c) = [c] ++ [Pay a' p t x c | a' <- shrink a] ++ [Pay a p' t x c | p' <- shrink p] ++ [Pay a p t' x c | t' <- shrink t] ++ [Pay a p t x' c | x' <- shrink x] ++ [Pay a p t x c' | c' <- shrink c]
+  shrink (If o x y) = [x, y] ++ [If o' x y | o' <- shrink o] ++ [If o x' y | x' <- shrink x] ++ [If o x y' | y' <- shrink y]
+  shrink (When a t c) = [c] ++ [When a' t c | a' <- shrink a] ++ [When a t' c | t' <- shrink t] ++ [When a t c' | c' <- shrink c]
+  shrink (Let v x c) = [c] ++ [Let v' x c | v' <- shrink v] ++ [Let v x' c | x' <- shrink x] ++ [Let v x c' | c' <- shrink c]
+  shrink (Assert o c) = [c] ++ [Assert o' c | o' <- shrink o] ++ [Assert o c' | c' <- shrink c]
   shrink _ = []
 
 
@@ -1047,10 +1061,22 @@ instance SemiArbitrary InputContent where
 instance Arbitrary Input where
   arbitrary = semiArbitrary =<< arbitrary
   shrink (NormalInput i)         = NormalInput <$> shrink i
-  shrink (MerkleizedInput i b c) = [MerkleizedInput i' b c | i' <- shrink i]
+  shrink (MerkleizedInput i b c) =
+    [NormalInput i]
+      <> [MerkleizedInput i' b c | i' <- shrink i]
+      <> [MerkleizedInput i (dataHash $ toBuiltinData c) c' | c' <- shrink c]
 
 instance SemiArbitrary Input where
-  semiArbitrary context = NormalInput <$> semiArbitrary context
+  semiArbitrary context =
+    frequency
+      [
+        (9, NormalInput <$> semiArbitrary context)
+      , (1, do
+              input <- semiArbitrary context
+              contract <- semiArbitrary context
+              pure $ MerkleizedInput input (dataHash $ toBuiltinData contract) contract
+        )
+      ]
 
 
 instance Arbitrary TransactionInput where
@@ -1073,7 +1099,7 @@ arbitraryValidStep :: State                 -- ^ The state of the contract.
                    -> Gen TransactionInput  -- ^ Generator for a transaction input for a single step.
 arbitraryValidStep _ (When [] timeout _) =
   TransactionInput <$> arbitraryTimeIntervalAfter timeout <*> pure []
-arbitraryValidStep state@State{..} (When cases timeout _) =
+arbitraryValidStep state@State{..} contract@(When cases timeout _) =
   do
     let
       isEmptyChoice (Choice _ []) = True
@@ -1090,7 +1116,13 @@ arbitraryValidStep state@State{..} (When cases timeout _) =
                                          Bound lower upper <- elements bs
                                          IChoice n <$> chooseInteger (lower, upper)
                     Notify _        -> pure INotify
-             pure $ TransactionInput times [NormalInput i]
+             is <-
+               frequency
+                 [
+                   (9, pure [NormalInput i])
+                 , (1, pure [MerkleizedInput i (dataHash $ toBuiltinData contract) contract])
+                 ]
+             pure $ TransactionInput times is
 arbitraryValidStep State{minTime} contract =
 {-
   NOTE: Alternatively, if semantics should allow applying `[]` to a non-quiescent contract
@@ -1144,10 +1176,66 @@ arbitraryValidInputs state contract =
 
 
 -- | Generate an arbitrary golden transaction.
-arbitraryGoldenTransaction :: Gen GoldenTransaction
-arbitraryGoldenTransaction =
+arbitraryGoldenTransaction :: Bool -> Gen GoldenTransaction
+arbitraryGoldenTransaction allowMerkleization =
   do
+    let
+      perhapsMerkleize gt@(state, contract, input, _) =
+        let
+          (contract', continuations) = shallowMerkleize contract
+          input' = merkleizeInputs continuations state contract' input
+        in
+          case input' of
+            Nothing      -> pure gt
+            Just input'' -> frequency [(9, pure gt), (1, pure (state, contract', input'', computeTransaction input'' state contract'))]
     equalContractWeights <- frequency [(1, pure True), (5, pure False)]
-    if equalContractWeights
-      then elements =<< elements goldenTransactions
-      else elements $ concat goldenTransactions
+    (if allowMerkleization then perhapsMerkleize else pure)
+      =<< if equalContractWeights
+            then elements =<< elements goldenTransactions
+            else elements $ concat goldenTransactions
+
+
+instance Arbitrary Payment where
+  arbitrary = Payment <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
+
+
+instance Arbitrary IntervalError where
+  arbitrary =
+    oneof
+      [
+        InvalidInterval <$> arbitrary
+      , IntervalInPastError <$> arbitrary <*> arbitrary
+      ]
+
+
+instance Arbitrary TransactionError where
+  arbitrary =
+    oneof
+      [
+        pure TEAmbiguousTimeIntervalError
+      , pure TEApplyNoMatchError
+      , TEIntervalError <$> arbitrary
+      , pure TEUselessTransaction
+      , pure TEHashMismatch
+      ]
+
+
+instance Arbitrary TransactionWarning where
+  arbitrary =
+    oneof
+      [
+        TransactionNonPositiveDeposit <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
+      , TransactionNonPositivePay <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
+      , TransactionPartialPay <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
+      , TransactionShadowing <$> arbitrary <*> arbitrary <*> arbitrary
+      , pure TransactionAssertionFailed
+      ]
+
+
+instance Arbitrary TransactionOutput where
+  arbitrary =
+    oneof
+      [
+        TransactionOutput <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
+      , Error <$> arbitrary
+      ]
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Compute.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Compute.hs
index 402460ed2..7aa9ed803 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Compute.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Compute.hs
@@ -13,6 +13,7 @@
 
 {-# LANGUAGE ConstraintKinds #-}
 {-# LANGUAGE FlexibleContexts #-}
+{-# LANGUAGE LambdaCase #-}
 {-# LANGUAGE RankNTypes #-}
 {-# LANGUAGE RecordWildCards #-}
 
@@ -31,6 +32,7 @@ import Control.Applicative (liftA2)
 import Control.Lens.Getter (Getter, to, view)
 import Control.Monad.Except (MonadError(throwError), unless, when)
 import Control.Monad.Reader (ReaderT(runReaderT))
+import Data.Bifunctor (second)
 import Data.Default (Default(..))
 import Data.Function (on)
 import Data.List (sort)
@@ -49,29 +51,34 @@ import Language.Marlowe.Core.V1.Semantics.Types
   ( AccountId
   , Accounts
   , Action(Choice, Deposit, Notify)
-  , Case
+  , Bound(..)
+  , Case(..)
   , ChoiceId
   , ChosenNum
   , Contract(..)
   , Environment(Environment)
-  , Input
+  , Input(..)
   , InputContent(IChoice, IDeposit, INotify)
   , IntervalError(IntervalInPastError, InvalidInterval)
-  , Observation
+  , Observation(TrueObs)
   , Payee(Party)
   , State(..)
   , TimeInterval
   , Token(..)
-  , Value
+  , Value(Constant)
   , ValueId
   , getAction
   , getInputContent
   )
 import Language.Marlowe.FindInputs (getAllInputs)
-import Plutus.V2.Ledger.Api (CurrencySymbol, POSIXTime(..), TokenName)
+import Plutus.Script.Utils.Scripts (datumHash)
+import Plutus.V2.Ledger.Api (CurrencySymbol, Datum(..), DatumHash(..), POSIXTime(..), TokenName, toBuiltinData)
 import Spec.Marlowe.Semantics.Arbitrary
-  ( SemiArbitrary(semiArbitrary)
+  ( Context
+  , SemiArbitrary(semiArbitrary)
   , arbitraryContractWeighted
+  , arbitraryGoldenTransaction
+  , arbitraryPositiveInteger
   , assertContractWeights
   , closeContractWeights
   , defaultContractWeights
@@ -85,7 +92,19 @@ import Spec.Marlowe.Semantics.Orphans ()
 import System.IO.Unsafe (unsafePerformIO)
 import Test.Tasty (TestTree, testGroup)
 import Test.Tasty.QuickCheck
-  (Arbitrary(..), Gen, Testable(property), discard, elements, forAll, forAllShrink, frequency, suchThat, testProperty)
+  ( Arbitrary(..)
+  , Gen
+  , Testable(property)
+  , chooseInteger
+  , discard
+  , elements
+  , forAll
+  , forAllShrink
+  , frequency
+  , shuffle
+  , suchThat
+  , testProperty
+  )
 
 import qualified PlutusTx.AssocMap as AM
 
@@ -161,18 +180,145 @@ arbitraryMarloweContext w =
 -- | Generate an arbitrary valid Marlowe transaction context.
 arbitraryValid :: Gen MarloweContext
 arbitraryValid =
-    do
-      mcContract <- arbitrary `suchThat` (/= Close)
-      (time, inputs') <-
-        case unsafePerformIO $ getAllInputs mcContract of
-          Right candidates -> elements candidates
-          Left _           -> discard
-      let
-        -- TODO: Generalize to arbitrary starting state.
-        mcState = State AM.empty AM.empty AM.empty time
-        mcInput = head inputs'
-        mcOutput = computeTransaction mcInput mcState mcContract
-      pure MarloweContext{..}
+  let
+    randomContext =
+      do
+        mcContract <- arbitrary `suchThat` (/= Close)
+        (time, inputs') <-
+          case unsafePerformIO $ getAllInputs mcContract of
+            Right candidates -> elements candidates
+            Left _           -> discard
+        let
+          -- TODO: Generalize to arbitrary starting state.
+          mcState = State AM.empty AM.empty AM.empty time
+          mcInput = head inputs'
+          mcOutput = computeTransaction mcInput mcState mcContract
+        pure MarloweContext{..}
+    goldenContext =
+      do
+        (mcState, mcContract, mcInput, mcOutput) <- arbitraryGoldenTransaction True
+        pure MarloweContext{..}
+  in
+    frequency [(1, randomContext), (2, goldenContext)]
+
+
+-- | Generate a simple valid transaction.
+simpleTransaction
+  :: Context
+  -> (TimeInterval -> Contract -> Gen Contract)
+  -> (State -> Gen State)
+  -> (TransactionInput -> Gen TransactionInput)
+  -> Gen MarloweContext
+simpleTransaction context modifyContract modifyState modifyInput =
+  do
+    mcState <- modifyState =<< semiArbitrary context
+    intervalStart <- (getPOSIXTime (minTime mcState) +) <$> arbitraryPositiveInteger
+    intervalEnd <- (intervalStart +) <$> arbitraryPositiveInteger
+    let
+      interval = (POSIXTime intervalStart, POSIXTime intervalEnd)
+    timeout <- (intervalEnd +) <$> arbitraryPositiveInteger
+    mcContract <- modifyContract interval . When [] (POSIXTime timeout) =<< semiArbitrary context
+    mcInput <- modifyInput $ TransactionInput interval []
+    let
+      mcOutput = computeTransaction mcInput mcState mcContract
+    pure MarloweContext{..}
+
+
+-- | Generate a simple payment.
+simplePayment :: Gen MarloweContext
+simplePayment =
+  do
+    context <- arbitrary
+    balance <- arbitraryPositiveInteger
+    payment <- chooseInteger (1, balance)
+    account <- semiArbitrary context
+    payee <- semiArbitrary context
+    token <- semiArbitrary context
+    let
+      modifyContract _ contract = pure $ Pay account (Party payee) token (Constant payment) contract
+      modifyState state =
+        do
+          accounts' <-
+            fmap AM.fromList . shuffle . AM.toList
+              . AM.insert (account, token) balance
+              . AM.delete (account, token)
+              $ accounts state
+          pure state {accounts = accounts'}
+    simpleTransaction context modifyContract modifyState pure
+
+
+-- | Generate a simple deposit.
+simpleDeposit :: Gen MarloweContext
+simpleDeposit =
+  do
+    context <- arbitrary
+    deposit <- arbitraryPositiveInteger
+    account <- semiArbitrary context
+    payee <- semiArbitrary context
+    token <- semiArbitrary context
+    let
+      modifyContract (_, POSIXTime intervalEnd) contract =
+        pure
+          $ When [Case (Deposit account payee token $ Constant deposit) contract]
+            (POSIXTime $ intervalEnd + 1) contract
+      modifyInput (TransactionInput interval _) = pure $ TransactionInput interval [NormalInput $ IDeposit account payee token deposit]
+    simpleTransaction context modifyContract pure modifyInput
+
+
+-- | Generate a simple notification.
+simpleChoice :: Gen MarloweContext
+simpleChoice =
+  do
+    context <- arbitrary
+    choiceId <- semiArbitrary context
+    value <- semiArbitrary context
+    bound <- Bound <$> ((value -) <$> arbitraryPositiveInteger) <*> ((value +) <$> arbitraryPositiveInteger)
+    let
+      modifyContract (_, POSIXTime intervalEnd) contract =
+        do
+          let
+            timeout = POSIXTime $ intervalEnd + 1
+          contract' <- When [] timeout <$> semiArbitrary context
+          pure $ When [Case (Choice choiceId [bound]) contract'] timeout contract
+      modifyInput (TransactionInput interval _) = pure $ TransactionInput interval [NormalInput $ IChoice choiceId value]
+    simpleTransaction context modifyContract pure modifyInput
+
+
+-- | Generate a simple notification.
+simpleNotify :: Gen MarloweContext
+simpleNotify =
+  do
+    context <- arbitrary
+    let
+      modifyContract (_, POSIXTime intervalEnd) contract =
+        do
+          let
+            timeout = POSIXTime $ intervalEnd + 1
+          contract' <- When [] timeout <$> semiArbitrary context
+          pure $ When [Case (Notify TrueObs) contract'] timeout contract
+      modifyInput (TransactionInput interval _) = pure $ TransactionInput interval [NormalInput INotify]
+    simpleTransaction context modifyContract pure modifyInput
+
+
+-- | Generate a simple notification.
+simpleMerkleization :: Gen MarloweContext
+simpleMerkleization =
+  do
+    context <- arbitrary
+    mcState <- semiArbitrary context
+    intervalStart <- (getPOSIXTime (minTime mcState) +) <$> arbitraryPositiveInteger
+    intervalEnd <- (intervalStart +) <$> arbitraryPositiveInteger
+    let
+      interval = (POSIXTime intervalStart, POSIXTime intervalEnd)
+    timeout <- (intervalEnd +) <$> arbitraryPositiveInteger
+    contract <- When [] (POSIXTime timeout) <$> semiArbitrary context
+    let
+      DatumHash hash = datumHash . Datum $ toBuiltinData contract
+      mcInput = TransactionInput interval [MerkleizedInput INotify hash contract]
+    mcContract <- When [MerkleizedCase (Notify TrueObs) hash] (POSIXTime timeout) <$> semiArbitrary context
+    let
+      mcOutput = computeTransaction mcInput mcState mcContract
+    pure MarloweContext{..}
 
 
 -- | Recompute the output of a Marlowe transaction in an transaction context.
@@ -543,6 +689,27 @@ requireAmbiguousTimeout =
   >> requireNextTimeout `requireLE` view latestTime
 
 
+-- | Require a payment to a party.
+requirePayout :: Testify ()
+requirePayout =
+  let
+    isPayout (Payment _ (Party _) _ i) = i > 0
+    isPayout _ = False
+  in
+    view payments >>= "Positive payout" `require` any isPayout
+
+
+-- | Require not deposits.
+requireNoDeposits :: Testify ()
+requireNoDeposits =
+  let
+    isDeposit (NormalInput (IDeposit _ _ _ i)) = i > 0
+    isDeposit (MerkleizedInput (IDeposit _ _ _ i) _ _) = i > 0
+    isDeposit _ = False
+  in
+    view inputs >>= "No deposits" `require` (not . any isDeposit)
+
+
 -- | Throw an error unless a condition holds.
 throwUnless :: MonadError String m
             => String
@@ -671,30 +838,31 @@ checkContinuation expected =
 data TransactionTest =
   TransactionTest
   {
-    name          :: String
-  , generator     :: Gen MarloweContext
-  , precondition  :: Testify ()
-  , invariant     :: [Invariant]
-  , postcondition :: Testify ()
+    name           :: String
+  , generator      :: Gen MarloweContext
+  , precondition   :: Testify ()
+  , invariant      :: [Invariant]
+  , postcondition  :: Testify ()
+  , allowShrinkage :: Bool
   }
 
 instance Default TransactionTest where
   def =
     TransactionTest
     {
-      name          = mempty
-    , generator     = arbitrary
-    , precondition  = pure ()
-    , invariant     = mempty
-    , postcondition = pure ()
+      name           = mempty
+    , generator      = arbitrary
+    , precondition   = pure ()
+    , invariant      = mempty
+    , postcondition  = pure ()
+    , allowShrinkage = True
     }
 
 
 -- | Test a Marlowe transaction.
-test :: Bool             -- ^ Whether to perform shrinkage of generated values.
-     -> TransactionTest  -- ^ The test.
+test :: TransactionTest  -- ^ The test.
      -> TestTree         -- ^ The result.
-test doShrink TransactionTest{..} =
+test TransactionTest{..} =
   testProperty name
     . property
     $ let
@@ -707,7 +875,7 @@ test doShrink TransactionTest{..} =
             Right () -> True   -- Test passed.
         gen = generator `suchThat` preResolve precondition
       in
-        (if doShrink then forAllShrink gen shrink else forAll gen)
+        (if allowShrinkage then forAllShrink gen shrink else forAll gen)
           . postResolve
           $ mapM_ checkInvariant invariant >> postcondition
 
@@ -858,11 +1026,128 @@ anyInput =
   }
 
 
+-- | Test that payments substract value from internal accounts.
+payingSubtractsFromAccount :: TransactionTest
+payingSubtractsFromAccount =
+  def
+  {
+    name           = "Paying subtracts from account"
+  , allowShrinkage = False
+  , generator      = simplePayment
+  , postcondition  = do
+                       delta <-
+                         fmap (AM.filter (/= 0))
+                           $ AM.unionWith (+)
+                           <$> view preAccounts
+                           <*> (AM.fromList . fmap (second negate) . AM.toList <$> view postAccounts)
+                       require "Only one balance changes." ((== 1) . length . AM.toList) delta
+                       require "Some balance decreases." (all (> 0) . AM.elems) delta
+  }
+
+
+-- | Test that deposits add value to internal accounts.
+depositAddsToAccount :: TransactionTest
+depositAddsToAccount =
+  def
+  {
+    name           = "Deposit adds to account"
+  , allowShrinkage = False
+  , generator      = simpleDeposit
+  , postcondition  = do
+                       delta <-
+                         fmap (AM.filter (/= 0))
+                           $ AM.unionWith (+)
+                           <$> view postAccounts
+                           <*> (AM.fromList . fmap (second negate) . AM.toList <$> view preAccounts)
+                       require "Only one balance changes." ((== 1) . length . AM.toList) delta
+                       require "Some balance increases." (all (> 0) . AM.elems) delta
+  }
+
+
+-- | Test that notify contines as expected
+notifyContinues :: TransactionTest
+notifyContinues =
+  def
+  {
+    name           = "Notify continues as expected"
+  , allowShrinkage = False
+  , generator      = simpleNotify
+  , postcondition  = view preContract >>=
+                       \case
+                         When [Case (Notify TrueObs) contract] _ _ -> checkContinuation contract
+                         _ -> throwError "Test setup failed."
+  }
+
+
+-- | Test that choice continues as expected.
+choiceContinues :: TransactionTest
+choiceContinues =
+  def
+  {
+    name           = "Choice continues as expected"
+  , allowShrinkage = False
+  , generator      = simpleChoice
+  , postcondition  = view preContract >>=
+                       \case
+                         When [Case (Choice _ _) contract] _ _ -> checkContinuation contract
+                         _ -> throwError "Test setup failed."
+  }
+
+
+-- | Test that deposit continues as expected.
+depositContinues :: TransactionTest
+depositContinues =
+  def
+  {
+    name           = "Deposit continues as expected"
+  , allowShrinkage = False
+  , generator      = simpleDeposit
+  , postcondition  = view preContract >>=
+                       \case
+                         When [Case Deposit{} contract] _ _ -> checkContinuation contract
+                         _ -> throwError "Test setup failed."
+  }
+
+
+-- | Test that deposit continues as expected.
+merkleizationContinues :: TransactionTest
+merkleizationContinues =
+  def
+  {
+    name           = "Merkleization continues as expected"
+  , allowShrinkage = False
+  , generator      = simpleMerkleization
+  , postcondition  = view inputs >>=
+                       \case
+                         [MerkleizedInput INotify _ contract] -> checkContinuation contract
+                         _ -> throwError "Test setup failed."
+  }
+
+
+-- | Test that deposit continues as expected.
+choiceSets :: TransactionTest
+choiceSets =
+  def
+  {
+    name           = "Choice records the value of the choice"
+  , allowShrinkage = False
+  , generator      = simpleChoice
+  , postcondition  = view inputs >>=
+                       \case
+                         [NormalInput (IChoice choiceId value)] ->
+                           do
+                             choices' <- choices <$> view postState
+                             unless (AM.lookup choiceId choices' == Just value)
+                               $ throwError "Choice missing from state"
+                         _ -> throwError "Test setup failed."
+  }
+
+
 -- | Run the tests.
 tests :: TestTree
 tests =
   testGroup "Compute Transaction"
-    $ fmap (test True)
+    $ test <$>
     [
       invalidInterval
     , tooEarly
@@ -875,4 +1160,11 @@ tests =
     , ifBranches
     , assertWarns
     , anyInput
+    , payingSubtractsFromAccount
+    , depositAddsToAccount
+    , depositContinues
+    , choiceContinues
+    , notifyContinues
+    , choiceSets
+    , merkleizationContinues
     ]
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Functions.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Functions.hs
index 25fbef841..9a3c8acdc 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Functions.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Functions.hs
@@ -100,6 +100,7 @@ tests =
         testProperty "Invalid interval" $ checkFixInterval True  False
       , testProperty "Interval in past" $ checkFixInterval False True
       , testProperty "Interval trimmed" $ checkFixInterval False False
+      , testProperty "Invalid interval in past" $ checkFixInterval True True
       ]
     , testGroup "evalValue"
       [
@@ -218,14 +219,22 @@ forAll' = flip forAllShrink shrink
 --   generating arbitrary valid and invalid intervals and checking that
 --   results or errors re reported correctly.
 checkFixInterval :: Bool      -- ^ Whether the validity interval should be invalid.
-                 -> Bool      -- ^ Whethe the validity interval should be in the past.
+                 -> Bool      -- ^ Whether the validity interval should be in the past.
                  -> Property  -- ^ The test.
 checkFixInterval invalid inPast =
   property $ do
   let gen = do
         state <- arbitrary
-        end   <- arbitrary `suchThat` (\t -> (t < minTime state) == inPast)
-        start <- arbitrary `suchThat` (\t -> (t > end) == invalid && (t < minTime state) == inPast)
+        (start, end) <-
+          case (invalid, inPast) of
+            (True, True) -> do
+                              start' <- arbitrary `suchThat` (< minTime state)
+                              end'   <- arbitrary `suchThat` (< start')
+                              pure (start', end')
+            _            -> do
+                              end'   <- arbitrary `suchThat` (\t -> (t < minTime state) == inPast)
+                              start' <- arbitrary `suchThat` (\t -> (t > end') == invalid && (t < minTime state) == inPast)
+                              pure (start', end')
         pure ((start, end), state)
   forAll' gen $ \(interval, state) ->
     case fixInterval interval state of
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Golden.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Golden.hs
index 9025906ad..72d052fb7 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Golden.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Golden.hs
@@ -40,6 +40,7 @@ import Test.Tasty.HUnit (assertBool, testCase)
 
 import qualified PlutusTx.AssocMap as AM (empty)
 import qualified Spec.Marlowe.Semantics.Golden.Escrow as Escrow (contract, invalids, valids)
+import qualified Spec.Marlowe.Semantics.Golden.Negative as Negative (contract, invalids, valids)
 import qualified Spec.Marlowe.Semantics.Golden.Pangram as Pangram (contract, invalids, valids)
 import qualified Spec.Marlowe.Semantics.Golden.Swap as Swap (contract, invalids, valids)
 import qualified Spec.Marlowe.Semantics.Golden.Trivial as Trivial (contract, invalids, valids)
@@ -59,6 +60,7 @@ goldenContracts =
   , Swap.contract
   , Trivial.contract
   , ZCB.contract
+  , Negative.contract
   -- Note that Pangram is omitted because `getAllInputs` takes 30 minutes for it.
   ]
 
@@ -68,11 +70,12 @@ tests :: TestTree
 tests =
   testGroup "Golden"
     [
-      testGolden "Escrow"           _GENERATE_TEST_CASES_ Escrow.contract  Escrow.valids  Escrow.invalids
-    , testGolden "Pangram"          _GENERATE_TEST_CASES_ Pangram.contract Pangram.valids Pangram.invalids
-    , testGolden "Swap"             _GENERATE_TEST_CASES_ Swap.contract    Swap.valids    Swap.invalids
-    , testGolden "Trivial"          _GENERATE_TEST_CASES_ Trivial.contract Trivial.valids Trivial.invalids
-    , testGolden "Zero Coupon Bond" _GENERATE_TEST_CASES_ ZCB.contract     ZCB.valids     ZCB.invalids
+      testGolden "Escrow"           _GENERATE_TEST_CASES_ Escrow.contract   Escrow.valids   Escrow.invalids
+    , testGolden "Pangram"          _GENERATE_TEST_CASES_ Pangram.contract  Pangram.valids  Pangram.invalids
+    , testGolden "Swap"             _GENERATE_TEST_CASES_ Swap.contract     Swap.valids     Swap.invalids
+    , testGolden "Trivial"          _GENERATE_TEST_CASES_ Trivial.contract  Trivial.valids  Trivial.invalids
+    , testGolden "Zero Coupon Bond" _GENERATE_TEST_CASES_ ZCB.contract      ZCB.valids      ZCB.invalids
+    , testGolden "Negative"         _GENERATE_TEST_CASES_ Negative.contract Negative.valids Negative.invalids
     ]
 
 
@@ -125,7 +128,7 @@ testInvalid :: Contract -> [GoldenCase] -> IO ()
 testInvalid = testValidity False
 
 
--- | Test erroneous transactions for the Pangram contract.
+-- | Test erroneous transactions for a contract.
 testValidity :: Bool          -- ^ Whether the test cases should pass.
              -> Contract      -- ^ The contract.
              -> [GoldenCase]  -- ^ The test cases.
@@ -148,11 +151,12 @@ goldenTransactions :: [[GoldenTransaction]]
 goldenTransactions =
   uncurry validTransactions
     <$> [
-          (Escrow.contract , Escrow.valids )
-        , (Pangram.contract, Pangram.valids)
-        , (Swap.contract   , Swap.valids   )
-        , (Trivial.contract, Trivial.valids)
-        , (ZCB.contract    , ZCB.valids    )
+          (Escrow.contract  , Escrow.valids  )
+        , (Pangram.contract , Pangram.valids )
+        , (Swap.contract    , Swap.valids    )
+        , (Trivial.contract , Trivial.valids )
+        , (ZCB.contract     , ZCB.valids     )
+        , (Negative.contract, Negative.valids)
         ]
 
 
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Golden/Negative.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Golden/Negative.hs
new file mode 100644
index 000000000..eea8fa414
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Golden/Negative.hs
@@ -0,0 +1,151 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Reference golden output for a contract with negative deposits.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE NumericUnderscores #-}
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE TypeSynonymInstances #-}
+
+
+module Spec.Marlowe.Semantics.Golden.Negative
+  ( -- * Contracts
+    contract
+    -- * Test cases
+  , invalids
+  , valids
+  ) where
+
+
+import Language.Marlowe.Core.V1.Semantics
+  (Payment(Payment), TransactionInput(..), TransactionOutput(..), TransactionWarning(TransactionNonPositiveDeposit))
+import Language.Marlowe.Core.V1.Semantics.Types
+  ( Action(Choice, Deposit, Notify)
+  , Bound(..)
+  , Case(Case)
+  , ChoiceId(..)
+  , Contract(Close, Let, When)
+  , Input(NormalInput)
+  , InputContent(IChoice, IDeposit, INotify)
+  , Observation(ValueEQ, ValueGT, ValueLT)
+  , Party
+  , Payee(Party)
+  , State(State, accounts, boundValues, choices, minTime)
+  , Token(..)
+  , Value(ChoiceValue, Constant)
+  )
+import Language.Marlowe.Util ()
+import Plutus.V2.Ledger.Api (POSIXTime(..))
+
+import qualified PlutusTx.AssocMap as AM (Map, fromList)
+
+
+party :: Party
+party = "Party"
+
+counterparty :: Party
+counterparty = "Counterparty"
+
+ada :: Token
+ada = Token "" ""
+
+
+-- | The Zero-Coupon Bond contract.
+contract :: Contract
+contract =
+  let
+    initial = Constant 2_000_000
+    choice = ChoiceId "Deposit" party
+    value = ChoiceValue choice
+    initialDeadline = 1000
+    choiceDeadline = 2000
+    notifyDeadline = 3000
+    depositDeadline = 4000
+  in
+    When
+      [
+        Case (Deposit counterparty counterparty ada initial)
+          $ When
+              [
+                Case (Choice choice [Bound (-1) 1])
+                  $ When
+                    [
+                      Case (Deposit party counterparty ada value)
+                        Close
+                    , Case (Notify $ ValueGT value $ Constant 0)
+                       $ Let "Positive" (Constant 1)
+                       $ When
+                         [
+                           Case (Deposit party counterparty ada value)
+                             Close
+                         ]
+                         depositDeadline
+                         Close
+                    , Case (Notify $ ValueEQ value $ Constant 0)
+                       $ Let "Neutral" (Constant 1)
+                       $ When
+                         [
+                           Case (Deposit party party ada value)
+                             Close
+                         ]
+                         depositDeadline
+                         Close
+                    , Case (Notify $ ValueLT value $ Constant 0)
+                       $ Let "Negative" (Constant 1)
+                       $ When
+                         [
+                           Case (Deposit counterparty party ada value)
+                             Close
+                         ]
+                         depositDeadline
+                         Close
+                    ]
+                    notifyDeadline
+                    Close
+              ]
+              choiceDeadline
+              Close
+      ]
+      initialDeadline
+      Close
+
+
+-- | A wrapper to assist parsing of test cases.
+newtype Map k v = Map {unMap :: [(k, v)]}
+
+
+-- | A function to assist parsing of test cases.
+toAM :: Map k v -> AM.Map k v
+toAM = AM.fromList . unMap
+
+
+-- | A list of test cases and results that should succeed, generated from `Language.Marlowe.FindInputs.getAllInputs`.
+valids :: [(POSIXTime, [TransactionInput], TransactionOutput)]
+valids =
+  [
+    (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 1000},POSIXTime {getPOSIXTime = 1000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = []}, boundValues = toAM $ Map {unMap = []}, minTime = POSIXTime {getPOSIXTime = 1000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 2000},POSIXTime {getPOSIXTime = 2000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = []}, boundValues = toAM $ Map {unMap = []}, minTime = POSIXTime {getPOSIXTime = 2000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 0)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 3000},POSIXTime {getPOSIXTime = 3000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",0)]}, boundValues = toAM $ Map {unMap = []}, minTime = POSIXTime {getPOSIXTime = 3000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 0)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Party" "Counterparty" (Token "" "") 0)]}], TransactionOutput {txOutWarnings = [TransactionNonPositiveDeposit "Counterparty" "Party" (Token "" "") 0], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",0)]}, boundValues = toAM $ Map {unMap = []}, minTime = POSIXTime {getPOSIXTime = 0}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 1)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 4000},POSIXTime {getPOSIXTime = 4000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",1)]}, boundValues = toAM $ Map {unMap = [("Positive",1)]}, minTime = POSIXTime {getPOSIXTime = 4000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 1)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Party" "Counterparty" (Token "" "") 1)]}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000,Payment "Party" (Party "Party") (Token "" "") 1], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",1)]}, boundValues = toAM $ Map {unMap = [("Positive",1)]}, minTime = POSIXTime {getPOSIXTime = 0}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 0)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 4000},POSIXTime {getPOSIXTime = 4000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",0)]}, boundValues = toAM $ Map {unMap = [("Neutral",1)]}, minTime = POSIXTime {getPOSIXTime = 4000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") 0)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Party" "Party" (Token "" "") 0)]}], TransactionOutput {txOutWarnings = [TransactionNonPositiveDeposit "Party" "Party" (Token "" "") 0], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",0)]}, boundValues = toAM $ Map {unMap = [("Neutral",1)]}, minTime = POSIXTime {getPOSIXTime = 0}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") (-1))]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 4000},POSIXTime {getPOSIXTime = 4000}), txInputs = []}], TransactionOutput {txOutWarnings = [], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",-1)]}, boundValues = toAM $ Map {unMap = [("Negative",1)]}, minTime = POSIXTime {getPOSIXTime = 4000}}, txOutContract = Close})
+  , (POSIXTime {getPOSIXTime = 0}, [TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Counterparty" (Token "" "") 2000000)]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IChoice (ChoiceId "Deposit" "Party") (-1))]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput INotify]},TransactionInput {txInterval = (POSIXTime {getPOSIXTime = 0},POSIXTime {getPOSIXTime = 0}), txInputs = [NormalInput (IDeposit "Counterparty" "Party" (Token "" "") (-1))]}], TransactionOutput {txOutWarnings = [TransactionNonPositiveDeposit "Party" "Counterparty" (Token "" "") (-1)], txOutPayments = [Payment "Counterparty" (Party "Counterparty") (Token "" "") 2000000], txOutState = State {accounts = toAM $ Map {unMap = []}, choices = toAM $ Map {unMap = [(ChoiceId "Deposit" "Party",-1)]}, boundValues = toAM $ Map {unMap = [("Negative",1)]}, minTime = POSIXTime {getPOSIXTime = 0}}, txOutContract = Close})
+  ]
+
+
+-- | A list of test cases and results that should fail.
+invalids :: [(POSIXTime, [TransactionInput], TransactionOutput)]
+invalids =
+  [
+  ]
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Merkle.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Merkle.hs
index 747c053fa..ebe286cb3 100644
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Merkle.hs
+++ b/marlowe-test/src/Spec/Marlowe/Semantics/Merkle.hs
@@ -14,7 +14,6 @@
 {-# LANGUAGE FlexibleContexts #-}
 {-# LANGUAGE RankNTypes #-}
 {-# LANGUAGE RecordWildCards #-}
-{-# LANGUAGE TupleSections #-}
 
 
 module Spec.Marlowe.Semantics.Merkle
diff --git a/marlowe-test/src/Spec/Marlowe/Semantics/Oracle.hs b/marlowe-test/src/Spec/Marlowe/Semantics/Oracle.hs
deleted file mode 100644
index 081e88034..000000000
--- a/marlowe-test/src/Spec/Marlowe/Semantics/Oracle.hs
+++ /dev/null
@@ -1,261 +0,0 @@
------------------------------------------------------------------------------
---
--- Module      :  $Headers
--- License     :  Apache 2.0
---
--- Stability   :  Experimental
--- Portability :  Portable
---
--- | Tests using external semantics oracle.
---
------------------------------------------------------------------------------
-
-
-
-{-# LANGUAGE DeriveGeneric #-}
-{-# LANGUAGE NumericUnderscores #-}
-{-# LANGUAGE OverloadedStrings #-}
-{-# LANGUAGE RecordWildCards #-}
-
-
-module Spec.Marlowe.Semantics.Oracle
-  ( -- * Tests
-    tests
-  ) where
-
-
-import Data.Aeson
-  ( FromJSON(parseJSON)
-  , KeyValue((.=))
-  , ToJSON(toJSON)
-  , Value(Array)
-  , eitherDecode
-  , encode
-  , object
-  , withArray
-  , withObject
-  , (.:)
-  )
-import Data.Aeson.Types (Parser)
-import Data.Function (on)
-import Data.List (sort)
-import Data.String (fromString)
-import Data.Vector ((!))
-import GHC.Generics (Generic)
-import Language.Marlowe.Core.V1.Semantics
-  ( Payment(..)
-  , TransactionInput
-  , TransactionOutput(TransactionOutput, txOutContract, txOutPayments, txOutState, txOutWarnings)
-  , computeTransaction
-  )
-import Language.Marlowe.Core.V1.Semantics.Types (Contract, State(..), Token(Token))
-import Language.Marlowe.FindInputs (getAllInputs)
-import System.Directory (doesFileExist)
-import System.IO
-  (BufferMode(LineBuffering), Handle, IOMode(ReadMode, WriteMode), hGetLine, hPutStrLn, hSetBuffering, openFile)
-import Test.Tasty (TestTree)
-import Test.Tasty.HUnit (assertBool, testCaseSteps)
-
-import qualified Data.ByteString.Lazy.Char8 as LBS8 (pack, unpack)
-import qualified Data.Vector as V (fromList)
-import qualified Language.Marlowe.Extended.V1 as E (Contract(Close), Value(Constant), toCore)
-import qualified PlutusTx.AssocMap as AM (Map, empty, toList)
-
-import qualified Marlowe.Contracts.Escrow as Escrow (escrow)
-import qualified Marlowe.Contracts.Forward as Forward (forward)
-import qualified Marlowe.Contracts.Futures as Futures (future)
-import qualified Marlowe.Contracts.Swap as Swap (swap)
-import qualified Marlowe.Contracts.Trivial as Trivial (trivial)
-import qualified Marlowe.Contracts.ZeroCouponBond as ZeroCouponBond (zeroCouponBond)
-
-
--- | Compare contract execution to the semantics oracle.
---
--- The function reads from a named pipe "orin" and writes to a
--- named pipe "orout". Those same pipes must be connected to the
--- semantics oracle. For example:
---
--- > git clone git@github.com:input-output-hk/marlowe-cardano.git -b 472170bdf77dc9d89bc77861da851d2476b2aa47
--- > nix-shell
--- > cd marlowe-purescript-spec
--- > spago install
--- > spago build
--- > npm install
--- > node index.js <orout >orin
-tests :: TestTree
-tests =
-  testCaseSteps "Semantics Oracle"
-    $ \step ->
-      do
-      okay <- and <$> mapM doesFileExist ["orin", "orout"]
-      if okay
-        then do
-               step "Connecting to semantics oracle . . ."
-               hToOracle   <- openFile "orout" WriteMode
-               hFromOracle <- openFile "orin"  ReadMode
-               hSetBuffering hToOracle   LineBuffering
-               hSetBuffering hFromOracle LineBuffering
-               sequence_
-                 [
-                   do
-                     step $ "Comparing " <> name <> " to oracle . . ."
-                     compareToOracle hToOracle hFromOracle name contract
-                 |
-                   (name, contract) <- contracts
-                 ]
-        else step "No semantics oracle found on pipes \"orin\" and \"orout\"."
-
-
--- | Contracts to be tested.
-contracts :: [(String, E.Contract)]
-contracts =
-  let
-    alice = "Alice"
-    bob = "Bob"
-    charlie = "Charlie"
-    v = E.Constant
-    a = Token "aaaa" "A"
-    b = Token "bbbb" "B"
-    c = Token "cccc" "C"
-  in
-    [
-      ("Escrow"          , Escrow.escrow (v 900_000_000) alice bob charlie 100 200 300 400)
-    , ("Forward"         , Forward.forward alice a (v 10) 100 bob b (v 20) 200 300)
-    , ("Future"          , Futures.future alice bob (v 100) (v 200) 100 [200] 500)
-    , ("Swap"            , Swap.swap alice a (v 100) 100 bob b (v 200) 200 E.Close)
-    , ("Trivial"         , Trivial.trivial alice 100_000_000 70_000_000 0)
-    , ("Zero-Coupon Bond", ZeroCouponBond.zeroCouponBond alice bob 100 200 (v 100_000_000) (v 200_000_000) c E.Close)
-    ]
-
-
--- | A request to the semantics oracle.
-data OracleRequest =
-  OracleRequest
-  {
-    request          :: String
-  , state            :: State
-  , transactionInput :: TransactionInput
-  , coreContract     :: Contract
-  }
-  deriving (Generic, Show)
-
-instance FromJSON OracleRequest
-
-instance ToJSON OracleRequest
-
-
--- | A response from the semantics oracle.
-data OracleResponse =
-    TransactionSuccess TransactionOutput
-  | TransactionError
-  deriving (Generic, Show)
-
-instance FromJSON OracleResponse where
-  parseJSON =
-    withObject "OracleResponse"
-      $ \o ->
-        do
-          success <- o .: "transaction_success"
-          txOutWarnings <- success .: "txOutWarnings"
-          payments      <- success .: "txOutPayments"
-          txOutState    <- success .: "txOutState"
-          txOutContract <- success .: "txOutContract"
-          txOutPayments <- mapM paymentFromJSON payments
-          pure . TransactionSuccess $ TransactionOutput{..}
-
-
-instance ToJSON OracleResponse where
-  toJSON (TransactionSuccess TransactionOutput{..}) =
-    object
-      [
-        "transaction_success" .= object
-                                   [
-                                     "txOutWarnings" .= toJSON txOutWarnings
-                                   , "txOutPayments" .= fmap paymentToJSON txOutPayments
-                                   , "txOutState"    .= toJSON txOutState
-                                   , "txOutContract" .= toJSON txOutContract
-                                   ]
-      ]
-  toJSON _ = "transaction_error"
-
-
--- | Deserialize a payment from JSON.
-paymentFromJSON :: Value -> Parser Payment
-paymentFromJSON =
-  withArray "Payment"
-    $ \v ->
-      do
-        a <- parseJSON $ v ! 0
-        p <- parseJSON $ v ! 1
-        [(c, [(n, i)])] <- parseJSON (v ! 2)
-        pure $ Payment a p (Token (fromString c) (fromString n)) i
-
-
--- | Serialize a payment to JSON.
-paymentToJSON :: Payment -> Value
-paymentToJSON (Payment a p t i) =
-  Array
-    $ V.fromList
-    [
-      toJSON a
-    , toJSON p
-    , toJSON t
-    , toJSON i
-    ]
-
-
--- | Equality test for transaction output.
-eqTransactionOutput :: TransactionOutput -> TransactionOutput -> Bool
-eqTransactionOutput x@TransactionOutput{} y@TransactionOutput{} =
-     txOutWarnings x == txOutWarnings y
-  && txOutPayments x == txOutPayments y
-  && txOutState    x ~~ txOutState    y
-  && txOutContract x == txOutContract y
-eqTransactionOutput _ _ = False
-
-
--- | Equality test for state.
-(~~) :: State -> State -> Bool
-x ~~ y =
-     accounts    x `eqAssocMap` accounts    y
-  && choices     x `eqAssocMap` choices     y
-  && boundValues x `eqAssocMap` boundValues y
-  && minTime     x ==           minTime     y
-
-
--- | Equality test for association lists.
-eqAssocMap :: Ord k => Ord v => AM.Map k v -> AM.Map k v -> Bool
-eqAssocMap = (==) `on` (sort . AM.toList)
-
-
--- | Use static analysis to generate paths through a contract, and then compare execution to the oracle.
-compareToOracle :: Handle -> Handle -> String -> E.Contract -> IO ()
-compareToOracle hToOracle hFromOracle name extended =
-  do
-    Just core <- pure $ E.toCore extended
-    Right paths <- getAllInputs core
-    let
-      accounts = AM.empty
-      choices = AM.empty
-      boundValues = AM.empty
-      request = "compute-transaction"
-    sequence_
-      [
-        let
-          go _ _ _ [] = pure ()
-          go j state coreContract (transactionInput : transactionInputs) =
-            do
-              hPutStrLn hToOracle "```"
-              hPutStrLn hToOracle $ LBS8.unpack $ encode OracleRequest{..}
-              hPutStrLn hToOracle "```"
-              result <- hGetLine hFromOracle
-              actual@TransactionOutput{..} <- pure $ computeTransaction transactionInput state coreContract
-              Right (TransactionSuccess expected) <- pure $ eitherDecode $ LBS8.pack result
-              let match = actual `eqTransactionOutput` expected
-              assertBool (name <> ", path " <> show (i :: Int) <> ", step " <> show (j :: Int)) match
-              go (j + 1) txOutState txOutContract transactionInputs
-        in
-          go 1 State{..} core inputs
-      |
-        (i, (minTime, inputs)) <- zip [1..] paths
-      ]
diff --git a/marlowe-test/src/Spec/Marlowe/Serialization/CoreJson.hs b/marlowe-test/src/Spec/Marlowe/Serialization/CoreJson.hs
index a3c456b9d..3420569d3 100644
--- a/marlowe-test/src/Spec/Marlowe/Serialization/CoreJson.hs
+++ b/marlowe-test/src/Spec/Marlowe/Serialization/CoreJson.hs
@@ -9,12 +9,16 @@
 -- | This suite tests the Json serialization of the Marlowe core module
 --
 -----------------------------------------------------------------------------
+
+
 {-# LANGUAGE OverloadedStrings #-}
 
+
 module Spec.Marlowe.Serialization.CoreJson
   ( tests
   ) where
 
+
 import Control.Arrow (Arrow((***)))
 import Data.Aeson (decode, encode)
 import Data.ByteString (ByteString)
@@ -28,6 +32,7 @@ import Test.QuickCheck.Property (forAll, forAllShrink, withMaxSuccess)
 import Test.Tasty (TestTree, testGroup)
 import Test.Tasty.QuickCheck (testProperty)
 
+
 tests :: TestTree
 tests = testGroup "Core Contract Serialization"
     [ testProperty "Serialise deserialise Contract loops" prop_contractJsonLoops
@@ -40,6 +45,7 @@ tests = testGroup "Core Contract Serialization"
 contractJsonLoops :: Contract -> Property
 contractJsonLoops cont = decode (encode cont) === Just cont
 
+
 -- | Test that JSON decoding inverts encoding for contracts.
 prop_contractJsonLoops :: Property
 prop_contractJsonLoops = withMaxSuccess 1000 $ forAllShrink contractGen shrinkContract contractJsonLoops
@@ -50,6 +56,7 @@ prop_contractJsonLoops = withMaxSuccess 1000 $ forAllShrink contractGen shrinkCo
 marloweParamsJsonLoops :: MarloweParams -> Property
 marloweParamsJsonLoops mp = decode (encode mp) === Just mp
 
+
 -- | Test that JSON decoding inverts encoding for Marlowe parameters.
 prop_marloweParamsJsonLoops :: Property
 prop_marloweParamsJsonLoops = withMaxSuccess 1000 $ forAll gen marloweParamsJsonLoops
@@ -58,6 +65,7 @@ prop_marloweParamsJsonLoops = withMaxSuccess 1000 $ forAll gen marloweParamsJson
       c <- toBuiltin <$> (arbitrary :: Gen ByteString)
       return $ MarloweParams (CurrencySymbol c)
 
+
 -- | Test that JSON decoding inverts encoding for an interval error.
 intervalErrorJsonLoops :: IntervalError -> Property
 intervalErrorJsonLoops ie = decode (encode ie) === Just ie
diff --git a/marlowe-test/src/Spec/Marlowe/Serialization/ExtendedJson.hs b/marlowe-test/src/Spec/Marlowe/Serialization/ExtendedJson.hs
index b93984ddd..0c357bbf4 100644
--- a/marlowe-test/src/Spec/Marlowe/Serialization/ExtendedJson.hs
+++ b/marlowe-test/src/Spec/Marlowe/Serialization/ExtendedJson.hs
@@ -9,18 +9,23 @@
 -- | This suite tests the Json serialization of the Marlowe extended module
 --
 -----------------------------------------------------------------------------
+
+
 {-# LANGUAGE OverloadedStrings #-}
 
+
 module Spec.Marlowe.Serialization.ExtendedJson
   ( tests
   ) where
 
+
 import Data.Aeson (eitherDecodeFileStrict)
 import Language.Marlowe.Extended.V1 (Contract, Module)
 import System.FilePath ((</>))
 import Test.Tasty (TestTree, testGroup)
 import Test.Tasty.HUnit (assertFailure, testCase)
 
+
 tests :: TestTree
 tests = testGroup "Extended Contract Serialization"
     [ testCase "Golden Swap contract" testGoldenSwapContract
@@ -29,9 +34,11 @@ tests = testGroup "Extended Contract Serialization"
 
 -- TODO: Do a small non-property round-trip with example contracts.
 
+
 goldenPath :: FilePath
 goldenPath = "test" </> "Spec" </> "Marlowe" </> "Serialization" </> "golden"
 
+
 -- | Checks that we can decode the Golden JSON Contract for Swap
 testGoldenSwapContract :: IO ()
 testGoldenSwapContract = do
@@ -40,6 +47,7 @@ testGoldenSwapContract = do
         Left err              -> assertFailure err
         Right (_ :: Contract) -> return ()
 
+
 -- | Checks that we can decode the Golden JSON Module for Swap
 -- | TODO: If we are more of these tests, add a helper function with a Proxy type
 testGoldenSwapModule :: IO ()
diff --git a/marlowe-test/src/Spec/Marlowe/Service.hs b/marlowe-test/src/Spec/Marlowe/Service.hs
new file mode 100644
index 000000000..e02ef56f8
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Service.hs
@@ -0,0 +1,73 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Client for Isabelle-based Marlowe testing service.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE LambdaCase #-}
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
+
+
+module Spec.Marlowe.Service
+  ( -- * Testing
+    handle
+  , handleValues
+  ) where
+
+
+import Spec.Marlowe.Service.Random (generateValue)
+import Spec.Marlowe.Service.Serialization (roundtripSerialization)
+import Spec.Marlowe.Service.Types (Request(..), Response(..))
+
+import qualified Data.Aeson as A (Result(..), Value, fromJSON, object, toJSON, (.=))
+import qualified Language.Marlowe.Core.V1.Semantics as Marlowe
+  (computeTransaction, evalObservation, evalValue, playTrace)
+
+
+-- | Respond to a request expressed as JSON.
+handleValues :: A.Value -> IO A.Value
+handleValues request =
+  case A.fromJSON request of
+    A.Success request' -> A.toJSON <$> handle request'
+    A.Error message -> error message
+
+
+-- | Respond to a request.
+handle :: Request -> IO Response
+handle TestRoundtripSerialization{..} =
+  pure
+    . RequestResponse . A.toJSON
+    $ roundtripSerialization typeSerialized valueSerialized
+handle GenerateRandomValue{..} =
+  generateValue size seed typeSerialized
+    >>= \case
+      Right value -> pure . RequestResponse . A.object . pure $ "value" A..= value
+      Left failureResponse -> pure $ ResponseFailure{..}
+handle ComputeTransaction{..} =
+  let
+    valueResponse = A.toJSON $ Marlowe.computeTransaction transactionInput state contract
+  in
+    pure RequestResponse{..}
+handle PlayTrace{..} =
+  let
+    valueResponse = A.toJSON $ Marlowe.playTrace initialTime contract transactionInputs
+  in
+    pure RequestResponse{..}
+handle EvalValue{..} =
+  let
+    valueResponse = A.toJSON $ Marlowe.evalValue environment state value
+  in
+    pure RequestResponse{..}
+handle EvalObservation{..} =
+  let
+    valueResponse = A.toJSON $ Marlowe.evalObservation environment state observation
+  in
+    pure RequestResponse{..}
diff --git a/marlowe-test/src/Spec/Marlowe/Service/Isabelle.hs b/marlowe-test/src/Spec/Marlowe/Service/Isabelle.hs
new file mode 100644
index 000000000..f4c5fcf0e
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Service/Isabelle.hs
@@ -0,0 +1,39 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Test Marlowe's Cardano implementation against the Isabelle-derived test server.
+--
+-----------------------------------------------------------------------------
+
+
+module Spec.Marlowe.Service.Isabelle
+  ( -- * Testing
+    tests
+  ) where
+
+
+import Spec.Marlowe.Service (handleValues)
+import Test.Tasty (TestTree, testGroup)
+
+import qualified Data.Aeson as A
+import qualified Marlowe.Spec.Core (tests)
+
+
+-- | Run the tests.
+tests :: TestTree
+tests =
+  testGroup "Marlowe Client"
+    [
+      Marlowe.Spec.Core.tests
+        $ \request ->
+          do
+            response <- handleValues $ A.toJSON request
+            case A.fromJSON response of
+              A.Success response' -> pure response'
+              A.Error message -> error message
+    ]
diff --git a/marlowe-test/src/Spec/Marlowe/Service/Random.hs b/marlowe-test/src/Spec/Marlowe/Service/Random.hs
new file mode 100644
index 000000000..5a312aa0f
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Service/Random.hs
@@ -0,0 +1,44 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Arbitrary instance for an existentially quantified JSON type.
+--
+-----------------------------------------------------------------------------
+
+
+module Spec.Marlowe.Service.Random
+  ( -- * Testing
+    generateValue
+  ) where
+
+
+import Data.Jsonable (generateJsonable)
+import Spec.Marlowe.Semantics.Arbitrary ()
+import Spec.Marlowe.Service.Serialization (knownJsonTypes)
+import Spec.Marlowe.Service.Types (Seed(..), Size(..))
+import Test.QuickCheck (generate)
+import Test.QuickCheck.Gen (Gen(..))
+import Test.QuickCheck.Random (mkQCGen, newQCGen)
+
+import qualified Data.Aeson as A (Value)
+
+
+-- | Generate an arbitrary value.
+generateValue
+  :: Maybe Size  -- ^ The optional size paramater.
+  -> Maybe Seed  -- ^ The optional seed for the generator.
+  -> String  -- ^ The key for the type.
+  -> IO (Either String A.Value)  -- ^ Either the value or an error message.
+generateValue size seed =
+  mapM (generate' size seed) . generateJsonable knownJsonTypes
+  where
+    generate' :: Maybe Size -> Maybe Seed -> Gen a -> IO a
+    generate' (Just (Size s)) (Just (Seed r)) (MkGen g) = return $ g (mkQCGen r) s
+    generate' Nothing (Just (Seed r)) (MkGen g) = return $ g (mkQCGen r) 30
+    generate' (Just (Size s)) Nothing (MkGen g) = newQCGen >>= \r -> return $ g r s
+    generate' _ _ g = generate g
diff --git a/marlowe-test/src/Spec/Marlowe/Service/Serialization.hs b/marlowe-test/src/Spec/Marlowe/Service/Serialization.hs
new file mode 100644
index 000000000..08a373eb9
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Service/Serialization.hs
@@ -0,0 +1,106 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Test of Marlowe's Cardano JSON implementation against the reference implementation.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
+
+
+module Spec.Marlowe.Service.Serialization
+  ( -- * Types
+    SerializationResponse(..)
+  , knownJsonTypes
+    -- * Testing
+  , roundtripSerialization
+  ) where
+
+
+import Control.Applicative ((<|>))
+import Data.Aeson (FromJSON(..), ToJSON(..))
+import Data.Jsonable (JsonableType(JsonableType), KnownJsonable, isKnownJson, roundTripJsonable)
+import Data.Proxy (Proxy(..))
+import Spec.Marlowe.Semantics.Arbitrary ()
+
+import qualified Data.Aeson as A (Value, object, withObject, (.:), (.=))
+import qualified Language.Marlowe.Core.V1.Semantics as Marlowe
+import qualified Language.Marlowe.Core.V1.Semantics.Types as Marlowe
+
+
+-- | Response to a round-trip serialization request.
+data SerializationResponse =
+    -- | Success.
+    SerializationSuccess
+    {
+      valueReserialized :: A.Value  -- ^ The reserialized value.
+    }
+    -- | The type was not known.
+  | UnknownType
+    {
+      unknownType :: String  -- ^ The type.
+    }
+    -- | The deserialization or serialization failed.
+  | SerializationError
+    {
+      serializationError :: String  -- ^ The error message.
+    }
+  deriving (Eq, Ord, Read, Show)
+
+instance ToJSON SerializationResponse where
+  toJSON SerializationSuccess{..} = A.object . pure $ "serialization-success" A..= valueReserialized
+  toJSON UnknownType{..} = A.object . pure $ "unknown-type" A..= unknownType
+  toJSON SerializationError{..} = A.object . pure $ "serialization-error" A..= serializationError
+
+instance FromJSON SerializationResponse where
+  parseJSON =
+    A.withObject "SerializationResponse"
+      $ \o ->
+            (SerializationSuccess <$> o A..: "serialization-success")
+        <|> (UnknownType <$> o A..: "unknown-type")
+        <|> (SerializationError <$> o A..: "serialization-error")
+
+
+-- | Deserialize and then serialize a value.
+roundtripSerialization
+  :: String  -- ^ The key to the type.
+  -> A.Value  -- ^ The value.
+  -> SerializationResponse  -- ^ The result.
+roundtripSerialization typeSerialized valueSerialized =
+  if isKnownJson knownJsonTypes typeSerialized
+    then case roundTripJsonable knownJsonTypes typeSerialized valueSerialized of
+             Right valueReserialized -> SerializationSuccess{..}
+             Left serializationError -> SerializationError{..}
+    else UnknownType typeSerialized
+
+
+-- | List of known types that can be serialized and deserialized as JSON.
+knownJsonTypes :: KnownJsonable
+knownJsonTypes =
+  [
+    JsonableType "Core.Action" (Proxy :: Proxy Marlowe.Action)
+  , JsonableType "Core.Bound" (Proxy :: Proxy Marlowe.Bound)
+  , JsonableType "Core.Case" (Proxy :: Proxy (Marlowe.Case Marlowe.Contract))
+  , JsonableType "Core.ChoiceId" (Proxy :: Proxy Marlowe.ChoiceId)
+  , JsonableType "Core.Contract" (Proxy :: Proxy Marlowe.Contract)
+  , JsonableType "Core.Token" (Proxy :: Proxy Marlowe.Token)
+  , JsonableType "Core.Payee" (Proxy :: Proxy Marlowe.Payee)
+  , JsonableType "Core.Input" (Proxy :: Proxy Marlowe.Input)
+  , JsonableType "Core.Observation" (Proxy :: Proxy Marlowe.Observation)
+  , JsonableType "Core.Value" (Proxy :: Proxy (Marlowe.Value Marlowe.Observation))
+  , JsonableType "Core.Party" (Proxy :: Proxy Marlowe.Party)
+  , JsonableType "Core.State" (Proxy :: Proxy Marlowe.State)
+  , JsonableType "Core.Payment" (Proxy :: Proxy Marlowe.Payment)
+  , JsonableType "Core.Transaction" (Proxy :: Proxy Marlowe.TransactionInput)
+  , JsonableType "Core.TransactionOutput" (Proxy :: Proxy Marlowe.TransactionOutput)
+  , JsonableType "Core.TransactionWarning" (Proxy :: Proxy Marlowe.TransactionWarning)
+  , JsonableType "Core.TransactionError" (Proxy :: Proxy Marlowe.TransactionError)
+  , JsonableType "Core.IntervalError" (Proxy :: Proxy Marlowe.IntervalError)
+  ]
diff --git a/marlowe-test/src/Spec/Marlowe/Service/Types.hs b/marlowe-test/src/Spec/Marlowe/Service/Types.hs
new file mode 100644
index 000000000..6bcbb7579
--- /dev/null
+++ b/marlowe-test/src/Spec/Marlowe/Service/Types.hs
@@ -0,0 +1,172 @@
+-----------------------------------------------------------------------------
+--
+-- Module      :  $Headers
+-- License     :  Apache 2.0
+--
+-- Stability   :  Experimental
+-- Portability :  Portable
+--
+-- | Marlowe types for the test service client.
+--
+-----------------------------------------------------------------------------
+
+
+{-# LANGUAGE GeneralizedNewtypeDeriving #-}
+{-# LANGUAGE LambdaCase #-}
+{-# LANGUAGE OverloadedStrings #-}
+{-# LANGUAGE RecordWildCards #-}
+
+
+module Spec.Marlowe.Service.Types
+  ( -- * Types
+    Request(..)
+  , Response(..)
+  , Seed(..)
+  , Size(..)
+  ) where
+
+
+import Control.Applicative ((<|>))
+import Data.Aeson (FromJSON(..), ToJSON(..))
+import Plutus.V1.Ledger.Api (POSIXTime(..))
+
+import qualified Data.Aeson as A (Value(Object, String), object, withObject, (.:), (.:?), (.=))
+import qualified Data.Aeson.Types as A (Parser)
+import qualified Language.Marlowe.Core.V1.Semantics as Marlowe
+import qualified Language.Marlowe.Core.V1.Semantics.Types as Marlowe
+
+newtype Size = Size Int deriving (Eq, Show, ToJSON, FromJSON)
+newtype Seed = Seed Int deriving (Eq, Show, ToJSON, FromJSON)
+
+data Request =
+    TestRoundtripSerialization
+    {
+      typeSerialized :: String
+    , valueSerialized :: A.Value
+    }
+  | GenerateRandomValue
+    {
+      typeSerialized :: String
+    , size :: Maybe Size
+    , seed :: Maybe Seed
+    }
+  | ComputeTransaction
+    {
+      transactionInput :: Marlowe.TransactionInput
+    , contract :: Marlowe.Contract
+    , state :: Marlowe.State
+    }
+  | PlayTrace
+    {
+      transactionInputs :: [Marlowe.TransactionInput]
+    , contract :: Marlowe.Contract
+    , initialTime :: POSIXTime
+    }
+  | EvalValue
+    {
+      environment :: Marlowe.Environment
+    , state :: Marlowe.State
+    , value :: Marlowe.Value Marlowe.Observation
+    }
+  | EvalObservation
+    {
+      environment :: Marlowe.Environment
+    , state :: Marlowe.State
+    , observation :: Marlowe.Observation
+    }
+    deriving (Eq, Show)
+
+instance FromJSON Request where
+  parseJSON =
+    A.withObject "Request"
+      $ \o ->
+        (o A..: "request" :: A.Parser String)
+          >>= \case
+            "test-roundtrip-serialization" -> TestRoundtripSerialization <$> o A..: "typeId" <*> o A..: "json"
+            "generate-random-value"        -> GenerateRandomValue <$> o A..: "typeId" <*> o A..:? "size" <*> o A..:? "seed"
+            "compute-transaction"          -> ComputeTransaction <$> o A..: "transactionInput" <*> o A..: "coreContract" <*> o A..: "state"
+            "playtrace"                    -> PlayTrace <$> o A..: "transactionInputs" <*> o A..: "coreContract" <*> (POSIXTime <$> o A..: "initialTime")
+            "eval-value"                   -> EvalValue <$> o A..: "environment" <*> o A..: "state" <*> o A..: "value"
+            "eval-observation"             -> EvalObservation <$> o A..: "environment" <*> o A..: "state" <*> o A..: "observation"
+            request                        -> fail $ "Request not understood: " <> show request <> "."
+
+instance ToJSON Request where
+  toJSON TestRoundtripSerialization{..} =
+    A.object
+      [
+        "request" A..= ("test-roundtrip-serialization" :: String)
+      , "typeId" A..= typeSerialized
+      , "json"  A..= valueSerialized
+      ]
+  toJSON GenerateRandomValue{..} =
+    A.object
+      [
+        "request" A..= ("generate-random-value" :: String)
+      , "typeId" A..= typeSerialized
+      , "size" A..= size
+      , "seed" A..= seed
+      ]
+  toJSON ComputeTransaction{..} =
+    A.object
+      [
+        "request" A..= ("compute-transaction" :: String)
+      , "transactionInput" A..= transactionInput
+      , "coreContract" A..= contract
+      , "state" A..= state
+      ]
+  toJSON PlayTrace{..} =
+    A.object
+      [
+        "request" A..= ("playtrace" :: String)
+      , "transactionInputs" A..= transactionInputs
+      , "coreContract" A..= contract
+      , "initialTime" A..= getPOSIXTime initialTime
+      ]
+  toJSON EvalValue{..} =
+    A.object
+      [
+        "request" A..= ("eval-value" :: String)
+      , "environment" A..= environment
+      , "state" A..= state
+      , "value" A..= value
+      ]
+  toJSON EvalObservation{..} =
+    A.object
+      [
+        "request" A..= ("eval-value" :: String)
+      , "environment" A..= environment
+      , "state" A..= state
+      , "observation" A..= observation
+      ]
+
+data Response =
+    InvalidRequest
+    {
+      errorInvalid :: String
+    }
+  | UnknownRequest
+  | RequestResponse
+    {
+      valueResponse :: A.Value
+    }
+  | RequestNotImplemented
+  | RequestTimeOut
+  | ResponseFailure
+    {
+      failureResponse :: String
+    }
+    deriving (Eq, Ord, Read, Show)
+
+instance FromJSON Response where
+    parseJSON (A.String "UnknownRequest") = return UnknownRequest
+    parseJSON (A.String "RequestNotImplemented") = return RequestNotImplemented
+    parseJSON (A.Object v) = (InvalidRequest <$> v A..: "invalid-request") <|> (RequestResponse <$> v A..: "request-response")
+    parseJSON _ = fail "Response must be either a string or an A.object"
+
+instance ToJSON Response where
+  toJSON UnknownRequest = "UnknownRequest"
+  toJSON RequestNotImplemented = "RequestNotImplemented"
+  toJSON RequestTimeOut = "RequestTimeOut"
+  toJSON (InvalidRequest err) = A.object . pure $ "invalid-request" A..= err
+  toJSON (RequestResponse res) = A.object . pure $ "request-response" A..= res
+  toJSON (ResponseFailure err) = A.object . pure $ "invalid-request" A..= err
```