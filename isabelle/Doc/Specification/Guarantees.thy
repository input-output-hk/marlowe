(*<*)
theory Guarantees
  imports
      Core.SemanticsTypes
      Core.AssetsPreservation
      Core.Timeout
      Core.QuiescentResult
      Core.SingleInputTransactions
      Core.CloseSafe
      Core.TransactionBound

begin
(*>*)

chapter \<open>Marlowe Guarantees \label{sec:marlowe-guarantees} \<close>

text \<open>We can also use the Isabelle proof assistant to prove that the Marlowe semantics presents certain
desirable properties, such as that assets are preserved and anything unspent is returned to users by
the end of the execution of any contract.\<close>

subsubsection \<open>Auxillary Functions\label{sec:playTrace}\<close>

text \<open>Many of the proofs in this chapter rely on function @{const playTrace} and
@{const playTraceAux} that execute a sequence of transactions using the Marlowe semantics defined in
@{const computeTransaction}. They also rely on starting from a valid and positive contract state,
@{const validAndPositive_state} and a function @{const maxTimeContract} that extracts the latest
timeout from the contract.\<close>

text \<open>@{const playTrace} :: @{typeof playTrace}\<close>
text \<open>@{const playTraceAux} :: @{typeof playTraceAux}\<close>
text \<open>@{const validAndPositive_state} :: @{typeof validAndPositive_state}\<close>
text \<open>@{const maxTimeContract} :: @{typeof maxTimeContract}\<close>

section \<open>Assets Preservation\<close>

text \<open>

One of the dangers of using smart contracts is that a badly written one can potentially lock its
funds forever.\<close>
text \<open>By the end of a Marlowe contract, all the assets paid to the contract must be distributed
back, in some way, to a subset of the participants. To ensure this behaviour we
proved two properties: ``MultiAssets Preservation'' and ``Contracts Always Close''.\<close>

text \<open>
Regarding asset preservation, tokens are not created nor destroyed by the semantics. Formally speaking,
if a transaction is computed successfully, the sum of the assets stored in the previous state and 
the assets deposited by a transaction are equal to the assets in the new state and possible external payments
(from internal account to external party).
\<close>

text \<open>@{thm computeTransaction_preserves_assets}\<close>

text \<open>If calling computeTransaction yields an error, then the transaction is invalid and should not be
part of the blockchain, preserving assets in its current state.\<close>

section \<open>Contracts Always Close\<close>

text \<open>

For every Marlowe Contract there is a maximum time that allows any participant
to create an empty transaction that will close the contract succesfuly. 
\<close>

text \<open>@{thm [display,names_short, margin=40] timeOutTransaction_does_not_fail}\<close>

text \<open>Moreover, that transaction empties the account and produces payments for any lingering assets\<close>

text \<open>@{thm [display,names_short, margin=40] timedOutTransaction_preserves_assets}\<close>

section \<open>Positive Accounts\<close>

text \<open>

There are some values for State that are allowed by its type but make no sense, especially in the
case of Isabelle semantics where we use lists of key values to represent maps:
\begin{enumerate}
\item The lists represent maps, so they should have no repeated keys (@{term valid_map}).
\item Two equal maps should be represented equally, so we force keys to be in ascending order  (@{term valid_map}).
\item Only the accounts that contain a positive amount are relevant (@{term allAccountsPositiveState}).
\end{enumerate}
\<close>



text \<open>@{code_stmts validAndPositive_state constant: validAndPositive_state valid_state valid_map allAccountsPositive allAccountsPositiveState (Haskell)}\<close>

text \<open>If the accounts are valid and possitive, then applying an input preserves that property.\<close>

text \<open>@{thm [display,names_short, margin=40] playTraceAux_preserves_validAndPositive_state}\<close>

section \<open>Quiescent Result\<close>

text \<open>

A contract is quiescent if and only if the root construct is @{term When}, or if the contract is
@{term Close} and all accounts are empty. If an input @{term State} is valid and accounts are
positive, then the output will be quiescent, @{const isQuiescent}.
\<close>

text \<open>

The following always produce quiescent contracts:
\begin{itemize}
\item reductionLoop \secref{sec:reductionloop}
\item reduceContractUntilQuiescent \secref{sec:reduceContractUntilQuiescent}
\item applyAllInputs  \secref{sec:applyAllInputs}
\item computeTransaction  \secref{sec:computeTransaction}
\item playTrace  \secref{sec:playTrace}
\end{itemize}
\<close>

text \<open>@{thm playTraceIsQuiescent}\<close>

section \<open>Reducing a Contract until Quiescence Is Idempotent\<close>

text \<open>Once a contract is quiescent, further reduction will not change the contract or state,
and it will not produce any payments or warnings.\<close>

text \<open>@{thm [display,names_short, margin=40] reduceContractUntilQuiescentIdempotent}\<close>

section \<open>Split Transactions Into Single Input Does Not Affect the Result\<close>

text \<open>Applying a list of inputs to a contract produces the same result as applying each input
singly.\<close>

text \<open>@{thm playTraceAuxToSingleInputIsEquivalent }\<close>

subsection \<open>Termination Proof\<close>

text \<open>

Isabelle automatically proves termination for most function. However, this is not the case for
@{const reductionLoop}, but it is manually proved that the reduction loop monotonically reduces the
size of the contract (except for @{term Close}, which reduces the number of accounts), this is
sufficient to prove termination.

@{thm reduceContractStepReducesSize}

\<close>

subsection \<open>All Contracts Have a Maximum Time\label{sec:max-time-guarantee}\<close>

text \<open>If one sends an empty transaction with time equal to @{const maxTimeContract}, then the
contract will close.\<close>

text \<open>@{thm [mode=Rule,names_short] timedOutTransaction_closes_contract}\<close>

subsection \<open>Contract Does Not Hold Funds After it Closes\<close>

text \<open>Funds are not held in a contract after it closes.\<close>

text \<open>@{thm closeIsSafe}\<close>

subsection \<open>Transaction Bound\label{sec:transaction-bound}\<close>

text \<open>There is a maximum number of transaction that can be accepted by a contract.\<close>

(* should we have a maxTransactions :: Contract \<Rightarrow> Int in the semantics? *)

text \<open>@{thm playTrace_only_accepts_maxTransactionsInitialState}\<close>

(*<*)
end
(*>*)
