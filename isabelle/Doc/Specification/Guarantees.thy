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

text \<open>We can also use the Isabelle proof assistant to prove that the Marlowe semantics
 presents certain desirable properties, such as that assets are preserved and anything
 unspent is returned to users by the end of the execution of any contract.\<close>

text \<open>To keep this section concise, whenever we introduce a helper function we'll 
provide a brief explanation and the type signature. We'll also add the name of the 
theories and files to access the full definitions.\<close>

section \<open>Positive Accounts\<close>

text \<open>The Marlowe State represents the \<^emph>\<open>accounts\<close>, \<^emph>\<open>choices\<close> and \<^emph>\<open>boundValues\<close> Maps as
associative lists \secref{sec:state}. While we make proofs in Isabelle, we often need to
 assert that two Maps are equal, and with the list representation, this means that the 
maps should be in the same order and without duplicate keys. To ensure this, we have the following helper located 
in the MList.thy theory\<close>

text \<open>
\<^item> valid\_map :: @{typeof valid_map}
\<close>

text \<open>Moreover, we use the following function to ensure that the Maps are valid and the
 \<^emph>\<open>accounts\<close> only have positive values\<close>

text \<open>
\<^item> validAndPositive\_state :: @{typeof validAndPositive_state}
\<close>

text \<open>
The following theorem asserts that if the State is valid before computing a transaction,
it is also valid after.
\<close>

text \<open>\<^bold>\<open>lemma\<close> \<^emph>\<open>computeTransaction\_preserves\_validAndPositive\_state\<close>:@{thm [display,names_short, margin=40] computeTransaction_preserves_validAndPositive_state}\<close>

text \<open>The function and lemma are located in \<^emph>\<open>PositiveAccounts.thy\<close>.\<close>

section \<open>Finite contracts\label{sec:finite-contracts}\<close>

text \<open>
All contracts are finite and will end at a particular time. We can use the following function
(located in Semantics.thy) to see what that time is\<close>

(* We use a hardcoded type as aliases get expanded *)
text \<open>
\<^item> maxTimeContract :: \isa{Contract\ {\isasymRightarrow}\ POSIXTime}\<close>

text 
\<open>
The Blockchain doesn't have the notion of a cronjob, so it can't refund participants
after the contract timeouts on its own. Instead we can guarantee that computing a transaction
without inputs with a validity interval that starts after the max time will always succeed 
\<close>

text \<open>\<^bold>\<open>corollary\<close> \<^emph>\<open>timeOutTransaction\_does\_not\_fail\<close>: @{thm [display,names_short, margin=60] timeOutTransaction_does_not_fail}\<close>

text \<open>Moreover, we can use the function \<^emph>\<open>isClosedAndEmpty\<close> to
assert that the previous transaction will result in a Close contract with empty accounts.\<close>

text \<open>
\<^item> isClosedAndEmpty :: @{typeof isClosedAndEmpty}\<close>

text \<open>\<^bold>\<open>theorem\<close> \<^emph>\<open>timedOutTransaction\_closes\_contract\<close>:@{thm [display,names_short, margin=60] timedOutTransaction_closes_contract}\<close>

text \<open>The helper and lemmas are located in \<^emph>\<open>Timeout.thy\<close>.\<close>


subsection \<open>Transaction Bound\label{sec:transaction-bound}\<close>

text \<open>There is a maximum number of transactions that can be accepted by a contract.\<close>

text \<open>
\<^item> maxTransactionsInitialState :: @{typeof maxTransactionsInitialState}
\<close>

text \<open>We can prove that if we run a successful trace, the number of transactions won't
exceed this value\<close>

(* should we have a maxTransactions :: Contract \<Rightarrow> Int in the semantics? *)

text \<open>\<^bold>\<open>lemma\<close> \<^emph>\<open>playTrace\_only\_accepts\_maxTransactionsInitialState\<close>: @{thm  [display,names_short, margin=60] playTrace_only_accepts_maxTransactionsInitialState}\<close>

text \<open>The helper and lemma are located in \<^emph>\<open>TransactionBound.thy\<close>.\<close>

subsection "Close is safe"
text \<open>Computing a transaction on a Closed contract doesn't produce any warnings \<close>
text \<open>\<^bold>\<open>theorem\<close> \<^emph>\<open>closeIsSafe\<close>: @{thm closeIsSafe}\<close>

text \<open>This theorem is located in \<^emph>\<open>CloseSafe.thy\<close>.\<close>

section \<open>Assets Preservation\<close>

text \<open>

One of the dangers of using smart contracts is that a badly written one can potentially lock its
funds forever.\<close>

text \<open>By the end of a Marlowe contract, all the assets paid to the contract must be returned to a subset of the participants. To ensure this behaviour we
proved two properties: ``MultiAssets Preservation'' and ``Refund after timeout''.\<close>

subsection "Multi assets preservation"

text \<open>To express this theory we need the following helper functions\<close>

text \<open>
\<^item> assetsInExternalPayments :: @{typeof assetsInExternalPayments}
\<^item> assetsInTransaction :: @{typeof assetsInTransaction}
\<^item> assetsInState :: @{typeof assetsInState}
\<close>

text \<open>These functions extracts the \<^emph>\<open>amount\<close> of \<^emph>\<open>token\<close> available in different 
structures. We store this information in a new type called \<^emph>\<open>Assets\<close>, that allow us 
to do addition and subtraction keeping the token information \<^footnote>\<open>The Assets type is located
in MultiAssets.thy, the functions and theorem are in AssetPreservation.thy\<close>.\<close>

text \<open>
The following theorem proves that tokens are not created nor destroyed by the semantics. Formally speaking,
if a transaction is computed successfully, the sum of the assets stored in the previous state and
the assets deposited by a transaction are equal to the assets in the new state and possible external payments
(from internal account to external party).
\<close>


text \<open>\<^bold>\<open>theorem\<close> \<^emph>\<open>computeTransaction\_preserves\_assets\<close>: @{thm [display,names_short, margin=40] computeTransaction_preserves_assets}\<close>

text \<open>If calling \<^emph>\<open>computeTransaction\<close> yields an error, then the transaction is invalid and should not be
part of the blockchain, preserving assets in its current state.\<close>

subsection \<open>Refund after timeout\<close>

text \<open>
In section \secref{sec:finite-contracts} we proved that there is a maximum time that 
allows any participant to create an empty transaction that will close the contract 
successfully.
\<close>

text \<open>The following theorem proves that the transaction also preserves assets\<close>

text \<open>\<^bold>\<open>theorem\<close> \<^emph>\<open>timedOutTransaction\_preserves\_assets\<close>@{thm [display,names_short, margin=60] timedOutTransaction_preserves_assets}\<close>

text \<open>This theorem can be found on the \<^emph>\<open>Timeout.thy\<close> theory.\<close>

section \<open>Quiescent\<close>

text \<open>

A contract is quiescent iff it is terminated or is awaiting an external Input \secref{sec:Quiescent}.
If calling \<^emph>\<open>computeTransaction\<close> produces a valid \<^emph>\<open>TransactionOutput\<close>, then the continuation
is quiescent.
\<close>

text \<open>
\<^bold>\<open>theorem\<close> \<^emph>\<open>computeTransactionIsQuiescent\<close>: @{thm [display,names_short, margin=60] computeTransactionIsQuiescent}
\<close>

text \<open>The theorem and helper function are located in \<^emph>\<open>QuiescentResult.thy\<close>.\<close>


text \<open>Moreover, once a contract is quiescent, further reduction will not change the contract or state,
and it will not produce any payments or warnings.\<close>

text \<open>\<^bold>\<open>lemma\<close> \<^emph>\<open>reduceContractUntilQuiescentIdempotent\<close>:@{thm [display,names_short, margin=60] reduceContractUntilQuiescentIdempotent}\<close>

text \<open>This lemma can be found on \<^emph>\<open>SingleInputTransactions.thy\<close>\<close>

section \<open>Split Transactions Into Single Input Does Not Affect the Result\<close>

text \<open>When we compute a transaction or play a trace we include zero or more \<^emph>\<open>Input\<close>s per \<^emph>\<open>Transaction\<close>.
The following function expands a list of transactions with multiple Inputs into a list
 of transactions of single input.\<close>

text \<open>
\<^item> traceListToSingleInput :: @{typeof traceListToSingleInput}
\<close>

text \<open>We can then prove that playing a trace with multiple inputs per transaction is the
same as playing the trace with a single input per transaction.\<close>

text \<open>\<^bold>\<open>theorem\<close> \<^emph>\<open>traceToSingleInputIsEquivalent\<close>: @{thm  [display,names_short, margin=60]  traceToSingleInputIsEquivalent }\<close>

text \<open>The helper and theorem are located in  \<^emph>\<open>SingleInputTransactions.thy\<close> \<close>


(*<*)
end
(*>*)
