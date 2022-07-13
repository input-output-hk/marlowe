(*<*)
theory Guarantees
  imports       
      Core.SemanticsTypes 
      Core.MoneyPreservation 
      Core.QuiescentResult
      Core.SingleInputTransactions
      Core.Timeout
      Core.TransactionBound
 
begin
(*>*)

chapter \<open>Marlowe Guarantees\<close>
text \<open>TODO: add human readable version of the important theorems and lemmas\<close>

section \<open>Money Preservation\<close>
text \<open>TODO: Money preservation\<close>
text \<open>@{thm playTrace_preserves_money}\<close>

section \<open>Positive Accounts\<close>
text \<open>TODO: Positive accounts\<close>
text \<open>@{thm playTraceAux_preserves_validAndPositive_state}\<close>

section \<open>Quiescent Result\<close>
text \<open>TODO: definition of Quiescent\<close>
text
\<open>
The following always produce quiescent contracts:
\<^item> reductionLoop \secref{sec:reductionloop}
\<^item> reduceContractUntilQuiescent \secref{sec:reduceContractUntilQuiescent}
\<^item> applyAllInputs  \secref{sec:applyAllInputs}
\<^item> computeTransaction  \secref{sec:computeTransaction}
\<^item> playTrace  \secref{sec:playTrace} 
\<close>

text \<open>@{thm playTraceIsQuiescent}\<close>
text \<open>TODO: explanation of theorem\<close>

section \<open>reduceContractUntilQuiescent is idempotent\<close>
text \<open>TODO: explain\<close>
text \<open>@{thm reduceContractUntilQuiescentIdempotent }\<close>

section \<open>Split Transactions Into Single Input Does Not Affect the Result\<close>
text \<open>TODO: explain\<close>
text \<open>@{thm playTraceAuxToSingleInputIsEquivalent }\<close>


section \<open>Contracts Always Close\<close>

text \<open>TODO: proofs around contracts always close and Funds are not held after it close\<close>
(* Do we have or need a lemma that accounts are empty after close? *)

subsection \<open>Termination Proof\<close>
text \<open>TODO: adapt text from section 5.1 "Termination proof" from the 
2019 paper.\<close>

subsection \<open>All Contracts Have a Maximum Time\<close>
text \<open>If we send an empty transaction with time equal to maxTimeContract, the contract will close\<close>
text \<open>TODO: explain\<close>
text \<open>@{thm [mode=Rule,names_short] timedOutTransaction_closes_contract}\<close>

subsection \<open>Contract Does Not Hold Funds After it Closes\<close>
text \<open>TODO: Funds are not held after it close\<close>

subsection \<open>Transaction Bound\<close>
text \<open>There is a maximum number of transaction that can be accepted by a contract\<close>

(* should we have a maxTransactions :: Contract \<Rightarrow> Int in the semantics? *)
text \<open>@{thm playTrace_only_accepts_maxTransactionsInitialState}\<close>

(*<*)
end
(*>*)