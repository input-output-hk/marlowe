(*<*)
theory Escrow
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin
(*>*)
section \<open>Escrow contract\<close>
text \<open>An escrow contract is for the purchase of an item at a price.
The buyer may complain that there is a problem, asking for a refund.
If the seller disputes that complaint, then a mediator decides.
\<close>
subsection \<open>Contract definition\<close>
text \<open>The participants of the contract are:\<close>
definition "seller = Role (BS ''Seller'')"
definition "buyer = Role (BS ''Buyer'')"
definition "mediator = Role (BS ''Mediator'')"
text \<open>An escrow contract takes as arguments the price, token
and the deadlines that apply for the payment, the complaint, the dispute and
the mediation.
\<close>
record EscrowArgs =
  price             :: Value
  token             :: Token
  paymentDeadline   :: Timeout
  complaintDeadline :: Timeout
  disputeDeadline   :: Timeout
  mediationDeadline :: Timeout
text \<open>The contract is built in multiple steps. The innermost step is the
mediation step, where the mediator either confirms or dismisses a claim about
a problem with the transaction. In case the mediator dismisses the claim the
seller is paid, in case the mediator confirms the claim, the contract is closed
and the buyer refunded implicitly:
\<close>
fun mediation :: "EscrowArgs \<Rightarrow> Contract" where
  "mediation args =
    When
      [ Case (Choice (ChoiceId (BS ''Dismiss claim'') mediator) [Bound 0 0])
          (Pay buyer (Account seller) (token args) (price args) Close)
      , Case (Choice (ChoiceId (BS ''Confirm claim'') mediator) [Bound 1 1]) Close
      ] (mediationDeadline args) Close"
text \<open>In case a problem is reported by the buyer, the seller has to either confirm or dispute the
problem. In case the seller confirms the problem, the buyer is refunded implicitly.
Disputing the problem leads to the mediation step defined above.\<close>
fun dispute :: "EscrowArgs \<Rightarrow> Contract" where
  "dispute args =
    When
      [ Case (Choice (ChoiceId (BS ''Confirm problem'') seller) [Bound 1 1]) Close
      , Case (Choice (ChoiceId (BS ''Dispute problem'') seller) [Bound 0 0]) (mediation args)
      ] (disputeDeadline args) Close"
text \<open>The buyer can either report that everything is alright with transaction or a problem. When
a problem is reported the funds are placed in the buyer's account and the contract continues with the
dispute step defined above.\<close>
fun report :: "EscrowArgs \<Rightarrow> Contract" where
  "report args =
    When
      [ Case (Choice (ChoiceId (BS ''Everything is alright'') buyer) [Bound 0 0]) Close
      , Case (Choice (ChoiceId (BS ''Report problem'') buyer) [Bound 1 1])
          (Pay (seller) (Account buyer) (token args) (price args) (dispute args))
      ] (complaintDeadline args) Close"
text \<open>The escrow contract waits for the buyer to deposit and then continues with the report step
defined above.\<close>
fun escrow :: "EscrowArgs \<Rightarrow> Contract" where
  "escrow args =
    When
      [ Case (Deposit seller buyer (token args) (price args)) (report args) ]
      (paymentDeadline args) Close"
(*<*)
definition "exampleArgs =
  \<lparr> price = Constant 10
  , token = Token (BS '''') (BS '''')
  , paymentDeadline = 1664812800000
  , complaintDeadline = 1664816400000
  , disputeDeadline = 1664820420000
  , mediationDeadline = 1664824440000
  \<rparr>"
definition "escrowExample = escrow exampleArgs"
(*>*)
subsection \<open>Possible Outcomes\<close>
text \<open>There are four possible outcomes for the escrow contract.\<close>
subsubsection \<open>Everything is alright\<close>
text \<open>
Steps:
\begin{enumerate}
\item Buyer deposits funds into seller's account.
\item Buyer reports that everything is alright.
\end{enumerate}
Outcome: Seller receives purchase price.
\<close>
(*<*)
definition
  "everythingIsAlrightTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit seller buyer (token exampleArgs) 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Everything is alright'') buyer) 0 ]
      \<rparr>
    ]
  "
definition
  "everythingIsAlrightPayments =
    [ Payment seller (Party seller) (token exampleArgs) 10 ]
  "
proposition
 "playTrace 0 escrowExample everythingIsAlrightTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = everythingIsAlrightPayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: everythingIsAlrightPayments_def
              seller_def buyer_def exampleArgs_def)
     done
(*>*)
subsubsection \<open>Confirm problem\<close>
text \<open>
Steps:
\begin{enumerate}
\item Buyer deposits funds into seller's account.
\item Buyer reports that there is a problem.
\item Seller confirms that there is a problem.
\end{enumerate}
Outcome: Buyer receives refund.
\<close>
(*<*)
definition
  "confirmProblemTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit seller buyer (token exampleArgs) 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') buyer) 1 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Confirm problem'') seller) 1 ]
      \<rparr>
    ]
  "
definition
  "confirmProblemPayments =
    [ Payment seller (Account buyer) (token exampleArgs) 10
    , Payment buyer (Party buyer) (token exampleArgs) 10
    ]
  "
proposition
 "playTrace 0 escrowExample confirmProblemTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = confirmProblemPayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: confirmProblemPayments_def
              seller_def buyer_def mediator_def exampleArgs_def)
     done
(*>*)
subsubsection \<open>Dismiss claim\<close>
text \<open>
\begin{enumerate}
\item Buyer deposits funds into seller's account.
\item Buyer reports that there is a problem.
\item Seller disputes that there is a problem.
\item Mediator dismisses the buyer's claim.
\end{enumerate}
Outcome: Seller receives purchase price.
\<close>
(*<*)
definition
  "dismissClaimTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit seller buyer (token exampleArgs) 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') buyer) 1 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dispute problem'') seller) 0 ]
      \<rparr>
   ,  \<lparr> interval = (1664821400000, 1664822400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dismiss claim'') mediator) 0 ]
      \<rparr>
    ]
  "
definition
  "dismissClaimPayments =
    [ Payment seller (Account buyer) (token exampleArgs) 10
    , Payment buyer (Account seller) (token exampleArgs) 10
    , Payment seller (Party seller) (token exampleArgs) 10
    ]
  "
proposition
 "playTrace 0 escrowExample dismissClaimTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = dismissClaimPayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: dismissClaimPayments_def
              seller_def buyer_def mediator_def exampleArgs_def)
     done
(*>*)
subsubsection \<open>Confirm claim\<close>
text \<open>
\begin{enumerate}
\item Buyer deposits funds into seller's account.
\item Buyer reports that there is a problem.
\item Seller disputes that there is a problem.
\item Mediator confirms the buyer's claim.
\end{enumerate}
Outcome: Buyer receives refund.
\<close>
(*<*)
definition
  "confirmClaimTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit seller buyer (token exampleArgs) 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') buyer) 1 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dispute problem'') seller) 0 ]
      \<rparr>
   ,  \<lparr> interval = (1664821400000, 1664822400000)
      , inputs = [ IChoice (ChoiceId (BS ''Confirm claim'') mediator) 1 ]
      \<rparr>
    ]
  "
definition
  "confirmClaimPayments =
    [ Payment seller (Account buyer) (token exampleArgs) 10
    , Payment buyer (Party buyer) (token exampleArgs) 10
    ]
  "
proposition
 "playTrace 0 escrowExample confirmClaimTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = confirmClaimPayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: confirmClaimPayments_def
              seller_def buyer_def mediator_def exampleArgs_def)
     done
end
(*>*)