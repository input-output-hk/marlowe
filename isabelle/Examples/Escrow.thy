(*<*)
theory Escrow
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin
(*>*)

section \<open>Escrow contract\<close>

subsection \<open>Contract definition\<close>

record EscrowArgs =
  price             :: Value
  token             :: Token
  seller            :: Party
  buyer             :: Party
  mediator          :: Party
  paymentDeadline   :: Timeout
  complaintDeadline :: Timeout
  disputeDeadline   :: Timeout
  mediationDeadline :: Timeout

definition "adaToken = Token (BS '''') (BS '''')"

fun mediation :: "EscrowArgs \<Rightarrow> Contract" where
  "mediation args =
    When
      [ Case (Choice (ChoiceId (BS ''Dismiss claim'') (mediator args)) [Bound 0 0])
          (Pay (buyer args) (Account (seller args)) adaToken (price args) Close)
      , Case (Choice (ChoiceId (BS ''Confirm claim'') (mediator args)) [Bound 1 1]) Close
      ] (mediationDeadline args) Close"

fun dispute :: "EscrowArgs \<Rightarrow> Contract" where
  "dispute args =
    When
      [ Case (Choice (ChoiceId (BS ''Confirm problem'') (seller args)) [Bound 1 1]) Close
      , Case (Choice (ChoiceId (BS ''Dispute problem'') (seller args)) [Bound 0 0]) (mediation args)
      ] (disputeDeadline args) Close"

fun report :: "EscrowArgs \<Rightarrow> Contract" where
  "report args =
    When
      [ Case (Choice (ChoiceId (BS ''Everything is alright'') (buyer args)) [Bound 0 0]) Close
      , Case (Choice (ChoiceId (BS ''Report problem'') (buyer args)) [Bound 1 1])
          (Pay (seller args) (Account (buyer args)) adaToken (price args) (dispute args))
      ] (complaintDeadline args) Close"

fun escrow :: "EscrowArgs \<Rightarrow> Contract" where
  "escrow args =
    When
      [ Case (Deposit (seller args) (buyer args) adaToken (price args)) (report args) ]
      (paymentDeadline args) Close"

definition "escrowArgs =
  \<lparr> price = Constant 10
  , token = adaToken
  , seller = Role (BS ''Seller'')
  , buyer = Role (BS ''Buyer'')
  , mediator = Role (BS ''Mediator'')
  , paymentDeadline = 1664812800000
  , complaintDeadline = 1664816400000
  , disputeDeadline = 1664820420000
  , mediationDeadline = 1664824440000
  \<rparr>"

definition "escrowExample = escrow escrowArgs"

subsection \<open>Everything is alright.\<close>

definition
  "everythingIsAlrightTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit
                    (seller escrowArgs)
                    (buyer escrowArgs)
                    (token escrowArgs)
                    10
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Everything is alright'') (buyer escrowArgs)) 0
                 ]
      \<rparr>
    ]
  "

definition
  "everythingIsAlrightPayments =
    [ Payment (seller escrowArgs) (Party (seller escrowArgs)) (token escrowArgs) 10
    ]
  "

proposition
 "playTrace 0 escrowExample everythingIsAlrightTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = everythingIsAlrightPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: everythingIsAlrightPayments_def escrowArgs_def adaToken_def)
     done(*>*)

subsection \<open>Confirm problem.\<close>

definition
  "confirmProblemTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit
                    (seller escrowArgs)
                    (buyer escrowArgs)
                    (token escrowArgs)
                    10
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') (buyer escrowArgs)) 1
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Confirm problem'') (seller escrowArgs)) 1
                 ]
      \<rparr>
    ]
  "

definition
  "confirmProblemPayments =
    [ Payment (seller escrowArgs) (Account (buyer escrowArgs)) (token escrowArgs) 10
    , Payment (buyer escrowArgs) (Party (buyer escrowArgs)) (token escrowArgs) 10
    ]
  "

proposition
 "playTrace 0 escrowExample confirmProblemTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = confirmProblemPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: confirmProblemPayments_def escrowArgs_def adaToken_def)
     done(*>*)

subsection \<open>Dismiss claim.\<close>

definition
  "dismissClaimTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit
                    (seller escrowArgs)
                    (buyer escrowArgs)
                    (token escrowArgs)
                    10
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') (buyer escrowArgs)) 1
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dispute problem'') (seller escrowArgs)) 0
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664821400000, 1664822400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dismiss claim'') (mediator escrowArgs)) 0
                 ]
      \<rparr>
    ]
  "

definition
  "dismissClaimPayments =
    [ Payment (seller escrowArgs) (Account (buyer escrowArgs)) (token escrowArgs) 10
    , Payment (buyer escrowArgs) (Account (seller escrowArgs)) (token escrowArgs) 10
    , Payment (seller escrowArgs) (Party (seller escrowArgs)) (token escrowArgs) 10
    ]
  "

proposition
 "playTrace 0 escrowExample dismissClaimTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = dismissClaimPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: dismissClaimPayments_def escrowArgs_def adaToken_def)
     done(*>*)

subsection \<open>Confirm claim.\<close>

definition
  "confirmClaimTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit
                    (seller escrowArgs)
                    (buyer escrowArgs)
                    (token escrowArgs)
                    10
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IChoice (ChoiceId (BS ''Report problem'') (buyer escrowArgs)) 1
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664817400000, 1664817400000)
      , inputs = [ IChoice (ChoiceId (BS ''Dispute problem'') (seller escrowArgs)) 0
                 ]
      \<rparr>
   ,  \<lparr> interval = (1664821400000, 1664822400000)
      , inputs = [ IChoice (ChoiceId (BS ''Confirm claim'') (mediator escrowArgs)) 1
                 ]
      \<rparr>
    ]
  "

definition
  "confirmClaimPayments =
    [ Payment (seller escrowArgs) (Account (buyer escrowArgs)) (token escrowArgs) 10
    , Payment (buyer escrowArgs) (Party (buyer escrowArgs)) (token escrowArgs) 10
    ]
  "

proposition
 "playTrace 0 escrowExample confirmClaimTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = confirmClaimPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: confirmClaimPayments_def escrowArgs_def adaToken_def)
     done(*>*)

end
