(*<*)
theory Escrow
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin
(*>*)

section \<open>Escrow contract\<close>

subsection \<open>Contract definition\<close>

record EscrowArgs =
  price             :: Value
  seller            :: Party
  buyer             :: Party
  mediator          :: Party
  paymentDeadline   :: Timeout
  complaintDeadline :: Timeout
  disputeDeadline   :: Timeout
  mediationDeadline :: Timeout

definition "ada = Token (BS '''') (BS '''')"

fun mediation :: "EscrowArgs \<Rightarrow> Contract" where
  "mediation args =
    When
      [ Case (Choice (ChoiceId (BS ''Dismiss claim'') (mediator args)) [Bound 0 0])
          (Pay (buyer args) (Account (seller args)) ada (price args) Close)
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
          (Pay (seller args) (Account (buyer args)) ada (price args) (dispute args))
      ] (complaintDeadline args) Close"

fun escrow :: "EscrowArgs \<Rightarrow> Contract" where
  "escrow args =
    When
      [ Case (Deposit (seller args) (buyer args) ada (price args)) (report args) ]
      (paymentDeadline args) Close"

definition "escrow_example = escrow
  \<lparr> price = Constant 1
  , seller = Role (BS ''Seller'')
  , buyer = Role (BS ''Buyer'')
  , mediator = Role (BS ''Mediator'')
  , paymentDeadline = 1664812800000
  , complaintDeadline = 1664812800000
  , disputeDeadline = 1664812800000
  , mediationDeadline = 1664812800000
  \<rparr>"

value escrow_example
