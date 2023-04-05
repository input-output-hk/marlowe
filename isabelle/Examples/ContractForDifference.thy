(*<*)
theory ContractForDifference
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin

(*>*)
section \<open>ContractForDifference contract\<close>

text \<open>A ContractForDifference (cfd)\<close>

subsection \<open>Contract definition\<close>

text \<open>The participants of the contract are:\<close>

definition "party = Role (BS ''Party'')"
definition "counterparty = Role (BS ''CounterParty'')"
definition "oracle = Role (BS ''Oracle'')"
definition "ada = Token (BS '''') (BS '''')"

fun initialDeposit :: "Party \<Rightarrow> Value \<Rightarrow> Timeout \<Rightarrow> Contract \<Rightarrow> Contract \<Rightarrow> Contract" where
  "initialDeposit by deposit timeout timeoutContinuation continuation =
    When [Case (Deposit by by ada deposit) continuation]
       timeout
       timeoutContinuation"

fun wait :: "Timeout \<Rightarrow> Contract \<Rightarrow> Contract" where
  "wait timeout cont = When [] timeout cont"

fun oracleInput :: "ChoiceId \<Rightarrow> Timeout \<Rightarrow> Contract \<Rightarrow> Contract \<Rightarrow> Contract" where
  "oracleInput choiceId timeout timeoutContinuation continuation =
    When [Case (Choice choiceId [Bound 0 1000000000]) continuation]
         timeout
         timeoutContinuation"

fun gtLtEq :: "Value \<Rightarrow> Value \<Rightarrow> Contract \<Rightarrow> Contract \<Rightarrow> Contract \<Rightarrow> Contract" where
  "gtLtEq value1 value2 gtContinuation ltContinuation eqContinuation =
       If (ValueGT value1 value2) gtContinuation 
     ((If (ValueLT value1 value2) ltContinuation) 
                                  eqContinuation)"

fun recordDifference :: "ValueId \<Rightarrow> ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> Contract \<Rightarrow> Contract" where
  "recordDifference name choiceId1 choiceId2 =
     Let name (SubValue (ChoiceValue choiceId1) (ChoiceValue choiceId2))"

fun transferUpToDeposit :: "Party \<Rightarrow> Value \<Rightarrow> Party \<Rightarrow> Value \<Rightarrow> Contract \<Rightarrow> Contract" where
  "transferUpToDeposit from payerDeposit to amount =
    Pay from (Account to) ada (Cond (ValueLT amount payerDeposit) amount payerDeposit)"

definition "partyDeposit = Constant 10"
definition "partyDepositDeadline = 1664812800000"

definition "counterpartyDeposit = Constant 10"
definition "counterpartyDepositDeadline = 1664816400000"

definition "firstWindowBeginning = 1664820420000"
definition "firstWindowDeadline = 1664820520000"

definition "secondWindowBeginning = 1664821420000"
definition "secondWindowDeadline = 1664821520000"

definition "priceBeginning = ChoiceId (BS ''Price in first window'') oracle"
definition "priceEnd = ChoiceId (BS ''Price in second window'') oracle"

definition "decreaseInPrice = ValueId (BS ''Decrease in price'')"
definition "increaseInPrice = ValueId (BS ''Increase in price'')"

definition cfd :: "Contract" where
  "cfd = initialDeposit party partyDeposit partyDepositDeadline Close
        (initialDeposit counterparty counterpartyDeposit counterpartyDepositDeadline Close
        (wait firstWindowBeginning
        (oracleInput priceBeginning firstWindowDeadline Close
        (wait secondWindowBeginning
        (oracleInput priceEnd secondWindowDeadline Close
        (gtLtEq (ChoiceValue priceBeginning) (ChoiceValue priceEnd)
                (recordDifference decreaseInPrice priceBeginning priceEnd
                  (transferUpToDeposit counterparty counterpartyDeposit party (UseValue decreaseInPrice)
                  (Close)))
                (recordDifference increaseInPrice priceEnd priceBeginning
                  (transferUpToDeposit party partyDeposit counterparty (UseValue increaseInPrice)
                  (Close)))
                Close))))))
  "
subsection \<open>Possible Outcomes\<close>

definition
  "everythingIsAlrightTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit party party ada 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IDeposit counterparty counterparty ada 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664820420001, 1664820500000)
      , inputs = [ IChoice priceBeginning 2 ]
      \<rparr>
   ,  \<lparr> interval = (1664821420001, 1664821510000)
      , inputs = [ IChoice priceEnd 4 ]
      \<rparr>
    ]
  "

definition
  "everythingIsAlrightPayments =
    [ Payment party (Account counterparty) ada 2 
    , Payment counterparty (Party counterparty) ada 12 
    , Payment party (Party party) ada 8 
    ]
  "
 
(*value "playTrace 0 cfd everythingIsAlrightTransactions"*)

proposition
 "playTrace 0 cfd everythingIsAlrightTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = everythingIsAlrightPayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: everythingIsAlrightPayments_def
              ada_def cfd_def
              everythingIsAlrightTransactions_def
              party_def counterparty_def oracle_def 
              partyDeposit_def partyDepositDeadline_def 
              counterpartyDeposit_def 
              counterpartyDepositDeadline_def 
              firstWindowBeginning_def 
              firstWindowDeadline_def 
              secondWindowBeginning_def 
              secondWindowDeadline_def 
              priceBeginning_def 
              priceEnd_def 
              decreaseInPrice_def 
              increaseInPrice_def) 
     done
end
