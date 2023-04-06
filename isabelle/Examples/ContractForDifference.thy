(*<*)
theory ContractForDifference
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin
(*>*)
section \<open>ContractForDifference contract\<close>

subsection \<open>Contract definition\<close>

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

definition "priceBeginning = ChoiceId (BS ''Price in first window'')"
definition "priceEnd = ChoiceId (BS ''Price in second window'')"

record CfdArgs =
  partyParty                  :: Party
  counterpartyParty           :: Party
  oracleParty                 :: Party
  partyDeposit                :: Value
  partyDepositDeadline        :: Timeout
  counterpartyDeposit         :: Value
  counterpartyDepositDeadline :: Timeout
  firstWindowBeginning        :: Timeout
  firstWindowDeadline         :: Timeout
  secondWindowBeginning       :: Timeout
  secondWindowDeadline        :: Timeout

definition contractForDifference :: "CfdArgs \<Rightarrow> Contract" where
  "contractForDifference args = (
      let decreaseInPrice = ValueId (BS ''Decrease in price'');
          increaseInPrice = ValueId (BS ''Increase in price'');
          party = partyParty args;
          counterparty = counterpartyParty args;
          oracle = oracleParty args
      in initialDeposit party (partyDeposit args) (partyDepositDeadline args) Close
        (initialDeposit counterparty (counterpartyDeposit args) (counterpartyDepositDeadline args) Close
        (wait (firstWindowBeginning args)
        (oracleInput (priceBeginning oracle) (firstWindowDeadline args) Close
        (wait (secondWindowBeginning args)
        (oracleInput (priceEnd oracle) (secondWindowDeadline args) Close
        (gtLtEq (ChoiceValue (priceBeginning oracle)) (ChoiceValue (priceEnd oracle))
                (recordDifference decreaseInPrice (priceBeginning oracle) (priceEnd oracle)
                  (transferUpToDeposit counterparty (counterpartyDeposit args) party (UseValue decreaseInPrice)
                  (Close)))
                (recordDifference increaseInPrice (priceEnd oracle) (priceBeginning oracle)
                  (transferUpToDeposit party (partyDeposit args) counterparty (UseValue increaseInPrice)
                  (Close)))
                Close)))))))
  "

subsection \<open>Example CFD\<close>

text \<open>The participants in the example contract are:\<close>

definition "party = Role (BS ''Party'')"
definition "counterparty = Role (BS ''CounterParty'')"
definition "oracle = Role (BS ''Oracle'')"

definition "cfdExampleArgs =
  \<lparr> partyParty = party
  , counterpartyParty = counterparty
  , oracleParty = oracle
  , partyDeposit = Constant 10
  , partyDepositDeadline = 1664812800000
  , counterpartyDeposit = Constant 10
  , counterpartyDepositDeadline = 1664816400000
  , firstWindowBeginning = 1664820420000
  , firstWindowDeadline = 1664820520000
  , secondWindowBeginning = 1664821420000
  , secondWindowDeadline = 1664821520000
  \<rparr>"

definition "cfdExample = contractForDifference cfdExampleArgs"

definition
  "cfdExampleTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [ IDeposit party party ada 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [ IDeposit counterparty counterparty ada 10 ]
      \<rparr>
   ,  \<lparr> interval = (1664820420001, 1664820500000)
      , inputs = [ IChoice (priceBeginning oracle) 2 ]
      \<rparr>
   ,  \<lparr> interval = (1664821420001, 1664821510000)
      , inputs = [ IChoice (priceEnd oracle) 4 ]
      \<rparr>
    ]
  "

definition
  "cfdExamplePayments =
    [ Payment party (Account counterparty) ada 2 
    , Payment counterparty (Party counterparty) ada 12 
    , Payment party (Party party) ada 8 
    ]
  "
 
proposition
 "playTrace 0 cfdExample cfdExampleTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = cfdExamplePayments
     \<and> txOutWarnings txOut = []"
     apply (code_simp)
     apply (auto simp add: ada_def contractForDifference_def
              cfdExampleArgs_def cfdExampleTransactions_def cfdExamplePayments_def
              party_def counterparty_def oracle_def)
     done

(*<*)
end
(*>*)