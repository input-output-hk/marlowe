(*<*)
theory Swap
  imports Core.Semantics Core.TransactionBound Core.Timeout
begin
(*>*)

section \<open>Simple Swap\<close>

text \<open>
A simple swap contract consists on two parties exchanging some \<^term>\<open>amount\<close> of \<^term>\<open>Token\<close>s 
atomically. Each participant needs to deposit their tokens into the contract by a certain
\<^term>\<open>depositDeadline\<close>. If they do, the contract makes the swap and pays the participants, if 
one of the participant fails to make the deposit, the funds held by the contract can be redeemed 
by the owner.
\<close>

subsection \<open>Contract definition\<close>

text \<open>
To reduce the number of parameters we bundle the information required by each participant into a record.
\<close>

record SwapParty = 
  \<comment> \<open>A participant of the contract,\<close>
  party           :: Party
  \<comment> \<open>wants to swap an \<^term>\<open>amount\<close> of \<^term>\<open>Token\<close>\<close>
  amount          :: Value   
  currency        :: Token    
  \<comment> \<open>before a deadline\<close>
  depositDeadline :: Timeout


text \<open>The following helper function allows participants to deposit their tokens into the contract. \<close>

fun makeDeposit :: "SwapParty \<Rightarrow> Contract \<Rightarrow> Contract" where 
  "makeDeposit sp continue  = 
    \<comment> \<open>The contract waits for a deposit\<close>
    When
      [ 
        Case 
          (Deposit 
            \<comment> \<open>into the internal account of the party\<close>
            (party sp) 
            \<comment> \<open>from the party wallet\<close>
            (party sp) 
            \<comment> \<open>Amount of tokens\<close>
            (currency sp) 
            (amount sp)
          )
          \<comment> \<open>Once the deposit has been made, execute the continuation\<close> 
          continue 
     ]
     \<comment> \<open>If the tokens haven't been deposited by the deadline, close the contract.\<close>
     \<comment> \<open>This will return all current funds to their owners.\<close>
     (depositDeadline sp) Close  
   "

text \<open>The following helper function makes a \<^term>\<open>Payment\<close> from one party to the other\<close>
fun makePayment :: "SwapParty \<Rightarrow> SwapParty \<Rightarrow> Contract \<Rightarrow> Contract" where 
  "makePayment src dest = 
    \<comment> \<open>The contract makes a Payment\<close>
    Pay 
      \<comment> \<open>from the party internal account\<close>
      (party src) 
      \<comment> \<open>to the destination wallet\<close>
      (Party (party dest)) 
      \<comment> \<open>of the number of tokens from the source\<close>
      (currency src) (amount src)
  " 

text \<open>The actual swap contract waits for both parties to make their deposits, then makes the payout
and closes.\<close>
fun swap :: "SwapParty \<Rightarrow> SwapParty \<Rightarrow> Contract" where 
  "swap p1 p2 = makeDeposit p1 
                ( makeDeposit p2 
                ( makePayment p1 p2 
                ( makePayment p2 p1 Close
                )))
  "

subsection \<open>Example execution\label{sec:swap-example-execution}\<close>

text \<open>Let's define two participants that want to trade USD and ADA in the cardano blockchain.\<close>

definition "adaProvider = Role (BS ''Ada Provider'')"
definition "dollarProvider = Role (BS ''Dollar Provider'')"

text "In cardano, the ADA symbol is represented by the empty string"

definition "adaToken = Token (BS '''') (BS '''')"
definition "dollarToken = Token (BS ''85bb65'') (BS ''dollar'')"

text \<open>The contract can be created as follow.\<close>

definition
  "swapExample = 
    swap 
      \<comment> \<open>Party A trades 10 lovelaces\<close>
      \<comment> \<open>deposited before Monday, October 3, 2022 4:00:00 PM GMT\<close>
      \<lparr> party = adaProvider
      , amount = Constant 10
      , currency = adaToken
      , depositDeadline = 1664812800000
      \<rparr>
      \<comment> \<open>Party B trades 20 cents\<close>
      \<comment> \<open>deposited before Monday, October 3, 2022 5:00:00 PM GMT\<close>
      \<lparr> party = dollarProvider
      , amount = Constant 20
      , currency = dollarToken
      , depositDeadline = 1664816400000 
      \<rparr>
  "

subsubsection \<open>Successful execution\<close>

text \<open>If both parties deposit before their deadline,\<close>

definition
  "successfulExecutionPathTransactions = 
    [ 
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit 
                    adaProvider 
                    adaProvider 
                    adaToken 
                    10
                 ] 
      \<rparr>
     \<comment> \<open>Second party deposit\<close>
    , \<lparr> interval = (1664812900000, 1664813100000)
      , inputs = [
                  IDeposit 
                    dollarProvider
                    dollarProvider  
                    dollarToken
                    20
                 ]  
      \<rparr>
    ]
  "

text  \<open>payments are made to swap the tokens\<close>
definition 
  "successfulExecutionPathPayments = 
    [ Payment adaProvider (Party dollarProvider) adaToken 10
    , Payment dollarProvider (Party adaProvider) dollarToken 20
    ]
  "

text \<open>and the contract is closed without emitting a warning\<close>

proposition
 "playTrace 0 swapExample successfulExecutionPathTransactions = TransactionOutput txOut
  \<Longrightarrow> 
     txOutContract txOut = Close
     \<and> txOutPayments txOut = successfulExecutionPathPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: successfulExecutionPathPayments_def  adaProvider_def adaToken_def dollarProvider_def  dollarToken_def)
     done(*>*)

subsubsection \<open>Swap does not take place\<close>

text \<open>If only the first party deposits before the deadline,\<close>

definition
  "partialExecutionPathTransactions =
    [
      \<comment> \<open>First party deposit\<close>
      \<lparr> interval = (1664812600000, 1664812700000)
      , inputs = [
                  IDeposit
                    adaProvider
                    adaProvider
                    adaToken
                    10
                 ]
      \<rparr>
    , \<lparr> interval = (1664816400000, 1664816600000 )
      , inputs = []
      \<rparr>
    ]
  "

text  \<open>we expect the repayment of the of the deposit\<close>
definition
  "partialExecutionPathPayments = [ Payment adaProvider (Party adaProvider) adaToken 10
  ] "

proposition
 "playTrace 0 swapExample partialExecutionPathTransactions = TransactionOutput txOut
  \<Longrightarrow>
     txOutContract txOut = Close
     \<and> txOutPayments txOut = partialExecutionPathPayments
     \<and> txOutWarnings txOut = []"
(*<*)apply (code_simp)
     apply (auto simp add: partialExecutionPathPayments_def adaProvider_def adaToken_def dollarProvider_def  dollarToken_def)
     done(*>*)

subsection \<open>Contract guarantees\<close>

subsubsection \<open>Number of transactions\<close>
text \<open>Counting the amount of \<open>When\<close>s, it is easy to notice that there can be at most two transactions\<close>

proposition (*<*)maxSwapTransactions:(*>*)
  "maxTransactionsInitialState (swap a b) = 2" 
(*<*)by simp(*>*)

text \<open>Expressed in a different way, if we use the lemma defined in \secref{sec:transaction-bound} we can
state that, if the execution of the contract yields a successful \<^term>\<open>TransactionOutput\<close>, then the number
of transactions must be lower or equal than @{value "maxTransactionsInitialState (swap a b)"}\<close>

lemma
  "playTrace 
      initialTime 
      (swap a b) 
      transactions = TransactionOutput txOut
   \<Longrightarrow> length transactions \<le> 2"
(*<*)by (metis maxSwapTransactions playTrace_only_accepts_maxTransactionsInitialState)(*>*)

subsubsection \<open>Maximum time\<close>

text \<open>If the deadline of the second party is bigger than the first, then that deadline is the 
maximum time of the contract.\<close>
proposition 
  "sp1 = 
         \<lparr> party = p1
         , amount = a1
         , currency = t1
         , depositDeadline = d1
         \<rparr>   
   \<Longrightarrow> sp2 = 
         \<lparr> party = p2
         , amount = a2
         , currency = t2
         , depositDeadline = d2
         \<rparr>
   \<Longrightarrow> d2 > d1
   \<Longrightarrow> d1 > 0
   \<Longrightarrow> contract = swap sp1 sp2 
   \<Longrightarrow> maxTimeContract (contract) = d2
  "
  (*<*)by simp(*>*)

(*<*)
\<comment> \<open>Section omitted for the moment\<close>
text \<open>Expressed in another way, by using the lemma defined in \secref{sec:max-time-guarantee} we can
guarantee that if we apply an empty transaction after the contract deadline, the contract will close.\<close>

lemma 
 "sp1 =  \<lparr> party = p1, amount = a1, currency = t1, depositDeadline = d1 \<rparr>   
   \<Longrightarrow> sp2 = \<lparr> party = p2, amount = a2, currency = t2, depositDeadline = d2 \<rparr>   
   \<Longrightarrow> d2 > d1
   \<Longrightarrow> d1 > 0
   \<Longrightarrow> contract = swap sp1 sp2 
   \<Longrightarrow> validAndPositive_state sta
   \<Longrightarrow> iniTime \<ge> minTime sta
   \<Longrightarrow> iniTime \<ge> d2
   \<Longrightarrow> endTime \<ge> iniTime
   \<Longrightarrow> accounts sta \<noteq> [] \<or> contract \<noteq> Close
   \<Longrightarrow> isClosedAndEmpty (computeTransaction \<lparr> interval = (iniTime, endTime)
                                            , inputs = [] \<rparr> sta contract)
  "
  using  swapExample_def successfulExecutionPathTransactions_def dollarProvider_def dollarToken_def adaProvider_def adaToken_def
  apply (simp_all)
  oops

\<comment> \<open>Another lemma to add would be: If d2 < d1, and the first deposit is made before d1 but after d2, then the second deposit can never be made.\<close>
\<comment> \<open>Another lemma to make would be around negative amounts, to show that they give warnings. Maybe show that if amounts are positive and d2 > d1 there can never be a warning?\<close>

(*>*)
  

(*<*)
end
(*>*)
