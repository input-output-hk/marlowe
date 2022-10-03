(*<*)
theory Swap
  imports Core.Semantics Core.TransactionBound
begin
(*>*)

section \<open>Contract definition\<close>

record SwapParty = party           :: Party
                   currency        :: Token
                   amount          :: Value
                   depositDeadline :: Timeout

fun makeDeposit :: "SwapParty \<Rightarrow> Contract \<Rightarrow> Contract" where 
  "makeDeposit sp continuation  = 
    When
      [ Case (Deposit (party sp) (party sp) (currency sp) (amount sp)) continuation ]
      (depositDeadline sp)
      Close  
   "

fun makePayment :: "SwapParty \<Rightarrow> SwapParty \<Rightarrow> Contract \<Rightarrow> Contract" where 
  \<open>makePayment src dest = Pay (party src) (Party (party dest)) (currency src) (amount src)
  \<close> 

fun swap :: \<open>SwapParty \<Rightarrow> SwapParty \<Rightarrow> Contract\<close> where 
  \<open>swap p1 p2 = makeDeposit p1 
                ( makeDeposit p2 
                ( makePayment p1 p2 
                ( makePayment p2 p1 Close
                )))
  \<close>

section \<open>Swap Example\<close>

definition tokenAProvider :: "SwapParty" where
  \<open>tokenAProvider = 
     \<lparr> party = Role (BS ''Token A Provider'')
     , currency = Token (BS ''symbol-a'') (BS ''a'')
     , amount = Constant 10
     , depositDeadline = 10
     \<rparr> \<close> 

definition tokenBProvider  :: "SwapParty" where
  \<open>tokenBProvider = 
     \<lparr> party = Role (BS ''Token B Provider'')
     , currency = Token (BS ''symbol-b'') (BS ''b'')
     , amount = Constant 20
     , depositDeadline = 20
     \<rparr> \<close> 

definition "swapExample = swap tokenAProvider tokenBProvider"

section \<open>Contract guarantees\<close>

proposition maxSwapTransactions: "maxTransactionsInitialState (swap a b) = 2" 
  by simp


lemma 
  "playTrace initialTime (swap a b) transactions = TransactionOutput txOut \<Longrightarrow>
   length transactions \<le> 2"
  by (metis maxSwapTransactions playTrace_only_accepts_maxTransactionsInitialState)


(*<*)
end
(*>*)