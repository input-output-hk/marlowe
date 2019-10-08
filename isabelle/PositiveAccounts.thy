theory PositiveAccounts
imports Semantics
begin

theorem accountsArePositive :
  "(\<forall>x. moneyInAccount x (accounts state) \<ge> 0) \<Longrightarrow>
   computeTransaction txIn state cont = TransactionOutput txOut \<Longrightarrow>
   moneyInAccount y (accounts (txOutState txOut)) \<ge> 0"
  oops

(* Alternative formulation *)

fun allAccountsPositive :: "(AccountId \<times> Money) list \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r (_, money) . r \<and> money \<ge> 0) True accs"


fun allAccountsPositiveState :: "State \<Rightarrow> bool" where
"allAccountsPositiveState state = allAccountsPositive (accounts state)"

lemma positiveMoneyInAccount :
  "allAccountsPositive accs \<Longrightarrow> 0 \<le> moneyInAccount accId accs"
  oops

lemma addMoneyToAccountPositive :
  "0 \<le> money \<and> allAccountsPositive accs
  \<Longrightarrow> allAccountsPositive (addMoneyToAccount accId money accs)"
  oops

theorem accountsArePositive2 :
    "allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"
  oops

end