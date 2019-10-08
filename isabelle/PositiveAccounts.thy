theory PositiveAccounts
imports Semantics
begin

fun allAccountsPositive :: "(AccountId \<times> Money) list \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r (_, money) . r \<and> money > 0) True accs"


fun allAccountsPositiveState :: "State \<Rightarrow> bool" where
"allAccountsPositiveState state = allAccountsPositive (accounts state)"


lemma positiveMoneyInAccount [simp] :
  "allAccountsPositive accs \<Longrightarrow> 0 \<le> moneyInAccount accId accs"
  oops

lemma addMoneyToAccountPositive :
  "0 \<le> money \<and> allAccountsPositive accs
  \<Longrightarrow> allAccountsPositive (addMoneyToAccount accId money accs)"
  oops

theorem accountsArePositive :
    "allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"
  oops

end