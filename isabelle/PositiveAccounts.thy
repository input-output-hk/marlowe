theory PositiveAccounts
imports Semantics
begin

lemma addMoneyToAccountPositve_match :
 "\<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    0 \<le> moneyInAccount y (MList.insert y newBalance accs)"
  apply simp
  by (simp add: MList.insert_lookup_Some)

lemma addMoneyToAccountPositive_noMatch :
 "\<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    accId \<noteq> y \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    0 \<le> moneyInAccount y (MList.insert accId newBalance accs)"
  apply simp
  by (simp add: insert_lookup_different)

lemma addMoneyToAccountPositive :
  "0 \<le> money \<Longrightarrow> (\<forall>x. moneyInAccount x accs \<ge> 0)
  \<Longrightarrow> moneyInAccount y (addMoneyToAccount accId money accs) \<ge> 0"
  apply (simp only:"addMoneyToAccount.simps")
  apply (cases "money \<le> 0")
  apply simp
  apply (simp del:moneyInAccount.simps)
  apply (cases "accId = y")
  apply (metis (full_types) addMoneyToAccountPositve_match add_le_same_cancel1 dual_order.trans not_less)
proof -
  assume a1: "accId \<noteq> y"
assume a2: "\<not> money \<le> 0"
  assume a3: "\<forall>x. 0 \<le> moneyInAccount x accs"
  then have f4: "\<not> moneyInAccount accId accs + money \<le> 0"
using a2 by (meson add_le_same_cancel1 le_less_trans not_less)
  have "\<And>i. \<not> 0 < i \<or> 0 \<le> moneyInAccount y (MList.insert accId i accs)"
    using a3 a1 addMoneyToAccountPositive_noMatch by blast
then show "0 \<le> moneyInAccount y (let i = moneyInAccount accId accs + money in if i \<le> 0 then MList.delete accId accs else MList.insert accId i accs)"
  using f4 by auto
qed


(* Alternative formulation *)

fun allAccountsPositive :: "(AccountId \<times> Money) list \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r (_, money) . r \<and> money > 0) True accs"

fun allAccountsPositiveState :: "State \<Rightarrow> bool" where
"allAccountsPositiveState state = allAccountsPositive (accounts state)"

lemma positiveMoneyInAccount :
  "allAccountsPositive accs \<Longrightarrow> 0 < moneyInAccount accId accs"
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