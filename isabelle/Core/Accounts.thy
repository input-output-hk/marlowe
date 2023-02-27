theory Accounts
imports SemanticsTypes MultiAssets
begin


section "Accounts" 

typedef Accounts = "{ accs :: AccountId \<rightharpoonup> Assets. finite (dom accs)}"
  apply (rule_tac x = "\<lambda>_. None" in exI)
  by simp

setup_lifting type_definition_Accounts


lift_definition accountAssets :: "AccountId \<Rightarrow> Accounts \<Rightarrow> Assets" 
  is "\<lambda>accId acc. case acc accId of None \<Rightarrow> 0 | Some a \<Rightarrow> a" .
  

subsection "Assets in Accounts"


text \<open>We define assetsInAccounts as the sum of Assets for every accId \<close>
definition sum_accs_graph :: "(AccountId \<times> Assets) \<Rightarrow> Assets \<Rightarrow> Assets"
  where "sum_accs_graph t a = snd t + a"

text "The comp_fun_commute_on locale interpretation allows us to better reason
about assetsInAccounts when the Account is finite"
interpretation sum_accs_graph: comp_fun_commute_on  "UNIV" sum_accs_graph
  by unfold_locales (simp add: comp_def add_ac(3) sum_accs_graph_def)

lift_definition assetsInAccounts :: "Accounts \<Rightarrow> Assets" 
  is "\<lambda>accs.  Finite_Set.fold sum_accs_graph 0 (Map.graph accs)" .



end