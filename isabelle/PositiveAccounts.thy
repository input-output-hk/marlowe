theory PositiveAccounts
imports Semantics ValidState
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

lemma updateMoneyInAccount_geZero :
 "0 < newBalance \<Longrightarrow>
  \<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
  0 \<le> moneyInAccount y (updateMoneyInAccount accId newBalance accs)"
  by (metis addMoneyToAccountPositive_noMatch addMoneyToAccountPositve_match not_less updateMoneyInAccount.simps)

lemma addMoneyToAccountPositive :
  "0 \<le> money \<Longrightarrow> (\<forall>x. moneyInAccount x accs \<ge> 0)
  \<Longrightarrow> moneyInAccount y (addMoneyToAccount accId money accs) \<ge> 0"
  apply (simp only:"addMoneyToAccount.simps")
  apply (cases "money \<le> 0")
  apply simp
  apply (simp del:moneyInAccount.simps)
  apply (cases "accId = y")
  apply (smt updateMoneyInAccount.simps updateMoneyInAccount_geZero)
  by (smt updateMoneyInAccount.simps updateMoneyInAccount_geZero)

lemma giveMoney_geZero :
    "\<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
       (eff, newAccs) = giveMoney payee money accs \<Longrightarrow>
       0 \<le> moneyInAccount y newAccs"
  by (metis addMoneyToAccount.simps addMoneyToAccountPositive giveMoney.elims linear snd_conv)

lemma moneyInAccount_valid_zero : "valid_map ((accId, money) # rest) \<Longrightarrow> moneyInAccount accId rest = 0"
  apply (simp only:moneyInAccount.simps findWithDefault.simps)
  by (simp add: MList.delete_lookup_None_aux)

lemma moneyInAccount_sublist_geZero_different :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   0 < money \<Longrightarrow> 0 \<le> moneyInAccount y ((accId, money) # rest) \<Longrightarrow>
   accId \<noteq> y \<Longrightarrow> 0 \<le> moneyInAccount y rest"
  apply (simp only:moneyInAccount.simps findWithDefault.simps)
  by (metis MList.delete.simps(2) MList.different_delete_lookup)

lemma moneyInAccount_sublist_geZero :
    "valid_map ((accId, money) # rest) \<Longrightarrow>
     money > 0 \<Longrightarrow>
    (\<forall>x. 0 \<le> moneyInAccount x ((accId, money) # rest)) \<Longrightarrow> 0 \<le> moneyInAccount y rest"
  apply (cases "accId = y")
  using moneyInAccount_valid_zero apply auto[1]
  using moneyInAccount_sublist_geZero_different by blast

lemma moneyInAccount_geZero_preservation :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   (\<forall>x. 0 \<le> moneyInAccount x ((accId, money) # rest)) \<Longrightarrow> 0 \<le> moneyInAccount y rest"
  apply (simp only:moneyInAccount.simps findWithDefault.simps)
  by (metis MList.delete.simps(2) MList.delete_lookup_None_aux MList.delete_valid_aux MList.insert_in_middle lookup.simps(2) not_less_iff_gr_or_eq option.simps(4) order_refl)

lemma reduceOne_geZero_aux :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   (money \<le> 0 \<Longrightarrow> \<forall>x. 0 \<le> moneyInAccount x rest \<Longrightarrow> refundOne rest = Some (paym, newAccs) \<Longrightarrow> 0 \<le> moneyInAccount y newAccs) \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x ((accId, money) # rest) \<Longrightarrow> refundOne ((accId, money) # rest) = Some (paym, newAccs) \<Longrightarrow> 0 \<le> moneyInAccount y newAccs"
  apply (cases "money > 0")
  apply (simp only:refundOne.simps)
  using moneyInAccount_sublist_geZero apply auto[1]
  apply (simp only:refundOne.simps if_False)
  using moneyInAccount_geZero_preservation not_less by blast

lemma reduceOne_geZero :
  "valid_map accs \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
   refundOne accs = Some (paym, newAccs) \<Longrightarrow>
   0 \<le> moneyInAccount y newAccs"
  apply (induction accs rule:"refundOne.induct")
  apply (meson MList.sublist_valid not_le reduceOne_geZero_aux)
  by auto

lemma reduceContractStep_geZero_Refund_aux :
  "valid_state state \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x (accounts state) \<Longrightarrow>
   refundOne (accounts state) = Some ((party, money), newAccount) \<Longrightarrow>
   wa = ReduceNoWarning \<Longrightarrow>
   eff = ReduceWithPayment (Payment party money) \<Longrightarrow>
   0 \<le> moneyInAccount y newAccount"
  using reduceOne_geZero valid_state.elims(2) by blast

lemma reduceContractStep_geZero_Refund :
  "valid_state state \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x (accounts state) \<Longrightarrow>
   refundOne (accounts state) = Some ((party, money), newAccount) \<Longrightarrow>
   Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) (state\<lparr>accounts := newAccount\<rparr>) Close =
      Reduced wa eff newState newCont \<Longrightarrow>
   0 \<le> moneyInAccount y (accounts newState)"
  using reduceContractStep_geZero_Refund_aux by auto

lemma MList_delete_preserves_geZero : "valid_map accs \<Longrightarrow> \<forall>x. 0 \<le> moneyInAccount x accs \<Longrightarrow>
                                       0 \<le> moneyInAccount y (MList.delete accId accs)"
  by (metis MList.delete_lookup_None MList.delete_lookup_None_aux MList.delete_valid MList.different_delete_lookup eq_iff findWithDefault.simps moneyInAccount.simps moneyInAccount_valid_zero refundOne.elims)

lemma reduceContractStep_geZero_Pay_aux :
  "valid_state state \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x (accounts state) \<Longrightarrow>
   0 \<le> moneyInAccount x (updateMoneyInAccount accId amount (accounts state))"
  using MList_delete_preserves_geZero updateMoneyInAccount_geZero by auto

lemma reduceContractStep_geZero_Pay :
  "valid_state state \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x (accounts state) \<Longrightarrow>
   reduceContractStep env state (Pay accId payee val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   0 \<le> moneyInAccount y (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "evalValue env state val \<le> 0")
  apply simp
  apply (cases "giveMoney payee (min (moneyInAccount accId (accounts state)) (evalValue env state val))
                (updateMoneyInAccount accId (moneyInAccount accId (accounts state) - min (moneyInAccount accId (accounts state)) (evalValue env state val))
                  (accounts state))")
  apply (simp del:moneyInAccount.simps valid_state.simps updateMoneyInAccount.simps)
  by (smt MList_delete_preserves_geZero ReduceStepResult.inject State.select_convs(1) State.surjective State.update_convs(1) giveMoney_geZero updateMoneyInAccount.simps updateMoneyInAccount_geZero valid_state.elims(2))

lemma reduceContractStep_geZero_Let :
  "valid_state state \<Longrightarrow>
   \<forall>x. 0 \<le> moneyInAccount x (accounts state) \<Longrightarrow>
   reduceContractStep env state (Contract.Let valueId val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   0 \<le> moneyInAccount y (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "state")
  apply (cases "newState")
  apply (simp del:moneyInAccount.simps valid_state.simps)
  by (metis ReduceStepResult.inject State.ext_inject)

theorem reduceContractStep_geZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. moneyInAccount x (accounts state) \<ge> 0) \<Longrightarrow>
   reduceContractStep env state cont = Reduced wa eff newState newCont \<Longrightarrow>
   moneyInAccount y (accounts newState) \<ge> 0"
  apply (cases cont)
  apply (cases "refundOne (accounts state)")
  apply simp
  using reduceContractStep_geZero_Refund apply force
  using reduceContractStep_geZero_Pay apply blast
  apply simp
  apply (smt ReduceStepResult.distinct(1) ReduceStepResult.inject ReduceStepResult.simps(5) case_prod_unfold reduceContractStep.simps(4))
  using reduceContractStep_geZero_Let by blast

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

theorem accountsArePositive :
"(\<forall>x. moneyInAccount x (accounts state) \<ge> 0) \<Longrightarrow>
  computeTransaction txIn state cont = TransactionOutput txOut \<Longrightarrow>
  moneyInAccount y (accounts (txOutState txOut)) \<ge> 0"
oops

theorem accountsArePositive2 :
    "allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"
  oops

end