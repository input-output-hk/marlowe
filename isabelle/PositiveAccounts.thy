theory PositiveAccounts
imports Semantics ValidState
begin

fun positiveMoneyInAccountOrNoAccount :: "AccountId \<Rightarrow> ((AccountId \<times> Money) list) \<Rightarrow> bool" where
"positiveMoneyInAccountOrNoAccount accId mlist =
  (case MList.lookup accId mlist of
     None \<Rightarrow> True
   | Some x \<Rightarrow> x > 0)"

lemma addMoneyToAccountPositve_match :
 "\<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y (MList.insert y newBalance accs)"
  apply simp
  by (simp add: MList.insert_lookup_Some)

lemma addMoneyToAccountPositive_noMatch :
 "\<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    accId \<noteq> y \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y (MList.insert accId newBalance accs)"
  apply simp
  by (simp add: insert_lookup_different)

lemma updateMoneyInAccount_gtZero :
 "0 < newBalance \<Longrightarrow>
  \<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
  positiveMoneyInAccountOrNoAccount y (updateMoneyInAccount accId newBalance accs)"
  by (metis addMoneyToAccountPositive_noMatch addMoneyToAccountPositve_match not_less updateMoneyInAccount.simps)

lemma addMoneyToAccountPositive :
  "0 \<le> money \<Longrightarrow> (\<forall>x. positiveMoneyInAccountOrNoAccount x accs)
  \<Longrightarrow> positiveMoneyInAccountOrNoAccount y (addMoneyToAccount accId money accs)"
  apply (simp only:"addMoneyToAccount.simps")
  apply (cases "money \<le> 0")
  apply simp
  apply (cases "lookup accId accs")
  apply simp
  apply (metis (full_types) MList.insert_lookup_Some insert_lookup_different not_less option.simps(5))
  apply simp
  by (smt MList.insert_lookup_Some insert_lookup_different option.simps(5))

lemma giveMoney_gtZero :
    "\<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
       (eff, newAccs) = giveMoney payee money accs \<Longrightarrow>
       positiveMoneyInAccountOrNoAccount y newAccs"
  by (metis addMoneyToAccount.simps addMoneyToAccountPositive giveMoney.elims linear snd_conv)

lemma positiveMoneyInAccountOrNoAccount_valid_zero : "valid_map ((accId, money) # rest) \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (simp add: MList.delete_lookup_None_aux)

lemma positiveMoneyInAccountOrNoAccount_sublist_gtZero_different :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   0 < money \<Longrightarrow> positiveMoneyInAccountOrNoAccount y ((accId, money) # rest) \<Longrightarrow>
   accId \<noteq> y \<Longrightarrow> positiveMoneyInAccountOrNoAccount y rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (metis MList.delete.simps(2) MList.different_delete_lookup)

lemma positiveMoneyInAccountOrNoAccount_sublist_gtZero :
    "valid_map ((accId, money) # rest) \<Longrightarrow>
     money > 0 \<Longrightarrow>
    (\<forall>x. positiveMoneyInAccountOrNoAccount x ((accId, money) # rest)) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y rest"
  apply (cases "accId = y")
  using positiveMoneyInAccountOrNoAccount_valid_zero apply auto[1]
  using positiveMoneyInAccountOrNoAccount_sublist_gtZero_different by blast

lemma positiveMoneyInAccountOrNoAccount_gtZero_preservation :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x ((accId, money) # rest)) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (metis lookup.simps(2) option.simps(5) positiveMoneyInAccountOrNoAccount.simps positiveMoneyInAccountOrNoAccount_sublist_gtZero)

lemma reduceOne_gtZero_aux :
  "valid_map ((accId, money) # rest) \<Longrightarrow>
   (money \<le> 0 \<Longrightarrow> \<forall>x. positiveMoneyInAccountOrNoAccount x rest \<Longrightarrow> refundOne rest = Some (paym, newAccs) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y newAccs) \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x ((accId, money) # rest) \<Longrightarrow> refundOne ((accId, money) # rest) = Some (paym, newAccs) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y newAccs"
  apply (cases "money > 0")
  apply (simp only:refundOne.simps)
  using positiveMoneyInAccountOrNoAccount_sublist_gtZero apply auto[1]
  apply (simp only:refundOne.simps if_False)
  using positiveMoneyInAccountOrNoAccount_gtZero_preservation not_less by blast

lemma reduceOne_gtZero :
  "valid_map accs \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
   refundOne accs = Some (paym, newAccs) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y newAccs"
  apply (induction accs rule:"refundOne.induct")
  apply (meson MList.sublist_valid not_le reduceOne_gtZero_aux)
  by auto

lemma reduceContractStep_gtZero_Refund_aux :
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   refundOne (accounts state) = Some ((party, money), newAccount) \<Longrightarrow>
   wa = ReduceNoWarning \<Longrightarrow>
   eff = ReduceWithPayment (Payment party money) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y newAccount"
  using reduceOne_gtZero valid_state.elims(2) by blast

lemma reduceContractStep_gtZero_Refund :
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   refundOne (accounts state) = Some ((party, money), newAccount) \<Longrightarrow>
   Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) (state\<lparr>accounts := newAccount\<rparr>) Close =
      Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  using reduceContractStep_gtZero_Refund_aux by auto

lemma MList_delete_preserves_gtZero : "valid_map accs \<Longrightarrow> \<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
                                       positiveMoneyInAccountOrNoAccount y (MList.delete accId accs)"
  by (metis (full_types) MList.delete_lookup_None MList.different_delete_lookup option.simps(4) positiveMoneyInAccountOrNoAccount.simps)

lemma reduceContractStep_gtZero_Pay_aux :
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount x (updateMoneyInAccount accId amount (accounts state))"
  using MList_delete_preserves_gtZero updateMoneyInAccount_gtZero by auto

lemma reduceContractStep_gtZero_Pay :
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   reduceContractStep env state (Pay accId payee val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "evalValue env state val \<le> 0")
  apply simp
  apply (cases "giveMoney payee (min (moneyInAccount accId (accounts state)) (evalValue env state val))
                (updateMoneyInAccount accId (moneyInAccount accId (accounts state) - min (moneyInAccount accId (accounts state)) (evalValue env state val))
                  (accounts state))")
  apply (simp del:positiveMoneyInAccountOrNoAccount.simps valid_state.simps updateMoneyInAccount.simps)
  by (smt MList_delete_preserves_gtZero ReduceStepResult.inject State.select_convs(1) State.surjective State.update_convs(1) giveMoney_gtZero updateMoneyInAccount.simps updateMoneyInAccount_gtZero valid_state.elims(2))

lemma reduceContractStep_gtZero_Let :
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   reduceContractStep env state (Contract.Let valueId val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "state")
  apply (cases "newState")
  apply (simp del:positiveMoneyInAccountOrNoAccount.simps valid_state.simps)
  by (metis ReduceStepResult.inject State.ext_inject)

theorem reduceContractStep_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   reduceContractStep env state cont = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (cases cont)
  apply (cases "refundOne (accounts state)")
  apply simp
  using reduceContractStep_gtZero_Refund apply force
  using reduceContractStep_gtZero_Pay apply blast
  apply simp
  apply (smt ReduceStepResult.distinct(1) ReduceStepResult.inject ReduceStepResult.simps(5) case_prod_unfold reduceContractStep.simps(4))
  using reduceContractStep_gtZero_Let by blast

(* Alternative formulation *)

fun allAccountsPositive :: "(AccountId \<times> Money) list \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r (_, money) . r \<and> money > 0) True accs"

fun allAccountsPositiveState :: "State \<Rightarrow> bool" where
"allAccountsPositiveState state = allAccountsPositive (accounts state)"

lemma allAccountsPositiveMeansFirstIsPositive_aux :
  "(foldl (\<lambda>r ab. r \<and> (case ab of (u, x) \<Rightarrow> 0 < x)) (0 < b) accs \<Longrightarrow> 0 < b) \<Longrightarrow>
   foldl (\<lambda>r ab. r \<and> (case ab of (u, x) \<Rightarrow> 0 < x)) (0 < b \<and> (case a of (u, x) \<Rightarrow> 0 < x)) accs \<Longrightarrow> 0 < b"
  apply (cases "(case a of (u, x) \<Rightarrow> 0 < x)")
  by auto

lemma allAccountsPositiveMeansFirstIsPositive :
 "allAccountsPositive ((a, b) # accs) \<Longrightarrow> 0 < b"
  apply (induction accs)
  apply simp
  apply simp
  using allAccountsPositiveMeansFirstIsPositive_aux by blast

lemma allAccountsPositiveMeansAllAccountsInTailArePositive_aux :
 "(allAccountsPositive ((a, b) # accs) \<Longrightarrow> allAccountsPositive accs) \<Longrightarrow> allAccountsPositive ((a, b) # aa # accs) \<Longrightarrow> allAccountsPositive (aa # accs)"
  apply simp
  apply (cases "(case aa of (u, x) \<Rightarrow> 0 < x)")
  by simp_all

lemma allAccountsPositiveMeansAllAccountsInTailArePositive :
 "allAccountsPositive ((a, b) # accs) \<Longrightarrow> allAccountsPositive accs"
  apply (induction accs)
  apply simp
  using allAccountsPositiveMeansAllAccountsInTailArePositive_aux by blast

lemma allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount_aux :
  "(\<And>accId. allAccountsPositive accs \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId accs) \<Longrightarrow>
   allAccountsPositive ((a, b) # accs) \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId ((a, b) # accs)"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps)
  apply (cases "accId = a")
  apply (simp del:valid_map.simps)
  apply (rule allAccountsPositiveMeansFirstIsPositive)
  apply simp
  apply (simp only:lookup.simps if_False)
  apply (cases "a < accId")
  apply (simp only:if_True)
  using allAccountsPositiveMeansAllAccountsInTailArePositive apply blast
  by simp

lemma allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount :
  "allAccountsPositive accs \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId accs"
  apply (induction accs arbitrary: accId)
  apply simp
  using allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount_aux by auto

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux :
 "b > 0 \<Longrightarrow> allAccountsPositive accs \<Longrightarrow> allAccountsPositive ((a, b) # accs)"
  by simp

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux2 :
  "(valid_map accs \<Longrightarrow> \<forall>accId. positiveMoneyInAccountOrNoAccount accId accs \<Longrightarrow> allAccountsPositive accs) \<Longrightarrow>
   valid_map ((a, b) # accs) \<Longrightarrow> \<forall>accId. positiveMoneyInAccountOrNoAccount accId ((a, b) # accs) \<Longrightarrow> allAccountsPositive ((a, b) # accs)"
  apply (cases "0 \<ge> b")
  apply (simp del:foldl_Cons valid_map.simps)
  apply (smt option.simps(5))
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps)
  apply (rule positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux)
  apply linarith
  using positiveMoneyInAccountOrNoAccount_gtZero_preservation by auto

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive :
  "valid_map accs \<Longrightarrow> (\<forall> accId. positiveMoneyInAccountOrNoAccount accId accs) \<Longrightarrow> allAccountsPositive accs"
  apply (induction accs)
  apply simp
  using positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux2 by auto

theorem accountsArePositive :
  "valid_state state \<Longrightarrow> (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
  computeTransaction txIn state cont = TransactionOutput txOut \<Longrightarrow>
  positiveMoneyInAccountOrNoAccount y (accounts (txOutState txOut))"
  oops

theorem accountsArePositive2 :
    "valid_state state \<Longrightarrow> allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"
  oops
  (* by (meson accountsArePositive allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositiveState.elims(2) allAccountsPositiveState.elims(3) computeTransaction_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive valid_state.elims(2)) *)

fun validAndPositive_state :: "State \<Rightarrow> bool" where
"validAndPositive_state state = (valid_state state \<and> allAccountsPositiveState state)"

lemma validAndPositiveImpliesValid : "validAndPositive_state state \<Longrightarrow> valid_state state"
  by simp

lemma validAndPositiveImpliesPositive : "validAndPositive_state state \<Longrightarrow> (\<forall> x. positiveMoneyInAccountOrNoAccount x (accounts state))"
  using allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount by auto

lemma reduceContractStep_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   reduceContractStep env state cont = Reduced wa eff newState newCont \<Longrightarrow>
   validAndPositive_state newState"
  apply (simp only:validAndPositive_state.simps)
  by (meson allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositiveState.elims(2) allAccountsPositiveState.elims(3) positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive reduceContractStep_gtZero reductionStep_preserves_valid_state valid_state.elims(2))

lemma reduceContractUntilQuiescent_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   reduceContractUntilQuiescent env state contract = ContractQuiescent nwa npa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  oops

lemma applyInput_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyInput env state inp cont = Applied nwa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  oops

lemma applyAllInputs_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyAllInputs env state cont inps = ApplyAllSuccess wa pa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  oops

lemma fixInterval_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   fixInterval inte state = IntervalTrimmed nenv nstate \<Longrightarrow>
   validAndPositive_state nstate"
  oops

lemma applyAllLoop_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyAllLoop env state cont inp wa pa = ApplyAllSuccess nwa npa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  oops

end