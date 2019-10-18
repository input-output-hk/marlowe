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

lemma reduceOne_gtZero :
  "valid_map accs \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x accs \<Longrightarrow>
   refundOne accs = Some (paym, newAccs) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y newAccs"
  apply (induction accs rule:"refundOne.induct")
  subgoal for accId money rest
    apply (cases "money > 0")
    apply (simp only:refundOne.simps)
    using positiveMoneyInAccountOrNoAccount_gtZero_preservation apply auto[1]
    apply (simp only:refundOne.simps if_False)
    using positiveMoneyInAccountOrNoAccount_gtZero_preservation by auto
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

lemma reduceLoop_gtZero : 
  "valid_state state \<Longrightarrow>
    \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
    reductionLoop env state contract warns pays = ContractQuiescent nwa npa newState ncont \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (induction env state contract warns pays rule: reductionLoop.induct)
  subgoal for env state contract warns pays 
    apply (cases "reduceContractStep env state contract")
    apply (simp only:reductionLoop.simps [of env state contract warns pays])
    apply (metis (no_types, lifting) ReduceStepResult.simps(8) reduceContractStep_gtZero reductionStep_preserves_valid_state)
    by simp_all
  done

lemma reduceContractUntilQuiescent_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   reduceContractUntilQuiescent env state contract = ContractQuiescent nwa npa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (simp only:reduceContractUntilQuiescent.simps)
  using reduceLoop_gtZero by blast

lemma applyCases_positive : "valid_state state \<Longrightarrow>
       \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
       applyCases env state inp cases = Applied nwa newState ncont \<Longrightarrow>
       positiveMoneyInAccountOrNoAccount y (accounts newState)"
  (* Deposit case *)
  apply (induction env state inp cases rule: applyCases.induct)
  subgoal for env state accId1 party1 money accId2 party2 val cont rest
    apply (simp only:applyCases.simps(1) [of env state accId1 party1 money accId2 party2 val cont rest])
    apply (cases "accId1 = accId2 \<and> party1 = party2 \<and> money = ( evalValue env state val)")
    apply (cases " evalValue env state val \<le> 0")
    apply (simp add:Let_def del:valid_state.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
    apply (simp add:Let_def del:valid_state.simps updateMoneyInAccount.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
    using reduceContractStep_gtZero_Pay_aux apply auto[1]
  by (simp add:Let_def del:valid_state.simps updateMoneyInAccount.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
  (* Choice case *)
  apply (metis ApplyResult.inject State.ext_inject State.simps(7) State.surjective applyCases.simps(2))
  (* Notify case *)
  apply (metis ApplyResult.inject applyCases.simps(3))
  (* Rest of cases *)
  by auto

lemma applyInput_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   applyInput env state inp cont = Applied nwa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (cases cont)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp only:applyInput.simps)
  using applyCases_positive apply blast
  by simp

lemma applyAllLoop_gtZero : 
  "valid_state state \<Longrightarrow>
   \<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state) \<Longrightarrow>
   applyAllLoop env state cont inps warns pays = ApplyAllSuccess wa pa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (induction  env state cont inps warns pays rule: applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments
    apply (cases inputs)
    apply (simp only:list.case applyAllLoop.simps [of env state contract "[]" warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    apply (simp only:ReduceResult.case)
    using reduceContractUntilQuiescent_gtZero apply auto[1]
    apply simp
    subgoal for h t
      apply (simp only:list.case applyAllLoop.simps [of env state contract "h#t" warnings payments])
      apply (cases "reduceContractUntilQuiescent env state contract")
      apply (simp only:ReduceResult.case)
      subgoal for newWarns newPays newSta newCont
        apply (cases "applyInput env newSta h newCont")
        apply (simp only:ApplyResult.case)
        apply (metis applyInput_gtZero applyInput_preserves_valid_state reduceContractUntilQuiescent.simps reduceLoop_gtZero reductionLoop_preserves_valid_state)
        by simp
      by simp
    done
  done

lemma applyAllInputs_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   applyAllInputs env state cont inps = ApplyAllSuccess wa pa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (simp only:applyAllInputs.simps)
  using applyAllLoop_gtZero by blast


lemma fixInterval_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   fixInterval inte state = IntervalTrimmed nenv newState \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts newState)"
  apply (cases  inte)
  apply (simp only:fixInterval.simps)
  by (smt IntervalResult.distinct(1) IntervalResult.inject(1) State.select_convs(1) State.surjective State.update_convs(4))


theorem computeTransaction_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x. positiveMoneyInAccountOrNoAccount x (accounts state)) \<Longrightarrow>
   computeTransaction tx state contract = (TransactionOutput txOut) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y (accounts (txOutState txOut))"
 
  apply (simp only:computeTransaction.simps)
  apply (cases "fixInterval (interval tx) state")
  apply (simp only:IntervalResult.case)
  subgoal for env state
    apply (simp only:Let_def)
    apply (cases "applyAllInputs env state contract (inputs tx)")
    apply (simp only:ApplyAllResult.case)
    apply (metis TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.select_convs(3) applyAllInputs_gtZero fixInterval_gtZero fixInterval_preserves_valid_state old.prod.exhaust)
    by auto
  by auto

(* Alternative formulation *)

fun allAccountsPositive :: "(AccountId \<times> Money) list \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r (_, money) . r \<and> money > 0) True accs"

fun allAccountsPositiveState :: "State \<Rightarrow> bool" where
"allAccountsPositiveState state = allAccountsPositive (accounts state)"

lemma allAccountsPositiveMeansFirstIsPositive :
 "allAccountsPositive ((a, b) # accs) \<Longrightarrow> 0 < b"
  apply (induction accs)
  apply simp
  subgoal for aa accs
    apply simp
    apply (cases "(case aa of (uu_, x) \<Rightarrow> 0 < x)")
    by auto
  done

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
  using computeTransaction_gtZero by blast

theorem accountsArePositive2 :
    "valid_state state \<Longrightarrow> allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"  
  by (meson accountsArePositive allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositiveState.elims(2) allAccountsPositiveState.elims(3) computeTransaction_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive valid_state.elims(2))

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
  by (metis allAccountsPositiveState.elims(3) positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive reduceContractUntilQuiescent.simps reduceContractUntilQuiescent_gtZero reductionLoop_preserves_valid_state validAndPositiveImpliesPositive validAndPositiveImpliesValid validAndPositive_state.elims(3) valid_state.elims(2))

lemma applyInput_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyInput env state inp cont = Applied nwa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  by (meson allAccountsPositiveState.simps applyInput_gtZero applyInput_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive validAndPositiveImpliesPositive validAndPositive_state.simps valid_state.simps)

lemma applyAllInputs_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyAllInputs env state cont inps = ApplyAllSuccess wa pa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  by (metis allAccountsPositiveState.elims(3) applyAllInputs.simps applyAllInputs_gtZero applyAllLoop_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive validAndPositiveImpliesPositive validAndPositiveImpliesValid validAndPositive_state.elims(3) valid_state.elims(2))

lemma fixInterval_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   fixInterval inte state = IntervalTrimmed nenv nstate \<Longrightarrow>
   validAndPositive_state nstate"
  by (metis allAccountsPositiveState.elims(3) fixInterval_gtZero fixInterval_preserves_valid_state old.prod.exhaust positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive validAndPositiveImpliesPositive validAndPositiveImpliesValid validAndPositive_state.elims(3) valid_state.simps)

lemma applyAllLoop_preserves_preserves_validAndPositive_state :
  "validAndPositive_state state \<Longrightarrow>
   applyAllLoop env state cont inp wa pa = ApplyAllSuccess nwa npa nstate ncont \<Longrightarrow>
   validAndPositive_state nstate"
  by (meson allAccountsPositiveState.simps applyAllLoop_gtZero applyAllLoop_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive validAndPositiveImpliesPositive validAndPositive_state.simps valid_state.simps)

end