theory PositiveAccounts
imports Semantics ValidState
begin

fun positiveMoneyInAccountOrNoAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Accounts \<Rightarrow> bool" where
"positiveMoneyInAccountOrNoAccount accId tok mlist =
  (case MList.lookup (accId, tok) mlist of
     None \<Rightarrow> True
   | Some x \<Rightarrow> x > 0)"

lemma addMoneyToAccountPositve_match :
 "\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y tok2 (MList.insert (y, tok2) newBalance accs)"
  apply simp
  by (simp add: MList.insert_lookup_Some)

lemma addMoneyToAccountPositive_noMatch :
 "\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
    money > 0 \<Longrightarrow>
    (accId, tok) \<noteq> (y, tok2) \<Longrightarrow>
    newBalance > 0 \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y tok2 (MList.insert (accId, tok2) newBalance accs)"
  by (metis addMoneyToAccountPositve_match insert_lookup_different positiveMoneyInAccountOrNoAccount.elims(2) positiveMoneyInAccountOrNoAccount.elims(3))

lemma updateMoneyInAccount_gtZero :
 "0 < newBalance \<Longrightarrow>
  \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
  positiveMoneyInAccountOrNoAccount y tok2 (updateMoneyInAccount accId tok2 newBalance accs)"
  by (metis addMoneyToAccountPositive_noMatch addMoneyToAccountPositve_match not_less updateMoneyInAccount.simps)
  
lemma addMoneyToAccountPositive :
  "(\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs)
  \<Longrightarrow> positiveMoneyInAccountOrNoAccount y tok2 (addMoneyToAccount accId tok3 money accs)"
  apply (simp only:"addMoneyToAccount.simps")
  apply (cases "money \<le> 0")
  apply simp
  apply (cases "lookup (accId, tok3) accs")
  apply simp
  apply (metis MList.insert_lookup_Some insert_lookup_different not_le option.simps(5) surj_pair)
  apply simp
  by (smt MList.insert_lookup_Some insert_lookup_different option.simps(5) prod_cases3)

lemma giveMoney_gtZero :
    "\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
       (eff, newAccs) = giveMoney src payee tok2 money accs \<Longrightarrow>
       positiveMoneyInAccountOrNoAccount y tok3 newAccs"
  apply (cases payee)
  apply (simp del:positiveMoneyInAccountOrNoAccount.simps addMoneyToAccount.simps)
  apply (rule addMoneyToAccountPositive)
  apply simp
  by (simp del:positiveMoneyInAccountOrNoAccount.simps addMoneyToAccount.simps)

lemma positiveMoneyInAccountOrNoAccount_valid_zero : "valid_map (((accId, tok), money) # rest) \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId tok rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (simp add: MList.delete_lookup_None_aux)

lemma positiveMoneyInAccountOrNoAccount_sublist_gtZero_different :
  "valid_map ((accIdTok, money) # rest) \<Longrightarrow>
   0 < money \<Longrightarrow> positiveMoneyInAccountOrNoAccount y tok ((accIdTok, money) # rest) \<Longrightarrow>
   accIdTok \<noteq> (y, tok) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y tok rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (metis MList.delete.simps(2) MList.different_delete_lookup)

lemma positiveMoneyInAccountOrNoAccount_sublist_gtZero :
    "valid_map ((accIdTok, money) # rest) \<Longrightarrow>
     money > 0 \<Longrightarrow>
    (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok ((accIdTok, money) # rest)) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y tok2 rest"
  apply (cases "accIdTok = (y, tok2)")
  using positiveMoneyInAccountOrNoAccount_valid_zero apply auto[1]
  using positiveMoneyInAccountOrNoAccount_sublist_gtZero_different by blast

lemma positiveMoneyInAccountOrNoAccount_gtZero_preservation :
  "valid_map ((accIdTok, money) # rest) \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok ((accIdTok, money) # rest)) \<Longrightarrow> positiveMoneyInAccountOrNoAccount y tok2 rest"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps findWithDefault.simps)
  by (metis (no_types, lifting) MList.delete.simps(2) MList.delete_lookup_None MList.sublist_valid delete_step lookup.simps(2) option.simps(4))

lemma reduceOne_gtZero :
  "valid_map accs \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
   refundOne accs = Some (paym, newAccs) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 newAccs"
  apply (induction accs rule:"refundOne.induct")
  subgoal for accId tok money rest
    apply (cases "money > 0")
    apply (simp only:refundOne.simps if_True)
    apply (metis option.inject positiveMoneyInAccountOrNoAccount_gtZero_preservation prod.inject)
    by (metis MList.sublist_valid positiveMoneyInAccountOrNoAccount_gtZero_preservation refundOne.simps(1))
  by auto

lemma reduceContractStep_gtZero_Refund :
  "valid_state state \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
   refundOne (accounts state) = Some ((party, tok2, money), newAccount) \<Longrightarrow>
   Reduced ReduceNoWarning (ReduceWithPayment (Payment party (Party party) tok2 money)) (state\<lparr>accounts := newAccount\<rparr>) Close =
      Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok3 (accounts newState)"
  by (metis (mono_tags) ReduceStepResult.inject State.simps(1) State.surjective State.update_convs(1) reduceOne_gtZero valid_state_valid_accounts)

lemma MList_delete_preserves_gtZero : "valid_map accs \<Longrightarrow> \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok accs \<Longrightarrow>
                                       positiveMoneyInAccountOrNoAccount y tok2 (MList.delete accIdTok accs)"
  by (metis (full_types) MList.delete_lookup_None MList.different_delete_lookup option.simps(4) positiveMoneyInAccountOrNoAccount.simps)

lemma reduceContractStep_gtZero_Pay_aux :
  "valid_state state \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (updateMoneyInAccount accId tok3 amount (accounts state))"
  by (metis MList_delete_preserves_gtZero insert_lookup_different not_le positiveMoneyInAccountOrNoAccount.elims(2) positiveMoneyInAccountOrNoAccount.elims(3) updateMoneyInAccount.simps updateMoneyInAccount_gtZero valid_state_valid_accounts)

lemma reduceContractStep_gtZero_Pay :
  "valid_state state \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
   reduceContractStep env state (Pay accId payee tok2 val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok3 (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "evalValue env state val \<le> 0")
  apply simp
  apply (cases "giveMoney accId payee tok2 (min (moneyInAccount accId tok2 (accounts state)) (evalValue env state val))
                (updateMoneyInAccount accId tok2
                  (moneyInAccount accId tok2 (accounts state) - min (moneyInAccount accId tok2 (accounts state)) (evalValue env state val))
                  (accounts state))")
  apply (simp del:positiveMoneyInAccountOrNoAccount.simps valid_state.simps updateMoneyInAccount.simps)
  apply (cases payee)
  apply (simp only:addMoneyToAccountPositive reduceContractStep_gtZero_Pay_aux)
  apply (metis (no_types, lifting) Payee.simps(5) ReduceStepResult.inject State.simps(1) State.surjective State.update_convs(1) addMoneyToAccountPositive reduceContractStep_gtZero_Pay_aux)
  by (metis (no_types, lifting) Payee.simps(6) ReduceStepResult.inject State.iffs State.surjective State.update_convs(1) reduceContractStep_gtZero_Pay_aux)

lemma reduceContractStep_gtZero_Let :
  "valid_state state \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
   reduceContractStep env state (Contract.Let valueId val cont) = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (simp only:reduceContractStep.simps)
  apply (cases "state")
  apply (cases "newState")
  apply (simp del:positiveMoneyInAccountOrNoAccount.simps valid_state.simps)
  by (metis ReduceStepResult.inject State.ext_inject)

theorem reduceContractStep_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   reduceContractStep env state cont = Reduced wa eff newState newCont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (cases cont)
  apply (cases "refundOne (accounts state)")
  apply simp
  apply (metis (mono_tags, lifting) option.simps(5) prod.case_eq_if prod.collapse reduceContractStep.simps(1) reduceContractStep_gtZero_Refund)
  using reduceContractStep_gtZero_Pay apply blast
  apply simp
  apply (smt ReduceStepResult.distinct(1) ReduceStepResult.inject ReduceStepResult.simps(5) case_prod_unfold reduceContractStep.simps(4))
  using reduceContractStep_gtZero_Let apply blast
  by simp

lemma reduceLoop_gtZero : 
  "valid_state state \<Longrightarrow>
    \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
    reductionLoop env state contract warns pays = ContractQuiescent nwa npa newState ncont \<Longrightarrow>
    positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (induction env state contract warns pays rule: reductionLoop.induct)
  subgoal for env state contract warns pays 
    apply (cases "reduceContractStep env state contract")
    apply (simp only:reductionLoop.simps [of env state contract warns pays])
      apply (metis (no_types, lifting) ReduceStepResult.simps(8) reduceContractStep_gtZero reductionStep_preserves_valid_state)
    apply fastforce
    by simp_all
  done

lemma reduceContractUntilQuiescent_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   reduceContractUntilQuiescent env state contract = ContractQuiescent nwa npa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (simp only:reduceContractUntilQuiescent.simps)
  using reduceLoop_gtZero by blast

lemma applyCases_positive : "valid_state state \<Longrightarrow>
       \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
       applyCases env state inp cases = Applied nwa newState ncont \<Longrightarrow>
       positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  (* Deposit case *)
  apply (induction env state inp cases rule: applyCases.induct)
  subgoal for env state accId1 party1 tok1 amount accId2 party2 tok2a val cont rest
    apply (simp only:applyCases.simps(1) [of env state accId1 party1 tok1 amount accId2 party2 tok2 val cont rest])
    apply (cases "accId1 = accId2 \<and> party1 = party2 \<and> tok1 = tok2a \<and> amount = evalValue env state val")
    apply (cases " evalValue env state val \<le> 0")
    apply (simp add:Let_def del:valid_state.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
    apply (simp add:Let_def del:valid_state.simps updateMoneyInAccount.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
    apply (metis State.simps(1) State.surjective State.update_convs(1) reduceContractStep_gtZero_Pay_aux)
    by (simp add:Let_def del:valid_state.simps updateMoneyInAccount.simps positiveMoneyInAccountOrNoAccount.simps moneyInAccount.simps)
  (* Choice case *)
  apply (metis ApplyResult.inject State.ext_inject State.simps(7) State.surjective applyCases.simps(2))
  (* Notify case *)
  apply (metis ApplyResult.inject applyCases.simps(3))
  (* Rest of cases *)
  by auto

lemma applyInput_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   applyInput env state inp cont = Applied nwa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (cases cont)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (simp only:applyInput.simps)
  using applyCases_positive apply blast
  apply simp
  by simp

lemma applyAllLoop_gtZero : 
  "valid_state state \<Longrightarrow>
   \<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state) \<Longrightarrow>
   applyAllLoop env state cont inps warns pays = ApplyAllSuccess wa pa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
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
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   applyAllInputs env state cont inps = ApplyAllSuccess wa pa newState ncont \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (simp only:applyAllInputs.simps)
  using applyAllLoop_gtZero by blast

lemma fixInterval_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   fixInterval inte state = IntervalTrimmed nenv newState \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts newState)"
  apply (cases  inte)
  apply (simp only:fixInterval.simps)
  by (smt IntervalResult.distinct(1) IntervalResult.inject(1) State.select_convs(1) State.surjective State.update_convs(4))

theorem computeTransaction_gtZero :
  "valid_state state \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
   computeTransaction tx state contract = (TransactionOutput txOut) \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts (txOutState txOut))"
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

lemma playTraceAux_gtZero :
  "valid_state (txOutState txIn) \<Longrightarrow>
   (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts (txOutState txIn))) \<Longrightarrow>
   playTraceAux txIn transList = TransactionOutput txOut \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok2 (accounts (txOutState txOut))"
  apply (induction txIn transList rule:playTraceAux.induct)
  apply simp
  apply (cases txOut)
  subgoal for state cont h t txOutWarnings txOutPayments txOutStatea txOutContract
    apply (simp del:valid_state.simps computeTransaction.simps positiveMoneyInAccountOrNoAccount.simps add:Let_def)
    apply (cases "computeTransaction txOutWarnings h t")
    using computeTransaction_gtZero computeTransaction_preserves_valid_state apply auto[1]
    by simp
  done

lemma emptyState_gtZero : "positiveMoneyInAccountOrNoAccount y tok (accounts (emptyState sl))"
  apply simp
  by (simp add: MList.lookup_empty)  

theorem playTrace_gtZero :
  "playTrace sl contract t = TransactionOutput txOut \<Longrightarrow>
   positiveMoneyInAccountOrNoAccount y tok (accounts (txOutState txOut))"
  by (metis TransactionOutputRecord.select_convs(3) emptyState_gtZero playTrace.simps playTraceAux.simps(1) playTraceAux_gtZero playTrace_preserves_valid_state)

(* Alternative formulation *)

fun allAccountsPositive :: "Accounts \<Rightarrow> bool" where
"allAccountsPositive accs = foldl (\<lambda> r ((_, _), money) . r \<and> money > 0) True accs"

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
  apply (simp add: case_prod_beta')
  by (simp add: case_prod_beta')

lemma allAccountsPositiveMeansAllAccountsInTailArePositive :
 "allAccountsPositive ((a, b) # accs) \<Longrightarrow> allAccountsPositive accs"
  apply (induction accs)
  apply simp
  using allAccountsPositiveMeansAllAccountsInTailArePositive_aux by blast

lemma allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount_aux :
  "(\<And>accId tok. allAccountsPositive accs \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId tok accs) \<Longrightarrow>
   allAccountsPositive ((a, b) # accs) \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId2 tok2 ((a, b) # accs)"
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps)
  apply (cases "(accId2, tok2) = a")
  apply (simp del:valid_map.simps)
  apply (rule allAccountsPositiveMeansFirstIsPositive)
  apply simp
  apply (simp only:lookup.simps if_False)
  apply (cases "a < (accId2, tok2)")
  apply (simp only:if_True)
  using allAccountsPositiveMeansAllAccountsInTailArePositive apply blast
  by simp

lemma allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount :
  "allAccountsPositive accs \<Longrightarrow> positiveMoneyInAccountOrNoAccount accId tok accs"
  apply (induction accs arbitrary: accId tok)
  apply simp
  using allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount_aux by auto

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux :
 "b > 0 \<Longrightarrow> allAccountsPositive accs \<Longrightarrow> allAccountsPositive ((a, b) # accs)"
  by simp

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux2 :
  "(valid_map accs \<Longrightarrow> \<forall>accId tok. positiveMoneyInAccountOrNoAccount accId tok accs \<Longrightarrow> allAccountsPositive accs) \<Longrightarrow>
   valid_map ((a, b) # accs) \<Longrightarrow> \<forall>accId tok. positiveMoneyInAccountOrNoAccount accId tok ((a, b) # accs) \<Longrightarrow> allAccountsPositive ((a, b) # accs)"
  apply (cases "0 \<ge> b")
  apply (simp del:foldl_Cons valid_map.simps)
  apply (smt old.prod.exhaust option.simps(5))
  apply (simp only:positiveMoneyInAccountOrNoAccount.simps)
  apply (rule positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux)
  apply linarith
  by (meson MList.sublist_valid positiveMoneyInAccountOrNoAccount.simps positiveMoneyInAccountOrNoAccount_gtZero_preservation)

lemma positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive :
  "valid_map accs \<Longrightarrow> (\<forall> accId tok. positiveMoneyInAccountOrNoAccount accId tok accs) \<Longrightarrow> allAccountsPositive accs"
  apply (induction accs)
  apply simp
  using positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive_aux2 by auto

theorem accountsArePositive :
  "valid_state state \<Longrightarrow> (\<forall>x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state)) \<Longrightarrow>
  computeTransaction txIn state cont = TransactionOutput txOut \<Longrightarrow>
  positiveMoneyInAccountOrNoAccount y tok2 (accounts (txOutState txOut))"
  using computeTransaction_gtZero by blast

theorem accountsArePositive2 :
    "valid_state state \<Longrightarrow> allAccountsPositiveState state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"  
  by (meson accountsArePositive allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositiveState.elims(2) allAccountsPositiveState.elims(3) computeTransaction_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive valid_state.elims(2))

lemma valid_state_valid_accounts : "valid_state state \<Longrightarrow> valid_map (accounts state)"
  apply (cases state)
  by simp

theorem accountsArePositive2_trace :
    "valid_state (txOutState txIn) \<Longrightarrow> allAccountsPositiveState (txOutState txIn)
    \<Longrightarrow> playTraceAux txIn transList = TransactionOutput txOut
    \<Longrightarrow> allAccountsPositiveState (txOutState txOut)"
  by (meson allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositiveState.simps playTraceAux_gtZero playTraceAux_preserves_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive valid_state_valid_accounts)

fun validAndPositive_state :: "State \<Rightarrow> bool" where
"validAndPositive_state state = (valid_state state \<and> allAccountsPositiveState state)"

lemma validAndPositiveImpliesValid : "validAndPositive_state state \<Longrightarrow> valid_state state"
  by simp

lemma validAndPositiveImpliesPositive : "validAndPositive_state state \<Longrightarrow> (\<forall> x tok. positiveMoneyInAccountOrNoAccount x tok (accounts state))"
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

lemma computeTransaction_preserves_validAndPositive_state :
    "validAndPositive_state state
    \<Longrightarrow> computeTransaction txIn state cont = TransactionOutput txOut
    \<Longrightarrow> validAndPositive_state (txOutState txOut)"  
  using accountsArePositive2 computeTransaction_preserves_valid_state validAndPositive_state.simps by blast

lemma playTraceAux_preserves_validAndPositive_state :
  "validAndPositive_state (txOutState txIn) \<Longrightarrow>
   playTraceAux txIn transList = TransactionOutput txOut \<Longrightarrow>
   validAndPositive_state (txOutState txOut)"
  using accountsArePositive2_trace playTraceAux_preserves_valid_state validAndPositive_state.simps by blast

lemma validAndPositive_initial_state : "validAndPositive_state (emptyState sl)"
  using emptyState_gtZero empty_state_valid_state positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive by auto

end