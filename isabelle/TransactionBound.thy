theory TransactionBound
  imports Main Semantics PositiveAccounts QuiescentResult ValidState
begin

fun countWhensCaseList :: "Case list \<Rightarrow> nat"
and countWhens :: "Contract \<Rightarrow> nat" where
"countWhensCaseList (Cons (Case _ c) tail) = max (countWhens c) (countWhensCaseList tail)" |
"countWhensCaseList Nil = 0" |
"countWhens Close = 0" |
"countWhens (Pay _ _ _ _ c) = countWhens c" |
"countWhens (If _ c c2) = max (countWhens c) (countWhens c2)" |
"countWhens (When cl t c) = Suc (max (countWhensCaseList cl) (countWhens c))" |
"countWhens (Contract.Let _ _ c) = countWhens c"

fun maxTransactionsCaseList :: "Case list \<Rightarrow> State \<Rightarrow> nat" where
"maxTransactionsCaseList caLi st = Suc (countWhensCaseList caLi)"

fun maxTransactions :: "Contract \<Rightarrow> State \<Rightarrow> nat" where
"maxTransactions c st = (if (isQuiescent c st)
                         then countWhens c
                         else Suc (countWhens c))"

lemma reduceContractStep_quiescent_reduces : "isQuiescent c st \<Longrightarrow>
                                              reduceContractStep env st c = Reduced wa ef nst nc \<Longrightarrow>
                                              countWhens nc < countWhens c"
  apply (induction env st c rule:reduceContractStep.induct)
  apply auto
  by (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject Suc_n_not_le_n case_prod_beta le_less_linear max.coboundedI2)

lemma reduceContractStep_not_quiescent_reduces : "\<not> isQuiescent c st \<Longrightarrow>
                                                  reduceContractStep env st c = Reduced wa ef nst nc \<Longrightarrow>
                                                  countWhens nc \<le> countWhens c"
  apply (induction env st c rule:reduceContractStep.induct)
  apply auto
  subgoal for state
    apply (cases "refundOne (accounts state)")
    by (simp_all add: prod.case_eq_if)
  subgoal for env state accId payee token val cont
    apply (cases token)
    subgoal for tok curr
      apply (cases "evalValue env state val \<le> 0")
      apply simp
      apply simp
      apply (cases "let moneyToPay = evalValue env state val;
                        balance = case lookup (accId, Token tok curr) (accounts state) of None \<Rightarrow> 0 | Some x \<Rightarrow> x;
                        paidMoney = min balance moneyToPay
                    in giveMoney payee (Token tok curr) paidMoney (if balance \<le> moneyToPay
                                                                   then MList.delete (accId, Token tok curr) (accounts state)
                                                                   else MList.insert (accId, Token tok curr) (balance - paidMoney) (accounts state))")
      apply (simp add:Let_def)
    done
  done
  by (metis ReduceStepResult.inject le_eq_less_or_eq)

lemma reduceContractStep_doesnt_increase_maxTransactions : "reduceContractStep env st c = Reduced wa ef nst nc \<Longrightarrow>
                                                            maxTransactions nc nst \<le> maxTransactions c st"
  using reduceContractStep_not_quiescent_reduces reduceContractStep_quiescent_reduces by fastforce

lemma reductionLoop_doesnt_increase_maxTransactions : "reductionLoop env st c wa ef = ContractQuiescent nwa nef nst nc \<Longrightarrow>
                                                       maxTransactions nc nst \<le> maxTransactions c st"
  apply (induction env st c wa ef rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.simps)
      by (metis dual_order.trans reduceContractStep_doesnt_increase_maxTransactions)
      by simp_all
  done

lemma reductionLoop_reduces_maxTransactions : "validAndPositive_state st \<Longrightarrow>
                                               reductionLoop env st c wa ef = ContractQuiescent nwa nef nst nc \<Longrightarrow>
                                               maxTransactions nc nst < maxTransactions c st \<or> c = nc"
  apply (induction env st c wa ef rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.simps)
      by (metis dual_order.trans leD leI le_imp_less_Suc maxTransactions.elims reduceContractStep_doesnt_increase_maxTransactions reduceContractStep_not_quiescent_reduces reduceContractStep_preserves_validAndPositive_state reduceContractStep_quiescent_reduces reductionLoopIsQuiescent)
      apply simp
      by simp
    done

lemma reductionLoop_doesnt_increase_countWhens : "reductionLoop env st c wa ef = ContractQuiescent nwa nef nst nc \<Longrightarrow>
                                                  countWhens nc \<le> countWhens c"
  apply (induction env st c wa ef rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.simps)
      by (metis le_eq_less_or_eq less_trans reduceContractStep_not_quiescent_reduces reduceContractStep_quiescent_reduces)
      by simp_all
    done

lemma applyCases_doesnt_increase_countWhens :
  "validAndPositive_state st \<Longrightarrow>
   applyCases env sta inp casLi = Applied wa nsta ncon \<Longrightarrow>
   countWhens ncon \<le> countWhensCaseList casLi"
  apply (induction env sta inp casLi rule:applyCases.induct)
  apply (simp only:applyCases.simps)
  apply (smt ApplyResult.inject countWhensCaseList.simps(1) le_refl max.coboundedI1 max.coboundedI2) 
  apply (simp only:applyCases.simps)
  apply (metis ApplyResult.inject countWhensCaseList.simps(1) le_refl max.coboundedI1 max.coboundedI2)
  apply (simp only:applyCases.simps)
  apply (metis ApplyResult.inject countWhensCaseList.simps(1) le_refl max.coboundedI1 max.coboundedI2)
  apply (simp only:applyCases.simps)
  by simp_all

lemma applyInput_decreases_countWhens :
  "validAndPositive_state st \<Longrightarrow>
   applyInput env sta inp cont = Applied nwa nsta ncon \<Longrightarrow>
   countWhens ncon < countWhens cont"
  apply (cases cont)
  apply simp
  apply simp
  apply simp
  using applyCases_doesnt_increase_countWhens apply fastforce
  by simp

lemma applyCases_doesnt_increase_maxTransactions :
  "validAndPositive_state st \<Longrightarrow>
   applyCases env sta inp casLi = Applied wa nsta ncon \<Longrightarrow>
   maxTransactions ncon nsta \<le> maxTransactionsCaseList casLi sta"
  by (simp add: applyCases_doesnt_increase_countWhens le_SucI)

lemma applyInput_doesnt_increase_maxTransactions :
  "validAndPositive_state st \<Longrightarrow>
   applyInput env sta inp cont = Applied nwa nsta ncon \<Longrightarrow>
   maxTransactions ncon nsta \<le> maxTransactions cont sta"
  apply (cases cont)
  apply simp
  apply simp
  apply simp
  using applyCases_doesnt_increase_countWhens apply fastforce
  by simp

lemma applyAllLoop_doesnt_increase_maxTransactions :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop env sta cont inpList wa pa = ApplyAllSuccess nwa npa nsta ncont \<Longrightarrow>
   maxTransactions ncont nsta \<le> maxTransactions cont sta"
  apply (induction inpList arbitrary:env sta cont wa pa)
  subgoal for env sta cont wa pa
  apply (simp only:applyAllLoop.simps[of env sta cont "[]" wa pa] list.case)
  apply (cases "reduceContractUntilQuiescent env sta cont")
  subgoal for x11 x12 x13 x14
    apply (simp only:ReduceResult.case)
    using reductionLoop_doesnt_increase_maxTransactions by auto
    by simp
  subgoal for head tail env sta cont wa pa
    apply (simp only:applyAllLoop.simps[of env sta cont "head # tail" wa pa] list.case)
    apply (cases "reduceContractUntilQuiescent env sta cont")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceResult.case)
      apply (cases "applyInput env x13 head x14")
      apply (simp only:ApplyResult.case)
      apply (metis applyInput_doesnt_increase_maxTransactions applyInput_preserves_preserves_validAndPositive_state dual_order.strict_trans2 leD leI reduceContractUntilQuiescent.simps reduceContractUntilQuiescent_preserves_validAndPositive_state reductionLoop_doesnt_increase_maxTransactions)
      by simp
    by simp
  done

lemma reduceContractUntilQuiescent_doesnt_increase_countWhens : "validAndPositive_state state \<Longrightarrow>
      reduceContractUntilQuiescent env state contract = ContractQuiescent x11 x12 x13 x14 \<Longrightarrow>
      countWhens x14 \<le> countWhens contract"
  by (simp add: reductionLoop_doesnt_increase_countWhens)

lemma applyAllLoop_doesnt_increase_countWhens :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop env sta cont inpList wa pa = ApplyAllSuccess nwa npa nsta ncont \<Longrightarrow>
   countWhens ncont \<le> countWhens cont"
  apply (induction env sta cont inpList wa pa rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceResult.case)
      apply (cases "inputs")
      apply (simp only:list.case)
      apply (metis ApplyAllResult.inject Suc_leD Suc_le_eq Suc_le_mono eq_iff maxTransactions.elims reduceContractUntilQuiescent.elims reductionLoop_reduces_maxTransactions)
      subgoal for head tail
        apply (simp only:list.case)
        apply (cases "applyInput env x13 head x14")
        apply (simp only:ApplyResult.case)
        apply (metis applyInput_decreases_countWhens applyInput_preserves_preserves_validAndPositive_state dual_order.trans leD le_cases reduceContractUntilQuiescent_doesnt_increase_countWhens reduceContractUntilQuiescent_preserves_validAndPositive_state)
        by simp
      done
    by simp
  done

lemma applyAllLoop_decreases_maxTransactions :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop env sta cont inpList wa pa = ApplyAllSuccess nwa npa nsta ncont \<Longrightarrow>
   maxTransactions ncont nsta < maxTransactions cont sta \<or> cont = ncont"
  apply (induction env sta cont inpList wa pa rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments] list.case)
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for rwa rpa rsta rcon
      apply (simp only:ReduceResult.case)
      apply (cases inputs)
      using reductionLoop_reduces_maxTransactions apply auto[1]
      apply (simp only:list.case)
      subgoal for head tail
        apply (cases "applyInput env rsta head rcon")
        subgoal for awa asta acon
          apply (simp only:ApplyResult.case)
          apply (cases "isQuiescent contract state")
          apply (simp only:maxTransactions.simps)
          apply (metis (mono_tags) applyAllInputsLoopIsQuiescent applyAllLoop_doesnt_increase_countWhens applyInput_decreases_countWhens applyInput_preserves_preserves_validAndPositive_state max.coboundedI2 max_absorb1 not_le reduceContractUntilQuiescent_doesnt_increase_countWhens reduceContractUntilQuiescent_preserves_validAndPositive_state)
          apply (simp only:maxTransactions.simps if_False)
          by (metis (mono_tags, lifting) applyAllInputsLoopIsQuiescent applyAllLoop_doesnt_increase_countWhens applyInput_decreases_countWhens applyInput_preserves_preserves_validAndPositive_state dual_order.strict_trans1 le_less_trans less_SucI reduceContractUntilQuiescent_doesnt_increase_countWhens reduceContractUntilQuiescent_preserves_validAndPositive_state)
      by simp
      done
    by simp
  done

lemma minSlot_doesnt_affect_maxTransactions :
  "maxTransactions cont (sta\<lparr>minSlot := y\<rparr>) = maxTransactions cont sta"
  apply (cases cont)
  by simp_all

lemma fixInterval_preserves_maxTransactions :
  "fixInterval interv sta = IntervalTrimmed env fixedState \<Longrightarrow>
   maxTransactions cont fixedState = maxTransactions cont sta"
  apply (cases interv)
  apply (simp only:fixInterval.simps)
  subgoal for left right
    apply (cases "right < left")
    apply simp
    apply (cases "right < minSlot sta")
    apply simp
    apply (simp del:maxTransactions.simps add:Let_def)
    using minSlot_doesnt_affect_maxTransactions by blast
  done

lemma computeTransaction_decreases_maxTransactions_aux :
  "validAndPositive_state fixedState \<Longrightarrow>
   applyAllInputs env fixedState cont inps = ApplyAllSuccess nwarn npay nstate ncont \<Longrightarrow>
   cont \<noteq> ncont \<Longrightarrow> maxTransactions ncont nstate < maxTransactions cont fixedState"
  using applyAllLoop_decreases_maxTransactions by fastforce

lemma computeTransaction_decreases_maxTransactions :
  "validAndPositive_state sta \<Longrightarrow>
   computeTransaction tra sta cont = TransactionOutput txOut \<Longrightarrow>
   maxTransactions (txOutContract txOut) (txOutState txOut) < maxTransactions cont sta"
  apply (simp only:computeTransaction.simps)
  apply (cases "fixInterval (interval tra) sta")
  apply (simp only:IntervalResult.case)
  subgoal for env fixedState
    apply (cases "applyAllInputs env fixedState cont (inputs tra)")
    subgoal for nwarn npay nstate ncont
      apply (cases "cont = ncont \<and> (cont \<noteq> Close \<or> accounts sta = [])")
      apply simp
      apply (simp del:validAndPositive_state.simps fixInterval.simps applyAllInputs.simps maxTransactions.simps)
      by (metis TransactionOutput.inject(1) TransactionOutputRecord.select_convs(3) TransactionOutputRecord.select_convs(4) applyAllInputsIsQuiescent computeTransaction_decreases_maxTransactions_aux fixInterval_preserves_maxTransactions fixInterval_preserves_preserves_validAndPositive_state isQuiescent.simps(1) less_irrefl maxTransactions.simps not_less_eq)
     apply simp
    by simp
  by simp

lemma playTraceAux_only_accepts_maxTransactions_aux :
  "validAndPositive_state (txOutState txIn) \<Longrightarrow>
   l \<noteq> Nil \<Longrightarrow>
   playTraceAux txIn l = TransactionOutput txOut \<Longrightarrow>
   maxTransactions (txOutContract txOut) (txOutState txOut) < maxTransactions (txOutContract txIn) (txOutState txIn)"
  apply (induction txIn l rule:playTraceAux.induct)
  apply blast
  subgoal for warnings payments state cont h t
    apply (cases "computeTransaction h state cont")
    apply (simp del:validAndPositive_state.simps computeTransaction.simps maxTransactions.simps add:Let_def)
    apply (metis TransactionOutput.inject(1) TransactionOutputRecord.select_convs(3) TransactionOutputRecord.select_convs(4) TransactionOutputRecord.surjective TransactionOutputRecord.update_convs(1) TransactionOutputRecord.update_convs(2) computeTransaction_decreases_maxTransactions computeTransaction_preserves_validAndPositive_state dual_order.strict_trans playTraceAux.simps(1))
    by simp
  done

lemma playTraceAux_only_accepts_maxTransactions :
  "validAndPositive_state (txOutState txIn) \<Longrightarrow>
   playTraceAux txIn tList = TransactionOutput txOut \<Longrightarrow>
   length tList \<le> maxTransactions (txOutContract txIn) (txOutState txIn)"
  apply (induction tList arbitrary: txIn txOut)
  apply simp
  subgoal for head tail txIn txOut
    apply (cases txIn)
    apply (simp only:playTraceAux.simps)
    subgoal for txOutWarningsa txOutPaymentsa txOutStatea txOutContracta
      apply (cases "computeTransaction head txOutStatea txOutContracta")
      apply (simp del:validAndPositive_state.simps computeTransaction.simps maxTransactions.simps add:Let_def)
      apply (metis (mono_tags, lifting) TransactionOutputRecord.select_convs(3) TransactionOutputRecord.select_convs(4) TransactionOutputRecord.surjective TransactionOutputRecord.update_convs(1) TransactionOutputRecord.update_convs(2) computeTransaction_decreases_maxTransactions computeTransaction_preserves_validAndPositive_state le_trans not_le not_less_eq)
      by simp
    done
  done

fun maxTransactionsInitialStateSN :: "int \<Rightarrow> Contract \<Rightarrow> nat" where
  "maxTransactionsInitialStateSN sl c = maxTransactions c (emptyState sl)"

lemma playTrace_only_accepts_maxTransactionsInitialStateSN :
  "playTrace sl c l = TransactionOutput txOut \<Longrightarrow>
   length l \<le> maxTransactionsInitialStateSN sl c"
  apply (simp only:playTrace.simps maxTransactionsInitialStateSN.simps)
  using playTraceAux_only_accepts_maxTransactions validAndPositive_initial_state by force

fun maxTransactionsInitialState :: "Contract \<Rightarrow> nat" where
  "maxTransactionsInitialState (When cl n c) = countWhens (When cl n c)" |
  "maxTransactionsInitialState Close = countWhens Close" |
  "maxTransactionsInitialState cont = Suc (countWhens cont)"

lemma maxTransactionsInitialState_equiv_maxTransactionsInitialStateSN :
  "maxTransactionsInitialStateSN sl c = maxTransactionsInitialState c"
  apply simp
  apply (cases c)
  by (simp_all add:MList.empty_def)

lemma playTrace_only_accepts_maxTransactionsInitialState :
  "playTrace sl c l = TransactionOutput txOut \<Longrightarrow>
   length l \<le> maxTransactionsInitialState c"
  using maxTransactionsInitialState_equiv_maxTransactionsInitialStateSN playTrace_only_accepts_maxTransactionsInitialStateSN by auto

end