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
"countWhens (Contract.Let _ _ c) = countWhens c" |
"countWhens (Assert _ c) = Suc (countWhens c)"

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
                    in giveMoney accId payee (Token tok curr) paidMoney (if balance \<le> moneyToPay
                                                                         then MList.delete (accId, Token tok curr) (accounts state)
                                                                         else MList.insert (accId, Token tok curr) (balance - paidMoney) (accounts state))")
      apply (simp add:Let_def)
    done
  done
  by (metis ReduceStepResult.inject eq_imp_le)

lemma reduceContractStep_doesnt_increase_maxTransactions : "reduceContractStep env st c = Reduced wa ef nst nc \<Longrightarrow>
                                                            maxTransactions nc nst \<le> maxTransactions c st"
  using reduceContractStep_not_quiescent_reduces reduceContractStep_quiescent_reduces by fastforce

lemma reductionLoop_doesnt_increase_maxTransactions : "reductionLoop reduced env st c wa ef = ContractQuiescent newReduced nwa nef nst nc \<Longrightarrow>
                                                       maxTransactions nc nst \<le> maxTransactions c st"
  apply (induction reduced env st c wa ef rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of reduced env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.simps)
      by (metis dual_order.trans reduceContractStep_doesnt_increase_maxTransactions)
      by simp_all
  done

lemma reductionLoop_reduces_maxTransactions : "validAndPositive_state st \<Longrightarrow>
                                               reductionLoop reduced env st c wa ef = ContractQuiescent newReduced nwa nef nst nc \<Longrightarrow>
                                               (maxTransactions nc nst < maxTransactions c st \<or> (c = nc \<and> reduced = newReduced))"
  apply (induction reduced env st c wa ef rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of reduced env state contract warnings payments])
     apply (cases "reduceContractStep env state contract")
     subgoal for x11 x12 x13 x14
       apply (simp only:ReduceStepResult.simps)
       by (metis le_imp_less_Suc less_le_trans maxTransactions.elims reduceContractStep_doesnt_increase_maxTransactions reduceContractStep_not_quiescent_reduces reduceContractStep_preserves_validAndPositive_state reduceContractStep_quiescent_reduces reductionLoopIsQuiescent)
      apply simp
      by simp
    done

lemma reductionLoop_doesnt_increase_countWhens : "reductionLoop reduced env st c wa ef = ContractQuiescent newReduced nwa nef nst nc \<Longrightarrow>
                                                  countWhens nc \<le> countWhens c"
  apply (induction reduced env st c wa ef rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of reduced env state contract warnings payments])
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
  apply simp
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
  apply simp
  by simp

lemma applyAllLoop_doesnt_increase_maxTransactions :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop reduced env sta cont inpList wa pa = ApplyAllSuccess newReduced nwa npa nsta ncont \<Longrightarrow>
   maxTransactions ncont nsta \<le> maxTransactions cont sta"
  apply (induction inpList arbitrary:reduced env sta cont wa pa)
  subgoal for reduced env sta cont wa pa
  apply (simp only:applyAllLoop.simps[of reduced env sta cont "[]" wa pa] list.case)
  apply (cases "reduceContractUntilQuiescent env sta cont")
  subgoal for x11 x12 x13 x14 x15
    apply (simp only:ReduceResult.case)
    using reductionLoop_doesnt_increase_maxTransactions by auto
    by simp
  subgoal for head tail reduced env sta cont wa pa
    apply (simp only:applyAllLoop.simps[of reduced env sta cont "head # tail" wa pa] list.case)
    apply (cases "reduceContractUntilQuiescent env sta cont")
    subgoal for x11 x12 x13 x14 x15
      apply (simp only:ReduceResult.case)
      apply (cases "applyInput env x14 head x15")
       apply (simp only:ApplyResult.case)
      apply (metis (full_types) applyInput_doesnt_increase_maxTransactions applyInput_preserves_preserves_validAndPositive_state le_trans reduceContractUntilQuiescent.simps reduceContractUntilQuiescent_preserves_validAndPositive_state reductionLoop_doesnt_increase_maxTransactions)
      by simp
    by simp
  done

lemma reduceContractUntilQuiescent_doesnt_increase_countWhens : "validAndPositive_state state \<Longrightarrow>
      reduceContractUntilQuiescent env state contract = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
      countWhens x15 \<le> countWhens contract"
  by (simp add: reductionLoop_doesnt_increase_countWhens)

lemma applyAllLoop_doesnt_increase_countWhens :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop reduced env sta cont inpList wa pa = ApplyAllSuccess newReduced nwa npa nsta ncont \<Longrightarrow>
   countWhens ncont \<le> countWhens cont"
  apply (induction reduced env sta cont inpList wa pa rule:applyAllLoop.induct)
  subgoal for reduced env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of reduced env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for x11 x12 x13 x14 x15
      apply (simp only:ReduceResult.case)
      apply (cases "inputs")
       apply (simp only:list.case)
      apply (simp add: reductionLoop_doesnt_increase_countWhens)
      subgoal for head tail
        apply (simp only:list.case)
        apply (cases "applyInput env x14 head x15")
        apply (simp only:ApplyResult.case)
        apply (smt applyInput_decreases_countWhens applyInput_preserves_preserves_validAndPositive_state leI less_le_trans less_not_refl order.strict_trans reduceContractUntilQuiescent_doesnt_increase_countWhens reduceContractUntilQuiescent_preserves_validAndPositive_state)
        by simp
      done
    by simp
  done

lemma applyAllLoop_decreases_maxTransactions :
  "validAndPositive_state sta \<Longrightarrow>
   applyAllLoop reduced env sta cont inpList wa pa = ApplyAllSuccess newReduced nwa npa nsta ncont \<Longrightarrow>
   maxTransactions ncont nsta < maxTransactions cont sta \<or> (reduced = newReduced)"
  apply (induction reduced env sta cont inpList wa pa rule:applyAllLoop.induct)
  subgoal for reduced env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of reduced env state contract inputs warnings payments] list.case)
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for newReduced rwa rpa rsta rcon
      apply (simp only:ReduceResult.case)
      apply (cases inputs)
      using reductionLoop_reduces_maxTransactions apply fastforce
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
   applyAllInputs env fixedState cont inps = ApplyAllSuccess reduced nwarn npay nstate ncont \<Longrightarrow>
   reduced \<Longrightarrow> maxTransactions ncont nstate < maxTransactions cont fixedState"
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
    subgoal for newReduced nwarn npay nstate ncont
      apply (cases "\<not> newReduced \<and> (cont = Close \<longrightarrow> accounts sta = [])")
      apply (simp only:Let_def ApplyAllResult.case)
      apply (simp add:refl Let_def)
      apply (simp del:validAndPositive_state.simps fixInterval.simps applyAllInputs.simps maxTransactions.simps)
      by (metis TransactionOutputRecord.select_convs(3) TransactionOutputRecord.select_convs(4) applyAllInputs.simps applyAllInputsIsQuiescent applyAllLoop_doesnt_increase_countWhens computeTransaction_decreases_maxTransactions_aux fixInterval_preserves_maxTransactions fixInterval_preserves_preserves_validAndPositive_state isQuiescent.simps(1) le_neq_implies_less maxTransactions.simps not_less_eq not_less_iff_gr_or_eq)
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