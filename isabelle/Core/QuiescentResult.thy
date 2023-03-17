theory QuiescentResult
imports Semantics PositiveAccounts
begin

lemma reduceContractStepPayIsQuiescent :
      "(let moneyToPay = evalValue env sta x23
        in if moneyToPay \<le> 0 then Reduced (ReduceNonPositivePay x21 x22 tok moneyToPay) ReduceNoPayment sta x24
           else let balance = moneyInAccount x21 tok (accounts sta); paidMoney = min balance moneyToPay; newBalance = balance - paidMoney;
                    newAccs = updateMoneyInAccount x21 tok newBalance (accounts sta);
                    warning = if paidMoney < moneyToPay then ReducePartialPay x21 x22 tok paidMoney moneyToPay else ReduceNoWarning;
                    (payment, finalAccs) = giveMoney x21 x22 tok paidMoney newAccs
                in Reduced warning payment (sta\<lparr>accounts := finalAccs\<rparr>) x24) =
       NotReduced \<Longrightarrow> False"
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 tok (accounts sta)) (evalValue env sta x23) < (evalValue env sta x23)")
  apply (cases "lookup (x21, tok) (accounts sta)")
  apply simp
  apply (meson ReduceStepResult.distinct(1))
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 tok (accounts sta)) (evalValue env sta x23) < evalValue env sta x23")
  apply simp
  apply (meson ReduceStepResult.distinct(1))
  apply simp
  by (smt ReduceStepResult.distinct(1) case_prod_unfold)

lemma reduceOneIsSomeIfNotEmptyAndPositive : "accs \<noteq> [] \<Longrightarrow> allAccountsPositive accs \<Longrightarrow> refundOne accs \<noteq> None"
  by (metis allAccountsPositiveMeansFirstIsPositive option.distinct(1) refundOne.cases refundOne.simps(1))

lemma reduceContractStepIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                       reduceContractStep env sta cont = NotReduced \<Longrightarrow> isQuiescent cont sta"
  apply (cases cont)
  apply (simp only:reduceContractStep.simps)
  apply (cases "accounts sta")
  using reduceContractStepPayIsQuiescent apply fastforce
  apply (cases "refundOne (accounts sta)")
  apply (simp add: reduceOneIsSomeIfNotEmptyAndPositive)
  apply (simp add: case_prod_beta')
  apply (metis reduceContractStep.simps(2) reduceContractStepPayIsQuiescent)
  apply simp
  using isQuiescent.simps(2) apply blast
  apply (metis ReduceStepResult.distinct(1) reduceContractStep.simps(5))
  by simp

lemma reductionLoopIsQuiescent_aux :
  "(\<And>x11 x12 x13 x14 x xa.
     reduceContractStep env state contract = Reduced x11 x12 x13 x14 \<Longrightarrow>
     x = (if x11 = ReduceNoWarning then warnings else x11 # warnings) \<Longrightarrow>
     xa = (case x12 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) \<Longrightarrow>
     validAndPositive_state x13 \<Longrightarrow> reductionLoop True env x13 x14 x xa = ContractQuiescent newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta) \<Longrightarrow>
   validAndPositive_state state \<Longrightarrow> reductionLoop reduced env state contract warnings payments = ContractQuiescent newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (simp only:reductionLoop.simps [of reduced env state contract warnings payments])
  apply (cases "reduceContractStep env state contract")
  apply (metis (no_types, lifting) ReduceStepResult.simps(8) reduceContractStep_preserves_validAndPositive_state)
  apply (simp add: reduceContractStepIsQuiescent)
  by simp

lemma reductionLoopIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                  reductionLoop reduced env sta c wa ef = ContractQuiescent newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (induction reduced env sta c wa ef rule:reductionLoop.induct)
  using reductionLoopIsQuiescent_aux by blast

theorem reduceContractUntilQuiecentIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                                  reduceContractUntilQuiescent env sta c = ContractQuiescent newReduced wa ef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  by (simp only:reduceContractUntilQuiescent.simps reductionLoopIsQuiescent)

lemma applyAllInputsLoopIsQuiescent_base : "validAndPositive_state fixSta \<Longrightarrow>
                                            applyAllLoop reduced env fixSta cont [] wa ef = ApplyAllSuccess newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  by (simp_all del:reduceContractUntilQuiescent.simps validAndPositive_state.simps add:reduceContractUntilQuiecentIsQuiescent)

lemma applyAllInputsLoopIsQuiescent_loop : "(\<And>reduced env fixSta cont wa ef.
           validAndPositive_state fixSta \<Longrightarrow> applyAllLoop reduced env fixSta cont inps wa ef = ApplyAllSuccess newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta) \<Longrightarrow>
       validAndPositive_state fixSta \<Longrightarrow> applyAllLoop reduced env fixSta cont (a # inps) wa ef = ApplyAllSuccess newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  apply (unfold applyAllLoop.simps [of "reduced" "env" "fixSta"])
  apply (simp only:ReduceResult.case list.case)
  subgoal for x11 x12 x13 x14 x15
    apply (cases "applyInput env x14 a x15")
    apply (simp only:ApplyResult.case)
    apply (meson applyInput_preserves_preserves_validAndPositive_state reduceContractUntilQuiescent_preserves_validAndPositive_state)
    apply (simp only:ApplyResult.case)
    by blast
  by simp

lemma applyAllInputsLoopIsQuiescent : "validAndPositive_state fixSta \<Longrightarrow>
                                       applyAllLoop reduced env fixSta cont inps wa ef = ApplyAllSuccess newReduced nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (induction inps arbitrary:reduced env fixSta cont wa ef)
  apply (simp add: applyAllInputsLoopIsQuiescent_base)
  using applyAllInputsLoopIsQuiescent_loop by blast

lemma applyAllInputsIsQuiescent : "validAndPositive_state fixSta \<Longrightarrow>
                                   applyAllInputs env fixSta cont inps = ApplyAllSuccess reduced warnings payments newState newCont \<Longrightarrow> isQuiescent newCont newState"
  by (simp add: applyAllInputsLoopIsQuiescent)

lemma computeTransactionIsQuiescent_aux : "validAndPositive_state sta \<Longrightarrow>
                                           computeTransaction (Transaction \<lparr>interval = interva, inputs = inps\<rparr>) sta cont
                                             = TransactionOutput \<lparr> txOutWarnings = nwa,
                                                                   txOutPayments = nef,
                                                                   txOutState = nsta,
                                                                   txOutContract = ncont\<rparr> \<Longrightarrow>
       fixInterval (interval (Transaction \<lparr>interval = interva, inputs = inps\<rparr>)) sta = IntervalTrimmed x11 x12
       \<Longrightarrow> isQuiescent ncont nsta"
  apply (simp only:computeTransaction.simps)
  by (smt ApplyAllResult.exhaust ApplyAllResult.simps(10) ApplyAllResult.simps(8) ApplyAllResult.simps(9) IntervalResult.simps(5) TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps applyAllInputsLoopIsQuiescent fixInterval_preserves_preserves_validAndPositive_state)

theorem computeTransactionIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                         computeTransaction traIn sta cont = TransactionOutput traOut \<Longrightarrow>
                                         isQuiescent (txOutContract traOut) (txOutState traOut)"

  apply (cases "traIn")
  apply (cases "traOut")
  by (smt IntervalResult.exhaust IntervalResult.simps(6) Transaction.update_convs(3) TransactionOutput.distinct(1) TransactionOutputRecord.surjective computeTransaction.simps computeTransactionIsQuiescent_aux old.unit.exhaust)

lemma playTraceAuxIsQuiescent : "validAndPositive_state (txOutState traIn) \<Longrightarrow>
                                 (l \<noteq> Nil \<or> isQuiescent (txOutContract traIn) (txOutState traIn)) \<Longrightarrow>
                                 playTraceAux traIn l = TransactionOutput traOut \<Longrightarrow>
                                 isQuiescent (txOutContract traOut) (txOutState traOut)"
  apply (induction traIn l arbitrary:traOut rule:playTraceAux.induct)
  apply simp
  apply (simp del:validAndPositive_state.simps isQuiescent.simps computeTransaction.simps)
  subgoal for warnings payments state cont h t traOut
    apply (cases "computeTransaction h state cont")
    apply (simp del:validAndPositive_state.simps isQuiescent.simps computeTransaction.simps)
    using computeTransactionIsQuiescent computeTransaction_preserves_validAndPositive_state by simp_all
  done

theorem playTraceIsQuiescent : "playTrace sl cont (Cons h t) = TransactionOutput traOut \<Longrightarrow>
                                isQuiescent (txOutContract traOut) (txOutState traOut)"
  by (metis TransactionOutputRecord.select_convs(3) list.discI playTrace.simps playTraceAuxIsQuiescent validAndPositive_initial_state)


lemma reductionLoop_reduce_monotonic : "reductionLoop True env sta cont wa ef = ContractQuiescent reduce nwa nef newState newCont \<Longrightarrow> reduce"
  apply (induction True env sta cont wa ef arbitrary:reduce nwa nef newState newCont rule:reductionLoop.induct)
  subgoal for env state contract warnings payments reduce nwa nef newState newCont
    apply (cases "reduceContractStep env state contract")
    apply (simp only:ReduceStepResult.case)
    subgoal premises fact for x11 x12 x13 x14
      apply (rule fact(1)[of x11 x12 x13 x14 "(if x11 = ReduceNoWarning then warnings else x11 # warnings)" "(case x12 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments)" reduce nwa nef newState newCont])
      apply simp
      apply simp
      apply simp
      by (metis (lifting) ReduceStepResult.simps(8) fact(2) fact(3) reductionLoop.elims)
     apply simp
    by simp
  done

text "If we reduce the contract and the continuation has changed, then the reduced flag should be true"
theorem reduceContractUntilQuiescent_ifDifferentReduced : "reduceContractUntilQuiescent si sta cont = ContractQuiescent reduce wa ef sta newCont \<Longrightarrow> cont \<noteq> newCont \<Longrightarrow> reduce"
  apply (simp only:reduceContractUntilQuiescent.simps)
  apply (simp only:reductionLoop.simps)
  apply (cases "reduceContractStep si sta cont")
  apply (simp only:ReduceStepResult.case Let_def)
  using reductionLoop_reduce_monotonic apply blast
   apply simp
  by auto


end
