theory QuiescentResult
imports Semantics PositiveAccounts
begin

lemma reduceContractStepPayIsQuiescent :
      "(let moneyToPay = evalValue env sta x23
        in if moneyToPay \<le> 0 then Reduced (ReduceNonPositivePay x21 x22 moneyToPay) ReduceNoPayment sta x24
           else let balance = moneyInAccount x21 (accounts sta); paidMoney = min balance moneyToPay; newBalance = balance - paidMoney;
                    newAccs = updateMoneyInAccount x21 newBalance (accounts sta);
                    warning = if paidMoney < moneyToPay then ReducePartialPay x21 x22 paidMoney moneyToPay else ReduceNoWarning;
                    (payment, finalAccs) = giveMoney x22 paidMoney newAccs
                in Reduced warning payment (sta\<lparr>accounts := finalAccs\<rparr>) x24) =
       NotReduced \<Longrightarrow>
       cont = Pay x21 x22 x23 x24 \<Longrightarrow> False"
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 (accounts sta)) (evalValue env sta x23) < (evalValue env sta x23)")
  apply (cases "lookup x21 (accounts sta)")
  apply simp
  apply (metis (mono_tags, lifting) ReduceStepResult.distinct(1) case_prod_unfold)
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 (accounts sta)) (evalValue env sta x23) < evalValue env sta x23")
  apply simp
  apply (metis (no_types, lifting) ReduceStepResult.distinct(1) case_prod_unfold)
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
  using reduceContractStepPayIsQuiescent apply fastforce
  apply simp
  using isQuiescent.simps(2) apply blast
  by (metis ReduceStepResult.distinct(1) reduceContractStep.simps(5))

lemma reductionLoopIsQuiescent_aux :
  "(\<And>x11 x12 x13 x14 x xa.
     reduceContractStep env state contract = Reduced x11 x12 x13 x14 \<Longrightarrow>
     x = (if x11 = ReduceNoWarning then warnings else x11 # warnings) \<Longrightarrow>
     xa = (case x12 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) \<Longrightarrow>
     validAndPositive_state x13 \<Longrightarrow> reductionLoop env x13 x14 x xa = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta) \<Longrightarrow>
   validAndPositive_state state \<Longrightarrow> reductionLoop env state contract warnings payments = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (simp only:reductionLoop.simps [of env state contract warnings payments])
  apply (cases "reduceContractStep env state contract")
  apply (metis (no_types, lifting) ReduceStepResult.simps(8) reduceContractStep_preserves_validAndPositive_state)
  apply (simp add: reduceContractStepIsQuiescent)
  by simp

lemma reductionLoopIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                  reductionLoop env sta c wa ef = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (induction env sta c wa ef rule:reductionLoop.induct)
  using reductionLoopIsQuiescent_aux by blast

theorem reduceContractUntilQuiecentIsQuiescent : "validAndPositive_state sta \<Longrightarrow>
                                                  reduceContractUntilQuiescent env sta c = ContractQuiescent wa ef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  by (simp only:reduceContractUntilQuiescent.simps reductionLoopIsQuiescent)

lemma applyAllInputsLoopIsQuiescent_base : "validAndPositive_state fixSta \<Longrightarrow>
                                            applyAllLoop env fixSta cont [] wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  by (simp_all del:reduceContractUntilQuiescent.simps validAndPositive_state.simps add:reduceContractUntilQuiecentIsQuiescent)

lemma applyAllInputsLoopIsQuiescent_loop : "(\<And>env fixSta cont wa ef.
           validAndPositive_state fixSta \<Longrightarrow> applyAllLoop env fixSta cont inps wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta) \<Longrightarrow>
       validAndPositive_state fixSta \<Longrightarrow> applyAllLoop env fixSta cont (a # inps) wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  apply (unfold applyAllLoop.simps [of "env" "fixSta"])
  apply (simp only:ReduceResult.case list.case)
  apply (metis (mono_tags, lifting) ApplyAllResult.distinct(1) ApplyResult.exhaust ApplyResult.simps(4) ApplyResult.simps(5) applyInput_preserves_preserves_validAndPositive_state reduceContractUntilQuiescent_preserves_validAndPositive_state)
  by simp

lemma applyAllInputsLoopIsQuiescent : "validAndPositive_state fixSta \<Longrightarrow>
                                       applyAllLoop env fixSta cont inps wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon nsta"
  apply (induction inps arbitrary:env fixSta cont wa ef)
  apply (simp add: applyAllInputsLoopIsQuiescent_base)
  using applyAllInputsLoopIsQuiescent_loop by blast

lemma applyAllInputsIsQuiescent : "validAndPositive_state fixSta \<Longrightarrow>
                                   applyAllInputs env fixSta cont inps = ApplyAllSuccess warnings payments newState newCont \<Longrightarrow> isQuiescent newCont newState"
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

end