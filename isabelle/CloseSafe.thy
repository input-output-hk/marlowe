theory CloseSafe
imports Semantics
begin

lemma closeIdemp_reduceContractStep : "reduceContractStep env fixSta Close = Reduced wa ef sta cont \<Longrightarrow> cont = Close"
  by (auto split:option.splits)

lemma closeIdemp_reductionLoop : "reductionLoop reducedBefore env fixSta Close wa ef = ContractQuiescent reducedAfter reduceWarns pays curState cont \<Longrightarrow> cont = Close"
  apply (induction reducedBefore env fixSta Close wa ef rule:reductionLoop.induct)
  subgoal for reducedBefore env state warnings payments
    apply (simp only:reductionLoop.simps[of reducedBefore env state Close warnings payments])
    apply (auto split:ReduceStepResult.splits simp del:reductionLoop.simps reduceContractStep.simps)
    using closeIdemp_reduceContractStep by blast
  done

lemma closeIdemp_reduceContractUntilQuiescent : "reduceContractUntilQuiescent env fixSta Close = ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow> cont = Close"
  apply (simp only:reduceContractUntilQuiescent.simps)
  using closeIdemp_reductionLoop by blast

lemma closeIsSafe_reduceContractStep : "reduceContractStep env fixSta Close = Reduced wa ef sta cont \<Longrightarrow> wa = ReduceNoWarning"
  by (auto split:option.splits)
                                         
lemma closeIsSafe_reductionLoop : "wa = [] \<Longrightarrow> reductionLoop reducedBefore env fixSta Close wa ef = ContractQuiescent reducedAfter reduceWarns pays curState cont \<Longrightarrow> reduceWarns = []"
  apply (induction reducedBefore env fixSta Close wa ef rule:reductionLoop.induct)
  subgoal for reducedBefore env state warnings payments
    apply (simp only:reductionLoop.simps[of reducedBefore env state Close warnings payments])
    apply (simp only:reductionLoop.simps[of reducedBefore env state Close "[]" payments])
    apply (auto split:ReduceStepResult.splits simp del:reductionLoop.simps reduceContractStep.simps)
    using closeIdemp_reduceContractStep closeIsSafe_reduceContractStep by fastforce
  done

lemma closeIsSafe_reduceContractUntilQuiescent : "reduceContractUntilQuiescent env fixSta Close = ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow> reduceWarns = []"
  by (simp add: closeIsSafe_reductionLoop)

lemma closeIsSafe_applyInput : "applyInput env curState head Close = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning"
  by simp  

lemma closeIsSafe_applyAllInputs : "applyAllInputs env fixSta Close inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow> warnings = []"
  apply (auto split:ReduceResult.splits
              simp del:applyAllLoop.simps reduceContractUntilQuiescent.simps
              simp add:applyAllLoop.simps [of "False" env fixSta Close inps "[]" "[]"])
  subgoal for reduced reduceWarns pays curState cont
    apply (auto split:list.splits simp del:reduceContractUntilQuiescent.simps applyAllLoop.simps)
    apply (subst closeIsSafe_reduceContractUntilQuiescent[of env fixSta reduced reduceWarns pays newState cont])
    apply simp
    apply simp
    using closeIsSafe_reduceContractUntilQuiescent convertReduceWarnings.simps(1) apply blast
    using closeIdemp_reduceContractUntilQuiescent by force
  done

theorem closeIsSafe : "computeTransaction tra sta Close = TransactionOutput trec \<Longrightarrow> txOutWarnings trec = []"
  apply (simp only:computeTransaction.simps)
  apply (auto split:IntervalResult.splits option.splits ApplyAllResult.splits
              simp del:applyAllLoop.simps simp add:closeIsSafe_applyAllInputs)
  subgoal for env fixSta warnings payments newState cont
    apply (cases "\<not> warnings \<and> accounts sta = []")
    by (auto simp del:applyAllLoop.simps simp add:closeIsSafe_applyAllInputs)
  done

end