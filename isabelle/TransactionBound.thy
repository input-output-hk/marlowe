theory TransactionBound
  imports Main Semantics PositiveAccounts QuiescentResult ValidState
begin

fun countWhensCaseList :: "Case list \<Rightarrow> nat"
and countWhens :: "Contract \<Rightarrow> nat" where
"countWhensCaseList (Cons (Case _ c) tail) = max (countWhens c) (countWhensCaseList tail)" |
"countWhensCaseList Nil = 0" |
"countWhens Close = 0" |
"countWhens (Pay _ _ _ c) = countWhens c" |
"countWhens (If _ c c2) = max (countWhens c) (countWhens c2)" |
"countWhens (When cl t c) = Suc (max (countWhensCaseList cl) (countWhens c))" |
"countWhens (Contract.Let _ _ c) = countWhens c"

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
  subgoal for env state accId payee val cont
    apply (cases "evalValue env state val \<le> 0")
    apply simp
    apply simp
    apply (cases "let moneyToPay = evalValue env state val;
                      balance = case lookup accId (accounts state) of None \<Rightarrow> 0 | Some x \<Rightarrow> x;
                      paidMoney = min balance moneyToPay
                  in giveMoney payee paidMoney (if balance \<le> moneyToPay
                                                then MList.delete accId (accounts state)
                                                else MList.insert accId (balance - paidMoney) (accounts state))")
    apply (simp add:Let_def)
  done
  by (metis ReduceStepResult.inject le_eq_less_or_eq)

lemma reduceContractStep_doesnt_increase_maxTransactions : "reduceContractStep env st c = Reduced wa ef nst nc \<Longrightarrow>
                                                            maxTransactions nc nst \<le> maxTransactions c st"
  using reduceContractStep_not_quiescent_reduces reduceContractStep_quiescent_reduces by fastforce


lemma reductionLoop_doesnt_increase_maxTransactions : "validAndPositive_state st \<Longrightarrow>
                                                       reductionLoop env st c wa ef = ContractQuiescent nwa nef nst nc \<Longrightarrow>
                                                       maxTransactions nc nst \<le> maxTransactions c st"
  apply (induction env st c wa ef rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (subst (asm) reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.simps)
      by (metis dual_order.trans reduceContractStep_doesnt_increase_maxTransactions reduceContractStep_preserves_validAndPositive_state)
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



end