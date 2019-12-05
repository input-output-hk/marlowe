theory Timeout
imports Semantics PositiveAccounts QuiescentResult
begin

fun isClosedAndEmpty :: "TransactionOutput \<Rightarrow> bool" where
"isClosedAndEmpty (TransactionOutput txOut) = (txOutContract txOut = Close
                                               \<and> accounts (txOutState txOut) = [])" |
"isClosedAndEmpty _ = False"

lemma max_of_ge : "ia \<le> i \<Longrightarrow> max (i::int) ia = i"
  by linarith

lemma reduceStepClose_is_Close : "reduceContractStep env sta Close = Reduced re wa nsta ncon \<Longrightarrow> ncon = Close"
  apply simp
  apply (cases "refundOne (accounts sta)")
  apply simp
  subgoal for a
    apply (cases "a")
    subgoal for aa b
      apply (cases "aa")
      by simp
    done
  done

lemma reductionLoopClose_is_Close : "reductionLoop env sta Close x y = ContractQuiescent re wa nsta ncon \<Longrightarrow> ncon = Close"
  apply (induction env sta Close x y rule:reductionLoop.induct)
  subgoal for env state warnings payments
    apply (simp only:reductionLoop.simps)
    apply (cases "reduceContractStep env state Close")
    subgoal for x11 x12 x13 x14
      apply (simp del:reductionLoop.simps reduceContractStep.simps add:reduceStepClose_is_Close)
      using reduceStepClose_is_Close by fastforce
    apply (simp del:reduceContractStep.simps)
    apply (simp del:reduceContractStep.simps)
    done
  done

lemma reduceClose_is_Close : "reduceContractUntilQuiescent env sta Close = ContractQuiescent re wa nsta ncon \<Longrightarrow> ncon = Close"
  apply (simp del:reductionLoop.simps)
  using reductionLoopClose_is_Close by blast

lemma timedOutReduce_only_quiescent_in_close_When :
  "minSlot sta \<le> iniSlot \<Longrightarrow>
   maxTimeContract (When x41 x42 x43) \<le> iniSlot \<Longrightarrow>
   iniSlot \<le> endSlot \<Longrightarrow>
   reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> (sta\<lparr>minSlot := iniSlot\<rparr>) (When x41 x42 x43) \<noteq> NotReduced"
  apply (induction x41)
  by simp_all

lemma maxTimeWhen : "maxTimeContract (When x41 x42 x43) \<le> iniSlot \<Longrightarrow> x42 \<le> iniSlot"
  apply (induction x41 arbitrary:x42 x43 iniSlot)
  by auto

lemma maxTimeNotAmbiguous_reduceStep :
   "maxTimeContract cont \<le> iniSlot \<Longrightarrow>
    iniSlot \<le> endSlot \<Longrightarrow>
    reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> state cont \<noteq> AmbiguousSlotIntervalReductionError"
  apply (cases cont)
  apply simp
  apply (auto split:option.split bool.split)
  subgoal for x21 x22 x23 x24 x25
    apply (cases "let moneyToPay = evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> state x24 in moneyToPay \<le> 0")
    apply simp
    apply simp
    apply (cases "let moneyToPay = evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> state x24;
                      balance = case lookup (x21, x23) (accounts state) of None \<Rightarrow> 0 | Some x \<Rightarrow> x; paidMoney = min balance moneyToPay
                  in giveMoney x22 x23 paidMoney (if balance \<le> moneyToPay then MList.delete (x21, x23) (accounts state)
                                                  else MList.insert (x21, x23) (balance - paidMoney) (accounts state))")
    by (metis ReduceStepResult.distinct(3) case_prod_conv)
  using maxTimeWhen apply blast
  by (meson ReduceStepResult.distinct(3))

lemma maxTimeOnlyDecreases_reduceStepWhen :
  "reduceContractStep inte state (When x41 x42 x43) = Reduced wa ef nstate ncont \<Longrightarrow>
   maxTimeContract ncont \<le> maxTimeContract (When x41 x42 x43)"
  apply (induction x41 arbitrary: inte state x42 x43 wa ef nstate ncont)
  apply (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject maxTimeContract.simps(4) prod.case_eq_if reduceContractStep.simps(4))
  by fastforce

lemma maxTimeOnlyDecreases_reduceStep :
  "reduceContractStep inte state cont = Reduced wa ef nstate ncont \<Longrightarrow>
   maxTimeContract ncont \<le> maxTimeContract cont"
  apply (cases cont)
  using reduceStepClose_is_Close apply blast
  apply (simp only:reduceContractStep.simps)
  subgoal for x21 x22 x23 x24 x25
    apply (cases "let moneyToPay = evalValue inte state x24
                  in evalValue inte state x24 \<le> 0")
    apply simp
    apply simp
    apply (cases "let moneyToPay = evalValue inte state x24; balance = case lookup (x21, x23) (accounts state) of None \<Rightarrow> 0 | Some x \<Rightarrow> x;
                      paidMoney = min balance moneyToPay
                  in giveMoney x22 x23 paidMoney
                               (if balance \<le> moneyToPay then MList.delete (x21, x23) (accounts state)
                                else MList.insert (x21, x23) (balance - paidMoney) (accounts state))")
    by (metis ReduceStepResult.inject case_prod_conv eq_iff)
    apply auto[1]
  apply (simp add: maxTimeOnlyDecreases_reduceStepWhen)
  by (metis ReduceStepResult.inject eq_iff maxTimeContract.simps(6) reduceContractStep.simps(5))

lemma maxTimeNotAmbiguous_reduceLoop : "maxTimeContract cont \<le> iniSlot \<Longrightarrow>
    iniSlot \<le> endSlot \<Longrightarrow>
    reductionLoop \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta cont x y \<noteq> RRAmbiguousSlotIntervalError"
  apply (induction "\<lparr>slotInterval = (iniSlot, endSlot)\<rparr>" sta cont x y rule:reductionLoop.induct)
  subgoal premises facts for state contract warnings payments
    apply (cases "reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> state contract")
      apply (simp only:reductionLoop.simps ReduceStepResult.case)
      apply (simp only:Let_def)
      using facts(1) facts(2) facts(3) maxTimeOnlyDecreases_reduceStep apply fastforce
      apply auto[1]
      by (simp add: facts(2) facts(3) maxTimeNotAmbiguous_reduceStep)
    done

lemma maxTimeNotAmbiguous : "maxTimeContract cont \<le> iniSlot \<Longrightarrow>
       iniSlot \<le> endSlot \<Longrightarrow>
       reduceContractUntilQuiescent \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> (sta\<lparr>minSlot := iniSlot\<rparr>) cont \<noteq> RRAmbiguousSlotIntervalError"
  using maxTimeNotAmbiguous_reduceLoop by auto


lemma timedOutReduce_only_quiescent_in_close :
  "minSlot sta \<le> iniSlot \<Longrightarrow>
   maxTimeContract c \<le> iniSlot \<Longrightarrow>
   iniSlot \<le> endSlot \<Longrightarrow>
   reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> (sta\<lparr>minSlot := iniSlot\<rparr>) c = NotReduced \<Longrightarrow> c = Close"
  apply (cases c)
  apply blast
  apply (metis reduceContractStep.simps(2) reduceContractStepPayIsQuiescent)
  apply simp
  using timedOutReduce_only_quiescent_in_close_When apply blast
  by (metis ReduceStepResult.distinct(1) reduceContractStep.simps(5))

lemma timedOutReduceStep_does_not_modify_minSlot :
  "minSlot sta = iniSlot \<Longrightarrow>
   reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta contract =
   Reduced warning effect newState ncontract \<Longrightarrow> minSlot newState = iniSlot"
  apply (cases contract)
    apply simp
    apply (cases "refundOne (accounts sta)")
      apply simp
      subgoal for a
        apply (cases a)
        subgoal for aa
          apply (cases aa)
          by auto
        done
      subgoal for x21 x22 x23 x24
      apply (cases "let moneyToPay = evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta x24
                    in moneyToPay \<le> 0")
      apply auto[1]
      apply simp
      apply (cases "giveMoney x22 x23
           (min (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
             (evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta x24))
           (if (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
               \<le> evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta x24
            then MList.delete (x21, x23) (accounts sta)
            else MList.insert (x21, x23)
                  ((case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x) -
                   min (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
                    (evalValue \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta x24))
                  (accounts sta))")
      by (auto simp:Let_def)
      apply auto[1]
    apply (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject State.ext_inject State.surjective State.update_convs(4) prod.case_eq_if reduceContractStep.simps(4))
    by (smt ReduceStepResult.inject State.ext_inject State.surjective State.update_convs(3) State.update_convs(4) reduceContractStep.simps(5))

lemma timedOutReduceContractLoop_closes_contract : "minSlot sta \<le> iniSlot \<Longrightarrow>
    maxTimeContract cont \<le> iniSlot \<Longrightarrow>
    iniSlot \<le> endSlot \<Longrightarrow>
    minSlot sta = iniSlot \<Longrightarrow>
    reductionLoop \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> sta cont x y =
    ContractQuiescent warning effect newState ncontract \<Longrightarrow>
    ncontract = Close"
  apply (induction "\<lparr>slotInterval = (iniSlot, endSlot)\<rparr>" sta cont x y arbitrary: warning effect newState ncontract rule:reductionLoop.induct)
  subgoal for state contract warnings payments warning effect newState ncontract
    apply (simp only:reductionLoop.simps[of "\<lparr>slotInterval = (iniSlot, endSlot)\<rparr>" "(sta\<lparr>minSlot := iniSlot\<rparr>)" contract warnings payments])
    apply (cases "reduceContractStep \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> state contract")
    subgoal for x11 x12 x13 x14
      apply (simp only:ReduceStepResult.case Let_def)
      subgoal premises facts
        apply (rule facts(1)[of x11 x12 x13 x14 "(if x11 = ReduceNoWarning then warnings else x11 # warnings)"
                                "(case x12 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments)"
                                warning effect newState ncontract])
        apply simp
        apply simp
        apply simp
        apply simp
        using facts(3) facts(7) maxTimeOnlyDecreases_reduceStep apply fastforce
        apply simp
        using facts(5) facts(7) timedOutReduceStep_does_not_modify_minSlot apply blast
        by (metis (no_types, lifting) ReduceStepResult.simps(8) facts(6) facts(7) reductionLoop.simps)
      done
    using timedOutReduce_only_quiescent_in_close apply fastforce
    using maxTimeNotAmbiguous_reduceStep by blast
  done

lemma timedOutReduceContractUntilQuiescent_closes_contract :
  "iniSlot \<ge> minSlot sta
   \<Longrightarrow> iniSlot \<ge> maxTimeContract cont
   \<Longrightarrow> endSlot \<ge> iniSlot
   \<Longrightarrow> reduceContractUntilQuiescent \<lparr>slotInterval = (max iniSlot (minSlot sta), endSlot)\<rparr> (sta\<lparr>minSlot := max iniSlot (minSlot sta)\<rparr>) cont
   = ContractQuiescent warning effect newState ncontract \<Longrightarrow> ncontract = Close"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (smt State.select_convs(4) State.surjective State.update_convs(4) timedOutReduceContractLoop_closes_contract)

lemma timedOutReduceContractStep_empties_accounts :
  "validAndPositive_state sta \<Longrightarrow>
    minSlot sta \<le> iniSlot \<Longrightarrow>
    maxTimeContract cont \<le> iniSlot \<Longrightarrow>
    iniSlot \<le> endSlot \<Longrightarrow>
    reduceContractUntilQuiescent \<lparr>slotInterval = (iniSlot, endSlot)\<rparr> (sta\<lparr>minSlot := iniSlot\<rparr>) cont
     = ContractQuiescent warning effect newState ncontract \<Longrightarrow> accounts newState = []"
  by (smt State.ext_inject State.surjective State.update_convs(4) allAccountsPositiveState.elims(3) isQuiescent.simps(1) positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive reduceContractUntilQuiecentIsQuiescent reduceContractUntilQuiescent.simps timedOutReduceContractLoop_closes_contract validAndPositiveImpliesPositive validAndPositiveImpliesValid validAndPositive_state.elims(3) valid_state.simps)

theorem timedOutTransaction_closes_contract :
  "validAndPositive_state sta
   \<Longrightarrow> iniSlot \<ge> minSlot sta
   \<Longrightarrow> iniSlot \<ge> maxTimeContract cont
   \<Longrightarrow> endSlot \<ge> iniSlot
   \<Longrightarrow> accounts sta \<noteq> []
   \<Longrightarrow> isClosedAndEmpty (computeTransaction \<lparr> interval = (iniSlot, endSlot)
                                            , inputs = [] \<rparr> sta cont)"
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps add:Let_def)
  apply (cases "reduceContractUntilQuiescent \<lparr>slotInterval = (max iniSlot (minSlot sta), endSlot)\<rparr> (sta\<lparr>minSlot := max iniSlot (minSlot sta)\<rparr>) cont")
  apply (simp only:ReduceResult.case list.case ApplyAllResult.case max_of_ge)
  apply (cases "cont = Close")
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  apply (metis maxTimeContract.simps(1) reduceContractUntilQuiescent.simps reductionLoopClose_is_Close timedOutReduceContractStep_empties_accounts)
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  apply (metis max.orderE timedOutReduceContractStep_empties_accounts timedOutReduceContractUntilQuiescent_closes_contract)
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  using maxTimeNotAmbiguous by auto

theorem timeOutTransaction_closes_contract2 :
  "validAndPositive_state sta
   \<Longrightarrow> accounts sta \<noteq> []
   \<Longrightarrow> \<exists> inp . isClosedAndEmpty (computeTransaction inp sta cont)"
  by (meson not_less not_less_iff_gr_or_eq timedOutTransaction_closes_contract)

end
