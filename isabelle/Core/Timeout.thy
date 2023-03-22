theory Timeout
imports Semantics PositiveAccounts QuiescentResult AssetsPreservation
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

lemma reductionLoopClose_is_Close : "reductionLoop reduced env sta Close x y = ContractQuiescent newReduced re wa nsta ncon \<Longrightarrow> ncon = Close"
  apply (induction reduced env sta Close x y rule:reductionLoop.induct)
  subgoal for reduced env state warnings payments
    apply (simp only:reductionLoop.simps)
    apply (cases "reduceContractStep env state Close")
    subgoal for x11 x12 x13 x14
      apply (simp del:reductionLoop.simps reduceContractStep.simps add:reduceStepClose_is_Close)
      using reduceStepClose_is_Close by fastforce
    apply (simp del:reduceContractStep.simps)
    apply (simp del:reduceContractStep.simps)
    done
  done

lemma reduceClose_is_Close : "reduceContractUntilQuiescent env sta Close = ContractQuiescent reduced re wa nsta ncon \<Longrightarrow> ncon = Close"
  apply (simp del:reductionLoop.simps)
  using reductionLoopClose_is_Close by blast

lemma timedOutReduce_only_quiescent_in_close_When :
  "minTime sta \<le> iniTime \<Longrightarrow>
   maxTimeContract (When x41 x42 x43) \<le> iniTime \<Longrightarrow>
   iniTime \<le> endTime \<Longrightarrow>
   reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> (sta\<lparr>minTime := iniTime\<rparr>) (When x41 x42 x43) \<noteq> NotReduced"
  apply (induction x41)
  by simp_all

lemma maxTimeWhen : "maxTimeContract (When x41 x42 x43) \<le> iniTime \<Longrightarrow> x42 \<le> iniTime"
  apply (induction x41 arbitrary:x42 x43 iniTime)
  by auto

lemma maxTimeNotAmbiguous_reduceStep :
   "maxTimeContract cont \<le> iniTime \<Longrightarrow>
    iniTime \<le> endTime \<Longrightarrow>
    reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> state cont \<noteq> AmbiguousTimeIntervalReductionError"
  apply (cases cont)
  apply simp
  apply (auto split:option.split bool.split)
  subgoal for x21 x22 x23 x24 x25
    apply (cases "let moneyToPay = evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> state x24 in moneyToPay \<le> 0")
    apply simp
    apply simp
    apply (cases "let moneyToPay = evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> state x24;
                      balance = case lookup (x21, x23) (accounts state) of None \<Rightarrow> 0 | Some x \<Rightarrow> x; paidMoney = min balance moneyToPay
                  in giveMoney x21 x22 x23 paidMoney (if balance \<le> moneyToPay then MList.delete (x21, x23) (accounts state)
                                                      else MList.insert (x21, x23) (balance - paidMoney) (accounts state))")
    by (meson ReduceStepResult.distinct(3))
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
                  in giveMoney x21 x22 x23 paidMoney
                               (if balance \<le> moneyToPay then MList.delete (x21, x23) (accounts state)
                                else MList.insert (x21, x23) (balance - paidMoney) (accounts state))")
    by (metis ReduceStepResult.inject eq_iff)
    apply auto[1]
  apply (simp add: maxTimeOnlyDecreases_reduceStepWhen)
  apply (metis ReduceStepResult.inject eq_iff maxTimeContract.simps(6) reduceContractStep.simps(5))
  by simp

lemma maxTimeNotAmbiguous_reduceLoop : "maxTimeContract cont \<le> iniTime \<Longrightarrow>
    iniTime \<le> endTime \<Longrightarrow>
    reductionLoop reduced \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta cont x y \<noteq> RRAmbiguousTimeIntervalError"
  apply (induction reduced "\<lparr>timeInterval = (iniTime, endTime)\<rparr>" sta cont x y rule:reductionLoop.induct)
  subgoal premises facts for reduced state contract warnings payments
    apply (cases "reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> state contract")
      apply (simp only:reductionLoop.simps ReduceStepResult.case)
      apply (simp only:Let_def)
      using facts(1) facts(2) facts(3) maxTimeOnlyDecreases_reduceStep apply fastforce
      apply auto[1]
      by (simp add: facts(2) facts(3) maxTimeNotAmbiguous_reduceStep)
    done

lemma maxTimeNotAmbiguous : "maxTimeContract cont \<le> iniTime \<Longrightarrow>
       iniTime \<le> endTime \<Longrightarrow>
       reduceContractUntilQuiescent \<lparr>timeInterval = (iniTime, endTime)\<rparr> (sta\<lparr>minTime := iniTime\<rparr>) cont \<noteq> RRAmbiguousTimeIntervalError"
  using maxTimeNotAmbiguous_reduceLoop by auto


lemma timedOutReduce_only_quiescent_in_close :
  "minTime sta \<le> iniTime \<Longrightarrow>
   maxTimeContract c \<le> iniTime \<Longrightarrow>
   iniTime \<le> endTime \<Longrightarrow>
   reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> (sta\<lparr>minTime := iniTime\<rparr>) c = NotReduced \<Longrightarrow> c = Close"
  apply (cases c)
  apply blast
  apply (metis reduceContractStep.simps(2) reduceContractStepPayIsQuiescent)
  apply simp
  using timedOutReduce_only_quiescent_in_close_When apply blast
  apply (metis ReduceStepResult.distinct(1) reduceContractStep.simps(5))
  by simp

lemma timedOutReduceStep_does_not_modify_minTime :
  "minTime sta = iniTime \<Longrightarrow>
   reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta contract =
   Reduced warning effect newState ncontract \<Longrightarrow> minTime newState = iniTime"
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
      apply (cases "let moneyToPay = evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta x24
                    in moneyToPay \<le> 0")
      apply auto[1]
      apply simp
      apply (cases "giveMoney x21 x22 x23
           (min (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
             (evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta x24))
           (if (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
               \<le> evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta x24
            then MList.delete (x21, x23) (accounts sta)
            else MList.insert (x21, x23)
                  ((case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x) -
                   min (case lookup (x21, x23) (accounts sta) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)
                    (evalValue \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta x24))
                  (accounts sta))")
      by (auto simp:Let_def)
      apply auto[1]
    apply (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject State.ext_inject State.surjective State.update_convs(4) prod.case_eq_if reduceContractStep.simps(4))
    apply (smt ReduceStepResult.inject State.ext_inject State.surjective State.update_convs(3) State.update_convs(4) reduceContractStep.simps(5))
    by simp

lemma timedOutReduceContractLoop_closes_contract : "minTime sta \<le> iniTime \<Longrightarrow>
    maxTimeContract cont \<le> iniTime \<Longrightarrow>
    iniTime \<le> endTime \<Longrightarrow>
    minTime sta = iniTime \<Longrightarrow>
    reductionLoop reduced \<lparr>timeInterval = (iniTime, endTime)\<rparr> sta cont x y =
    ContractQuiescent newReduced warning effect newState ncontract \<Longrightarrow>
    ncontract = Close"
  apply (induction reduced "\<lparr>timeInterval = (iniTime, endTime)\<rparr>" sta cont x y arbitrary: warning effect newState ncontract rule:reductionLoop.induct)
  subgoal for reduced state contract warnings payments warning effect newState ncontract
    apply (simp only:reductionLoop.simps[of reduced "\<lparr>timeInterval = (iniTime, endTime)\<rparr>" "(sta\<lparr>minTime := iniTime\<rparr>)" contract warnings payments])
    apply (cases "reduceContractStep \<lparr>timeInterval = (iniTime, endTime)\<rparr> state contract")
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
        using facts(5) facts(7) timedOutReduceStep_does_not_modify_minTime apply blast
        by (metis (no_types, lifting) ReduceStepResult.simps(8) facts(6) facts(7) reductionLoop.simps)
      done
    using timedOutReduce_only_quiescent_in_close apply fastforce
    using maxTimeNotAmbiguous_reduceStep by blast
  done

lemma timedOutReduceContractUntilQuiescent_closes_contract :
  "iniTime \<ge> minTime sta
   \<Longrightarrow> iniTime \<ge> maxTimeContract cont
   \<Longrightarrow> endTime \<ge> iniTime
   \<Longrightarrow> reduceContractUntilQuiescent \<lparr>timeInterval = (max iniTime (minTime sta), endTime)\<rparr> (sta\<lparr>minTime := max iniTime (minTime sta)\<rparr>) cont
   = ContractQuiescent reduced warning effect newState ncontract \<Longrightarrow> ncontract = Close"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (smt State.select_convs(4) State.surjective State.update_convs(4) timedOutReduceContractLoop_closes_contract)

lemma timedOutReduceContractStep_empties_accounts :
  "validAndPositive_state sta \<Longrightarrow>
    minTime sta \<le> iniTime \<Longrightarrow>
    maxTimeContract cont \<le> iniTime \<Longrightarrow>
    iniTime \<le> endTime \<Longrightarrow>
    reduceContractUntilQuiescent \<lparr>timeInterval = (iniTime, endTime)\<rparr> (sta\<lparr>minTime := iniTime\<rparr>) cont
     = ContractQuiescent reduced warning effect newState ncontract \<Longrightarrow> accounts newState = []"
  by (smt State.ext_inject State.surjective State.update_convs(4) allAccountsPositiveState.elims(3) isQuiescent.simps(1) positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive reduceContractUntilQuiecentIsQuiescent reduceContractUntilQuiescent.simps timedOutReduceContractLoop_closes_contract validAndPositiveImpliesPositive validAndPositiveImpliesValid validAndPositive_state.elims(3) valid_state.simps)

theorem timedOutTransaction_closes_contract :
  "validAndPositive_state sta
   \<Longrightarrow> iniTime \<ge> minTime sta
   \<Longrightarrow> iniTime \<ge> maxTimeContract cont
   \<Longrightarrow> endTime \<ge> iniTime
   \<Longrightarrow> accounts sta \<noteq> [] \<or> cont \<noteq> Close
   \<Longrightarrow> isClosedAndEmpty (computeTransaction \<lparr> interval = (iniTime, endTime)
                                            , inputs = [] \<rparr> sta cont)"
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps add:Let_def)
  apply (cases "reduceContractUntilQuiescent \<lparr>timeInterval = (max iniTime (minTime sta), endTime)\<rparr> (sta\<lparr>minTime := max iniTime (minTime sta)\<rparr>) cont")
  apply (simp only:ReduceResult.case list.case ApplyAllResult.case max_of_ge)
  apply (cases "cont = Close")
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  apply (metis maxTimeContract.simps(1) reduceContractUntilQuiescent.simps reductionLoopClose_is_Close timedOutReduceContractStep_empties_accounts)
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  subgoal for x11 x12 x13 x14 x15
     apply (rule mp[of x11])
     apply (metis max.orderE timedOutReduceContractStep_empties_accounts timedOutReduceContractUntilQuiescent_closes_contract)
    apply (rule mp[of "x15 = Close"])
    apply (metis (no_types, lifting) ReduceResult.inject ReduceStepResult.exhaust ReduceStepResult.simps(8) ReduceStepResult.simps(9) maxTimeNotAmbiguous_reduceStep reduceContractUntilQuiescent.simps reductionLoop.simps reductionLoop_reduce_monotonic)
    by (metis max.orderE timedOutReduceContractUntilQuiescent_closes_contract)     
  apply (simp del:validAndPositive_state.simps reduceContractUntilQuiescent.simps)
  using maxTimeNotAmbiguous by auto

corollary timeOutTransaction_does_not_fail : 
  assumes "validAndPositive_state sta"
  assumes "emptyTxAfterDeadline = \<lparr> interval = (iniTime, endTime), inputs = [] \<rparr>"
  assumes "iniTime \<ge> minTime sta"
      and "iniTime \<ge> maxTimeContract cont"
      and "endTime \<ge> iniTime" 
  assumes "accounts sta \<noteq> [] \<or> cont \<noteq> Close"
    shows "\<exists>txOut. computeTransaction emptyTxAfterDeadline sta cont = TransactionOutput txOut"
  using assms by (meson Timeout.isClosedAndEmpty.elims(2)  timedOutTransaction_closes_contract)

theorem timeOutTransaction_closes_contract2 :
  "validAndPositive_state sta
   \<Longrightarrow> accounts sta \<noteq> [] \<or> cont \<noteq> Close
   \<Longrightarrow> \<exists> inp . isClosedAndEmpty (computeTransaction inp sta cont)"
  by (meson not_less not_less_iff_gr_or_eq timedOutTransaction_closes_contract)

theorem timedOutTransaction_preserves_assets :
  assumes "validAndPositive_state sta"
  assumes "emptyTxAfterDeadline = \<lparr> interval = (iniTime, endTime), inputs = [] \<rparr>"
  assumes "iniTime \<ge> minTime sta"
      and "iniTime \<ge> maxTimeContract cont"
      and "endTime \<ge> iniTime"
  assumes "accounts sta \<noteq> [] \<or> cont \<noteq> Close"
  assumes "computeTransaction emptyTxAfterDeadline sta cont = TransactionOutput txOut"
  shows "assetsInState sta = assetsInExternalPayments (txOutPayments txOut)"
proof -
  note assms
  moreover have "assetsInState sta + assetsInTransaction emptyTxAfterDeadline 
          = assetsInState (txOutState txOut) + assetsInExternalPayments (txOutPayments txOut)"
    using computeTransaction_preserves_assets calculation by presburger
  moreover have "accounts (txOutState txOut) = []"
    using calculation by (metis Timeout.isClosedAndEmpty.simps(1) timedOutTransaction_closes_contract)
  ultimately show ?thesis by auto
qed

end
