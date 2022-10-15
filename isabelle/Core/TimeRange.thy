theory TimeRange
imports Semantics PositiveAccounts QuiescentResult MoneyPreservation Timeout TransactionBound
begin

fun isCompatible :: "POSIXTime \<times> POSIXTime \<Rightarrow> POSIXTime option \<times> POSIXTime option \<Rightarrow> bool" where
"isCompatible (min1, max1) (None, None) = True" |
"isCompatible (_, max1) (None, Some max2) = (max1 \<le> max2)" |
"isCompatible (min1, _) (Some min2, None) = (min1 \<ge> min2)" |
"isCompatible (min1, max1) (Some min2, Some max2) = (min1 \<ge> min2 \<and> max1 \<le> max2)"

theorem isCompatibleIdempotentToCombineInterval :
  "isCompatible (min1, max1) (min2, max2) =
     (combineIntervals (Some min1, Some max1) (min2, max2) = (Some min1, Some max1))"
  apply (cases min2)
  apply (cases max2)
    apply simp
  subgoal for a
    by auto[1]
    apply (cases max2)
    subgoal for a
      by auto
    subgoal for a b
      by auto
    done

lemma compatibleIdempotency1 :
  "isCompatible (x, y) (combineIntervals b c) \<Longrightarrow> isCompatible (x, y) b"
  apply (cases b)
  apply (cases c)
  subgoal for b1 b2 c1 c2
    apply (simp only:combineIntervals.simps)
    apply (cases b1)
    apply (cases c1)
    apply (smt (verit, best) Semantics.maxOpt.simps(1) Semantics.minOpt.elims TimeRange.isCompatible.simps(1) TimeRange.isCompatible.simps(2))
    apply (smt (verit, ccfv_threshold) Semantics.minOpt.elims TimeRange.isCompatible.simps(1) TimeRange.isCompatible.simps(2) TimeRange.isCompatible.simps(4))
    apply (cases c1)
    apply simp
    apply (smt (verit, del_insts) Option.option.sel Semantics.minOpt.elims TimeRange.isCompatible.simps(3) TimeRange.isCompatible.simps(4))
    apply simp
    apply (cases b2)
    using isCompatibleIdempotentToCombineInterval apply force
    apply (cases c2)
     apply force
    by simp
  done

lemma compatibleIdempotency2 :
  "isCompatible (x, y) (combineIntervals b c) \<Longrightarrow> isCompatible (x, y) c"
  apply (cases b)
  apply (cases c)
  subgoal for b1 b2 c1 c2
    apply (simp only:combineIntervals.simps)
    apply (cases b1)
    apply (cases c1)
    apply (smt (verit, ccfv_SIG) Semantics.maxOpt.simps(1) Semantics.minOpt.elims TimeRange.isCompatible.simps(1) TimeRange.isCompatible.simps(2))
    apply simp
    apply (smt (verit, best) Semantics.minOpt.elims TimeRange.isCompatible.simps(3) TimeRange.isCompatible.simps(4))
    apply (cases c1)
    apply simp
    apply (smt (verit, best) Option.option.discI Pair_inject Semantics.minOpt.elims TimeRange.isCompatible.elims(1) TimeRange.isCompatible.simps(4))
    apply simp
    apply (cases b2)
    using isCompatibleIdempotentToCombineInterval apply force
    apply (cases c2)
     apply force
    by simp
  done

lemma compatibleIdempotencyWhen :
  "b \<le> a2 \<Longrightarrow> b \<le> a1 \<Longrightarrow>
   isCompatible (a1, a2) (calculateTimeInterval n ct (When a b c)) \<Longrightarrow>
   isCompatible (a1, a2) (calculateTimeInterval n ct c)"
  apply (induction a)
  apply (smt (verit, best) Semantics.calculateTimeInterval.simps(4) TimeRange.isCompatible.simps(2) compatibleIdempotency2)
  subgoal for c1 c2
    apply (cases c1)
    apply simp
    apply (cases "gtIfNone n 0")
     apply simp
    using compatibleIdempotency2 apply blast
    by presburger
  done

lemma calculateTimeIntervalAvoidsAmbiguousInterval_When :
   "isCompatible (x, y) (calculateTimeInterval n ct (When a b c)) \<Longrightarrow>
    y < b \<or> x \<ge> b"
  apply (induction a arbitrary:x y n ct b c)
  subgoal for x y n ct b c
    apply (cases "ct < b")
     apply simp
    apply auto
    using TimeRange.isCompatible.simps(3) compatibleIdempotency1 by blast
  subgoal for a1 a2 x y n ct b c
    apply (cases a1)
    apply (simp only:calculateTimeInterval.simps)
    subgoal for a ac
      apply (cases "gtIfNone n 0")
       apply simp
      using compatibleIdempotency2 apply blast
      by simp
    done
  done

lemma calculateTimeIntervalAvoidsAmbiguousInterval_reduceContractStep :
"isCompatible (timeInterval env) (calculateTimeInterval n ct contract) \<Longrightarrow>
 reduceContractStep env state contract \<noteq> AmbiguousTimeIntervalReductionError"
  apply (cases contract)
  apply (cases "refundOne (accounts state)")
  apply auto[1]
       apply auto[1]
  subgoal for a b c d e
    by (auto split:bool.splits simp add:Let_def)
     apply simp
  subgoal for a b c
    apply (auto split:prod.splits)
    subgoal for x y
      using calculateTimeIntervalAvoidsAmbiguousInterval_When by blast
    done
  apply (simp add:Let_def)
  by simp

lemma resultOfReduceIsCompatibleToo :
  "isCompatible (timeInterval env) (calculateTimeInterval n ct contract) \<Longrightarrow>
   reduceContractStep env state contract = Reduced x11 x12 x13 x14 \<Longrightarrow>
   isCompatible (timeInterval env) (calculateTimeInterval n ct x14)"
  apply (cases contract)
  using reduceStepClose_is_Close apply blast
  subgoal for a b c d e
    apply (cases "evalValue env state d \<le> 0")
    by (simp_all add:Let_def)
     apply (smt (verit, best) Semantics.ReduceStepResult.inject Semantics.calculateTimeInterval.simps(3) Semantics.reduceContractStep.simps(3) TimeRange.isCompatible.elims(2) compatibleIdempotency1 compatibleIdempotency2)
  subgoal for a b c
    apply (cases "timeInterval env")
    apply (simp only:reduceContractStep.simps Let_def prod.case)
    subgoal for a1 a2
      apply (cases "a2 < b")
       apply simp
      apply simp
      apply (cases "b \<le> a1")
       apply simp
       apply (meson compatibleIdempotencyWhen linorder_not_le)
      by simp
    done
  apply (metis Semantics.ReduceStepResult.inject Semantics.calculateTimeInterval.simps(6) Semantics.reduceContractStep.simps(5))
  by simp


lemma resultOfReductionLoopQuiescentIsCompatibleToo :
  "isCompatible (timeInterval env) (calculateTimeInterval n ct contract) \<Longrightarrow>
   reductionLoop b env state contract wa ef = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
   isCompatible (timeInterval env) (calculateTimeInterval n ct x15)"
  apply (induction b env state contract wa ef rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (simp only:reductionLoop.simps[of reduced env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for warning effect newState ncontract
      apply (simp only:Let_def ReduceStepResult.case)
      using resultOfReduceIsCompatibleToo by presburger
     apply force
    by simp
  done

lemma resultOfReduceUntilQuiescentIsCompatibleToo :
  "isCompatible (timeInterval env) (calculateTimeInterval n ct contract) \<Longrightarrow>
   reduceContractUntilQuiescent env state contract = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
   isCompatible (timeInterval env) (calculateTimeInterval n ct x15)"
  by (metis Semantics.reduceContractUntilQuiescent.simps resultOfReductionLoopQuiescentIsCompatibleToo)

lemma calculateTimeIntervalAvoidsAmbiguousInterval_reduceContractUntilQuiescent :
"isCompatible (timeInterval env) (calculateTimeInterval n ct contract) \<Longrightarrow>
 reductionLoop b env state contract wa err \<noteq> RRAmbiguousTimeIntervalError"
  apply (induction b env state contract wa err rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (simp only:reductionLoop.simps[of reduced env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
      apply (simp only:ReduceStepResult.case Let_def)
    using resultOfReduceIsCompatibleToo apply presburger
     apply simp
    using calculateTimeIntervalAvoidsAmbiguousInterval_reduceContractStep by auto
  done

fun childCase :: "Contract \<Rightarrow> Case list \<Rightarrow> bool" where
"childCase c Nil = False" |
"childCase c (Cons (Case _ h) t) = ((h = c) \<or> childCase c t)"

lemma successInApplyCasesReturnChildCase :
"applyCases env sta h l = Applied nwa nsta ncont \<Longrightarrow> childCase ncont l"
  apply (induction l)
   apply simp
  subgoal for f t
    apply (cases h)
      apply (cases f)
    subgoal for x11 x12 x13 x14 x1 x2
      apply (cases x1)
      apply (meson Semantics.ApplyResult.inject)
        apply (metis Semantics.ApplyResult.inject Semantics.applyCases.simps(1) TimeRange.childCase.simps(2))
       apply simp
      by simp
    apply (cases f)
    subgoal for x21 x22 x1 x2
      apply (cases x1)
        apply simp
       apply (metis Semantics.ApplyResult.inject Semantics.applyCases.simps(2) TimeRange.childCase.simps(2))
      by simp
    apply (cases f)
    subgoal for x1 x2
      apply (cases x1)
    apply simp
    apply simp
      by (metis Semantics.ApplyResult.inject Semantics.applyCases.simps(3) TimeRange.childCase.simps(2))
    done
  done

lemma resultOfApplyCaseIsCompatibleToo_aux :
"isCompatible (timeInterval env) (calculateTimeInterval n ct (When x41 x42 x43)) \<Longrightarrow>
 childCase ncont x41 \<Longrightarrow> ct < x42 \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 isCompatible (timeInterval env) (calculateTimeInterval (subIfSome n 1) ct ncont)"
  apply (induction x41)
   apply simp
  subgoal for h t
    apply (cases h)
    subgoal for x y
      apply simp
    by (smt (verit, best) TimeRange.isCompatible.elims(3) compatibleIdempotency1 compatibleIdempotency2)
  done
  done

lemma resultOfApplyCaseIsCompatibleToo :
"isCompatible (timeInterval env) (calculateTimeInterval n ct (When x41 x42 x43)) \<Longrightarrow>
 applyCases env sta h x41 = Applied nwa nsta ncont \<Longrightarrow> ct < x42 \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 isCompatible (timeInterval env) (calculateTimeInterval (subIfSome n 1) ct ncont)"
  by (simp add: resultOfApplyCaseIsCompatibleToo_aux successInApplyCasesReturnChildCase)

fun ifCaseLt :: "POSIXTime \<Rightarrow> Contract \<Rightarrow> bool" where
"ifCaseLt ct (When a b c) = (ct < b)" |
"ifCaseLt _ _ = True"

lemma resultOfApplyInputIsCompatibleToo :
"isCompatible (timeInterval env) (calculateTimeInterval n ct cont) \<Longrightarrow>
 applyInput env sta h cont = Applied nwa nsta ncont \<Longrightarrow> ifCaseLt ct cont \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 isCompatible (timeInterval env) (calculateTimeInterval (subIfSome n 1) ct ncont)"
  apply (cases cont)
  apply simp_all
  by (simp add: resultOfApplyCaseIsCompatibleToo)

lemma geIfNone_redListSize :
  "geIfNone n (int (length (h # t))) \<Longrightarrow> geIfNone (subIfSome n 1) (int (length t))"
  by (smt (verit, ccfv_threshold) Semantics.geIfNone.elims(1) Semantics.geIfNone.simps(2) Semantics.subIfSome.elims impossible_Cons of_nat_le_iff)

fun isValidInterval :: "POSIXTime \<times> POSIXTime \<Rightarrow> bool" where
"isValidInterval (a, b) = (a \<le> b)"

lemma reduceStep_ifCaseLtCt_aux : "isCompatible (a, b) (calculateTimeInterval n ct (When x41 x42 x43)) \<Longrightarrow>
                                   a \<le> b \<Longrightarrow> env = \<lparr>timeInterval = (a, b)\<rparr> \<Longrightarrow> b < x42 \<Longrightarrow> ct < x42"
  apply (induction x41)
   apply simp
   apply (smt (verit, best) TimeRange.isCompatible.simps(3) compatibleIdempotency1)
  subgoal for h t
    apply simp
    apply (cases h)
    apply simp
  using compatibleIdempotency2 by presburger
  done

lemma reduceStep_ifCaseLtCt : "isCompatible (timeInterval env) (calculateTimeInterval n ct (When x41 x42 x43)) \<Longrightarrow> 
                               reduceContractStep env state (When x41 x42 x43) = NotReduced \<Longrightarrow> isValidInterval (timeInterval env) \<Longrightarrow> ct < x42"
  apply (cases env)
  subgoal for timeInterv
    apply (cases timeInterv)
    apply simp
    subgoal for a b
      apply (cases "b < x42")
       apply simp
      using reduceStep_ifCaseLtCt_aux apply blast
      by (metis Semantics.ReduceStepResult.distinct(5) Semantics.ReduceStepResult.simps(3))
    done
  done


lemma reduceLoop_ifCaseLtCt : "isCompatible (timeInterval env) (calculateTimeInterval n ct cont) \<Longrightarrow>
                               reductionLoop b env state cont wa ef = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow> isValidInterval (timeInterval env) \<Longrightarrow> ifCaseLt ct x15"
  apply (induction b env state cont wa ef rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
  apply (cases "x15 = Close")
  apply simp
  apply (cases x15)
  apply simp
  apply simp
  apply simp
    apply (simp only:reductionLoop.simps[of reduced env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    apply (simp only:ReduceStepResult.case)
    using resultOfReduceIsCompatibleToo apply presburger
    apply (simp only:ReduceStepResult.case ifCaseLt.simps)
       apply (simp add: reduceStep_ifCaseLtCt)
    apply force
    using TimeRange.ifCaseLt.simps(5) apply blast
    using TimeRange.ifCaseLt.simps(6) by blast
  done

lemma reduceContractUntilQuiescent_ifCaseLtCt : "isCompatible (timeInterval env) (calculateTimeInterval n ct cont) \<Longrightarrow>
                                                 reduceContractUntilQuiescent env state cont = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
                                                 isValidInterval (timeInterval env) \<Longrightarrow> ifCaseLt ct x15"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (simp add: reduceLoop_ifCaseLtCt)

lemma calculateTimeIntervalAvoidsAmbiguousInterval_applyAllLoop :
"geIfNone n (int (length inps)) \<Longrightarrow>
 isCompatible (timeInterval env) (calculateTimeInterval n ct c) \<Longrightarrow>
 isValidInterval (timeInterval env) \<Longrightarrow> 
 applyAllLoop b env s c inps wa ef \<noteq>
 ApplyAllAmbiguousTimeIntervalError"
  apply (induction b env s c inps wa ef arbitrary: n ct rule:applyAllLoop.induct)
  subgoal for contractChanged env state contract inputs warnings payments n ct
    apply (simp only:applyAllLoop.simps[of contractChanged env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
     apply (simp only:ReduceResult.case)
    apply (cases inputs)
    apply (simp only:list.cases)
      apply force
     apply (simp only:list.cases)
    subgoal for x11 x12 x13 x14 x15 h t
      apply (cases "applyInput env x14 h x15")
       apply (simp only:ApplyResult.case)
      subgoal fact for nwa nsta ncont
        subgoal premises fact
        apply (rule fact(1)[of x11 x12 x13 x14 x15 h t nwa nsta ncont "subIfSome n 1" "ct"])
            apply auto
            apply (simp add: fact(7))
            using fact(2) geIfNone_redListSize apply auto[1]
            apply (rule resultOfApplyInputIsCompatibleToo[of env n ct x15 x14 h nwa nsta])
            using fact(3) fact(5) resultOfReduceUntilQuiescentIsCompatibleToo apply blast
            apply (simp add: fact(7))
            using fact(3) fact(4) fact(5) reduceContractUntilQuiescent_ifCaseLtCt apply blast
            using Semantics.gtIfNone.elims(3) fact(2) of_nat_le_iff by fastforce
          done
        by (metis Semantics.ApplyAllResult.distinct(5) Semantics.ApplyResult.simps(5))
      using calculateTimeIntervalAvoidsAmbiguousInterval_reduceContractUntilQuiescent by auto
    done

lemma calculateTimeIntervalAvoidsAmbiguousInterval_applyAllInputs :
"geIfNone n (int (length inps)) \<Longrightarrow>
 isCompatible (minInterv, maxInterv) (calculateTimeInterval n ct c) \<Longrightarrow>
 isValidInterval (minInterv, maxInterv) \<Longrightarrow> 
 applyAllInputs \<lparr> timeInterval = (minInterv, maxInterv) \<rparr> s c inps
    \<noteq> ApplyAllAmbiguousTimeIntervalError"
  apply (simp only:applyAllInputs.simps)
  using calculateTimeIntervalAvoidsAmbiguousInterval_applyAllLoop by auto

theorem calculateTimeIntervalAvoidsAmbiguousInterval :
  "geIfNone n (int (length (inputs tx))) \<Longrightarrow>
   isCompatible (interval tx) (calculateTimeInterval n ct c) \<Longrightarrow>
   computeTransaction tx s c \<noteq> TransactionError TEAmbiguousTimeIntervalError"
  apply (simp only:computeTransaction.simps Let_def)
  apply (cases tx)
  subgoal for interv inps
    apply (cases interv)
    subgoal for minInterv maxInterv
      apply (simp add:Let_def del:applyAllInputs.simps)
      apply (cases "applyAllInputs \<lparr>timeInterval = (max minInterv (minTime s), maxInterv)\<rparr>
           (s\<lparr>minTime := max minInterv (minTime s)\<rparr>) c inps")
      apply simp
      apply simp
      apply (simp del:applyAllInputs.simps)
      by (smt (verit) Semantics.applyAllInputs.simps SemanticsTypes.Environment.select_convs(1) TimeRange.isCompatible.elims(2) TimeRange.isCompatible.simps(1) TimeRange.isCompatible.simps(2) TimeRange.isCompatible.simps(3) TimeRange.isCompatible.simps(4) TimeRange.isValidInterval.simps calculateTimeIntervalAvoidsAmbiguousInterval_applyAllLoop)
    done
  done
end
