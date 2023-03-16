theory TimeRange
imports Semantics PositiveAccounts QuiescentResult Timeout TransactionBound
begin

theorem inIntervalIdempotentToIntersectInterval :
  "inInterval (min1, max1) (min2, max2) =
     (intersectInterval (Bounded min1, Bounded max1) (min2, max2) = (Bounded min1, Bounded max1))"
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

lemma inIntervalIdempotency1 :
  "inInterval (x, y) (intersectInterval b c) \<Longrightarrow> inInterval (x, y) b"
  apply (cases b)
  apply (cases c)
  subgoal for b1 b2 c1 c2
    apply (simp only:inInterval.simps)
    apply (cases b1)
    apply (cases c1)
    apply (smt (verit, best) OptBoundTimeInterval.intersectInterval.simps OptBoundTimeInterval.maxLow.simps(1) OptBoundTimeInterval.minHigh.elims assoc commute inIntervalIdempotentToIntersectInterval)
    apply (smt (verit, ccfv_threshold) OptBoundTimeInterval.inInterval.simps(2) OptBoundTimeInterval.inInterval.simps(4) OptBoundTimeInterval.intersectInterval.simps OptBoundTimeInterval.maxLow.simps(2) OptBoundTimeInterval.minHigh.elims OptBoundTimeInterval.minHigh.simps(2) inIntervalIdempotentToIntersectInterval maxLow_comm)
    apply (cases c1)
    apply simp
    apply (smt (verit, ccfv_threshold) OptBoundTimeInterval.inInterval.simps(3) OptBoundTimeInterval.inInterval.simps(4) OptBoundTimeInterval.minHigh.elims)
    by (smt (verit) Groups.abel_semigroup.commute Groups.semigroup.assoc OptBoundTimeInterval.intersectInterval.simps OptBoundTimeInterval.maxLow.simps(3) OptBoundTimeInterval.minHigh.elims abel_semigroup_axioms inIntervalIdempotentToIntersectInterval semigroup_axioms)
  done

lemma inIntervalIdempotency2 :
  "inInterval (x, y) (intersectInterval b c) \<Longrightarrow> inInterval (x, y) c"
  apply (cases b)
  apply (cases c)
  subgoal for b1 b2 c1 c2
    apply (simp only:intersectInterval.simps)
    apply (cases b1)
    apply (cases c1)
    apply (metis OptBoundTimeInterval.intersectInterval.simps commute inIntervalIdempotency1)
    apply (metis OptBoundTimeInterval.intersectInterval.simps commute inIntervalIdempotency1)
    apply simp
    by (metis OptBoundTimeInterval.intersectInterval.simps inIntervalIdempotency1 minHigh_comm)
  done

lemma compatibleIdempotencyWhen :
  "b \<le> a2 \<Longrightarrow> b \<le> a1 \<Longrightarrow>
   inInterval (a1, a2) (calculateNonAmbiguousInterval n ct (When a b c)) \<Longrightarrow>
   inInterval (a1, a2) (calculateNonAmbiguousInterval n ct c)"
  apply (induction a)
  apply (smt (verit, best) OptBoundTimeInterval.inInterval.simps(2) Semantics.calculateNonAmbiguousInterval.simps(4) inIntervalIdempotency2)
  subgoal for c1 c2
    apply (cases c1)
    apply simp
    apply (cases "gtIfNone n 0")
     apply simp
    using inIntervalIdempotency2 apply blast
    by presburger
  done

lemma calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_When :
   "inInterval (x, y) (calculateNonAmbiguousInterval n ct (When a b c)) \<Longrightarrow>
    y < b \<or> x \<ge> b"
  apply (induction a arbitrary:x y n ct b c)
  subgoal for x y n ct b c
    apply (cases "ct < b")
     apply simp
    apply auto
    using OptBoundTimeInterval.inInterval.simps(3) inIntervalIdempotency1 by blast
  subgoal for a1 a2 x y n ct b c
    apply (cases a1)
    apply (simp only:calculateNonAmbiguousInterval.simps)
    subgoal for a ac
      apply (cases "gtIfNone n 0")
       apply simp
      using inIntervalIdempotency2 apply blast
      by simp
    done
  done

lemma calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_reduceContractStep :
"inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct contract) \<Longrightarrow>
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
      using calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_When by blast
    done
  apply (simp add:Let_def)
  by simp

lemma resultOfReduceIsCompatibleToo :
  "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct contract) \<Longrightarrow>
   reduceContractStep env state contract = Reduced x11 x12 x13 x14 \<Longrightarrow>
   inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct x14)"
  apply (cases contract)
  using reduceStepClose_is_Close apply blast
  subgoal for a b c d e
    apply (cases "evalValue env state d \<le> 0")
    by (simp_all add:Let_def)
    apply (smt (verit, del_insts) OptBoundTimeInterval.inInterval.elims(3) Semantics.ReduceStepResult.inject Semantics.calculateNonAmbiguousInterval.simps(3) Semantics.reduceContractStep.simps(3) inIntervalIdempotency1 inIntervalIdempotency2)
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
  apply (metis Semantics.ReduceStepResult.inject Semantics.calculateNonAmbiguousInterval.simps(6) Semantics.reduceContractStep.simps(5))
  by simp

lemma resultOfReductionLoopQuiescentIsCompatibleToo :
  "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct contract) \<Longrightarrow>
   reductionLoop b env state contract wa ef = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
   inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct x15)"
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
  "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct contract) \<Longrightarrow>
   reduceContractUntilQuiescent env state contract = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
   inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct x15)"
  by (metis Semantics.reduceContractUntilQuiescent.simps resultOfReductionLoopQuiescentIsCompatibleToo)

lemma calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_reduceContractUntilQuiescent :
"inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct contract) \<Longrightarrow>
 reductionLoop b env state contract wa err \<noteq> RRAmbiguousTimeIntervalError"
  apply (induction b env state contract wa err rule:reductionLoop.induct)
  subgoal for reduced env state contract warnings payments
    apply (simp only:reductionLoop.simps[of reduced env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
      apply (simp only:ReduceStepResult.case Let_def)
    using resultOfReduceIsCompatibleToo apply presburger
     apply simp
    using calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_reduceContractStep by auto
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
"inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct (When x41 x42 x43)) \<Longrightarrow>
 childCase ncont x41 \<Longrightarrow> ct < x42 \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 inInterval (timeInterval env) (calculateNonAmbiguousInterval (subIfSome n 1) ct ncont)"
  apply (induction x41)
   apply simp
  subgoal for h t
    apply (cases h)
    subgoal for x y
      apply simp
      by (smt (verit, best) OptBoundTimeInterval.inInterval.elims(3) inIntervalIdempotency1 inIntervalIdempotency2)
  done
  done

lemma resultOfApplyCaseIsCompatibleToo :
"inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct (When x41 x42 x43)) \<Longrightarrow>
 applyCases env sta h x41 = Applied nwa nsta ncont \<Longrightarrow> ct < x42 \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 inInterval (timeInterval env) (calculateNonAmbiguousInterval (subIfSome n 1) ct ncont)"
  by (simp add: resultOfApplyCaseIsCompatibleToo_aux successInApplyCasesReturnChildCase)

fun ifCaseLt :: "POSIXTime \<Rightarrow> Contract \<Rightarrow> bool" where
"ifCaseLt ct (When a b c) = (ct < b)" |
"ifCaseLt _ _ = True"

lemma resultOfApplyInputIsCompatibleToo :
"inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct cont) \<Longrightarrow>
 applyInput env sta h cont = Applied nwa nsta ncont \<Longrightarrow> ifCaseLt ct cont \<Longrightarrow> gtIfNone n 0 \<Longrightarrow>
 inInterval (timeInterval env) (calculateNonAmbiguousInterval (subIfSome n 1) ct ncont)"
  apply (cases cont)
  apply simp_all
  by (simp add: resultOfApplyCaseIsCompatibleToo)

lemma geIfNone_redListSize :
  "geIfNone n (int (length (h # t))) \<Longrightarrow> geIfNone (subIfSome n 1) (int (length t))"
  by (smt (verit, ccfv_threshold) Semantics.geIfNone.elims(1) Semantics.geIfNone.simps(2) Semantics.subIfSome.elims impossible_Cons of_nat_le_iff)


lemma reduceStep_ifCaseLtCt_aux : "inInterval (a, b) (calculateNonAmbiguousInterval n ct (When x41 x42 x43)) \<Longrightarrow>
                                   a \<le> b \<Longrightarrow> env = \<lparr>timeInterval = (a, b)\<rparr> \<Longrightarrow> b < x42 \<Longrightarrow> ct < x42"
  apply (induction x41)
   apply simp
   apply (smt (verit, best) OptBoundTimeInterval.inInterval.simps(3) inIntervalIdempotency1)
  subgoal for h t
    apply simp
    apply (cases h)
    apply simp
  using inIntervalIdempotency2 by presburger
  done

lemma reduceStep_ifCaseLtCt : "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct (When x41 x42 x43)) \<Longrightarrow>
                               reduceContractStep env state (When x41 x42 x43) = NotReduced \<Longrightarrow> validTimeInterval (timeInterval env) \<Longrightarrow> ct < x42"
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

lemma reduceLoop_ifCaseLtCt : "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct cont) \<Longrightarrow>
                               reductionLoop b env state cont wa ef = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow> validTimeInterval (timeInterval env) \<Longrightarrow> ifCaseLt ct x15"
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

lemma reduceContractUntilQuiescent_ifCaseLtCt : "inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct cont) \<Longrightarrow>
                                                 reduceContractUntilQuiescent env state cont = ContractQuiescent x11 x12 x13 x14 x15 \<Longrightarrow>
                                                 validTimeInterval (timeInterval env) \<Longrightarrow> ifCaseLt ct x15"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (simp add: reduceLoop_ifCaseLtCt)

lemma calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_applyAllLoop :
"geIfNone n (int (length inps)) \<Longrightarrow>
 inInterval (timeInterval env) (calculateNonAmbiguousInterval n ct c) \<Longrightarrow>
 validTimeInterval (timeInterval env) \<Longrightarrow>
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
      using calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_reduceContractUntilQuiescent by auto
    done

lemma calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_applyAllInputs :
"geIfNone n (int (length inps)) \<Longrightarrow>
 inInterval (minInterv, maxInterv) (calculateNonAmbiguousInterval n ct c) \<Longrightarrow>
 validTimeInterval (minInterv, maxInterv) \<Longrightarrow>
 applyAllInputs \<lparr> timeInterval = (minInterv, maxInterv) \<rparr> s c inps
    \<noteq> ApplyAllAmbiguousTimeIntervalError"
  apply (simp only:applyAllInputs.simps)
  using calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_applyAllLoop by auto

theorem calculateNonAmbiguousIntervalAvoidsAmbiguousInterval :
  "geIfNone n (int (length (inputs tx))) \<Longrightarrow>
   inInterval (interval tx) (calculateNonAmbiguousInterval n ct c) \<Longrightarrow>
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
      apply (cases s)
      apply (simp del:applyAllInputs.simps)
      subgoal for accounts choices boundValues minTime
        apply (cases "minInterv \<le> minTime")
        apply (simp del:applyAllInputs.simps)
         apply (smt (verit, ccfv_threshold) OptBoundTimeInterval.inInterval.elims(3) OptBoundTimeInterval.inInterval.simps(2) OptBoundTimeInterval.inInterval.simps(3) OptBoundTimeInterval.inInterval.simps(4) validTimeInterval.simps calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_applyAllInputs)
        by (metis Lattices.linorder_class.max.absorb4 Lattices.linorder_class.max.commute OptBoundTimeInterval.validTimeInterval.simps calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_applyAllInputs linorder_not_le)
      done
    done
  done

corollary calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_bounded :
  "n \<ge> (int (length (inputs tx))) \<Longrightarrow>
   inInterval (interval tx) (calculateNonAmbiguousInterval (Some n) ct c) \<Longrightarrow>
   computeTransaction tx s c \<noteq> TransactionError TEAmbiguousTimeIntervalError"
  using Semantics.geIfNone.simps(2) calculateNonAmbiguousIntervalAvoidsAmbiguousInterval by blast

corollary calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_unbounded :
  "inInterval (interval tx) (calculateNonAmbiguousInterval None ct c) \<Longrightarrow>
   computeTransaction tx s c \<noteq> TransactionError TEAmbiguousTimeIntervalError"
  by (meson Semantics.geIfNone.simps(1) calculateNonAmbiguousIntervalAvoidsAmbiguousInterval)

end
