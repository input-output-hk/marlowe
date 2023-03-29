theory TimeRange
imports Semantics PositiveAccounts QuiescentResult Timeout TransactionBound
begin


subsection "calculateNonAmbiguousInterval"

text "Helper functions for \<^emph>\<open>calculateNonAmbiguousInterval\<close>"
fun gtIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"gtIfNone None _ = True" |
"gtIfNone (Some x) y = (x > y)"

fun geIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"geIfNone None _ = True" |
"geIfNone (Some x) y = (x \<ge> y)"

fun subIfSome :: "int option \<Rightarrow> int \<Rightarrow> int option" where
"subIfSome None _ = None" |
"subIfSome (Some x) y = Some (x - y)"


text \<open>
A TimeInterval (startTime, endTime) can be ambiguous wrt a When's timeout if startTime < timeout \<le> endTime

\<close>

text \<open>The \<^emph>\<open>calculateNonAmbiguousInterval\<close> function can help a user to calculate a TimeInterval that
won't be ambiguous for the next \<^emph>\<open>n\<close> inputs of a contract.\<close>

text \<open>The only Contract constructor that can yield a \<^term>\<open>TEAmbiguousTimeIntervalError\<close> is the \<^term>\<open>When\<close> case. 
Computing a transaction of a contract that starts in a non quiescent state (\<^term>\<open>Let\<close>, \<^term>\<open>Pay\<close>, \<^term>\<open>If\<close>, \<^term>\<open>Assert\<close>) 
can end in a \<^term>\<open>TEAmbiguousTimeIntervalError\<close> iff there is a \<^term>\<open>When\<close> case that makes it ambiguous.
\<close>

text \<open>A TimeInterval expressed as the tuple \<^term>\<open>(startTime \<times> endTime)\<close> can be ambiguous wrt a \<^term>\<open>When\<close>'s timeout
iff \<^emph>\<open>startTime < timeout \<le> endTime\<close>
\<close>

text
\<open> The parameters of \<^emph>\<open>calculateNonAmbiguousInterval\<close> are:
\<^item> An optional number of Inputs to check. The number of inputs corresponds to the number of "When". 
If None is passed, it means that we should check for transactions of any number of inputs.
\<^item> A lower bound (normally the current time).
\<^item> The Contract to check.

The function returns an Optionally Bound Time Interval, as defined in the \<^emph>\<open>OptBoundTimeInterval.thy\<close> theory.
In the \<^emph>\<open>TimeRange.thy\<close> theory we prove that computing a transaction with these bounds doesn't end with an ambiguous error. 
\<close>
\<comment> \<open>NOTE: The intersectInterval can produce an invalid time interval, which would mean that not suitable TimeInterval was found\<close>
fun calculateNonAmbiguousInterval :: "int option \<Rightarrow> POSIXTime \<Rightarrow> Contract \<Rightarrow> OptBoundTimeInterval"
  where
\<comment> \<open>A Close contract can't be ambiguous, so an Unbounded interval is returned \<close>
"calculateNonAmbiguousInterval _ _ Close = (Unbounded, Unbounded)" |
\<comment> \<open>A Pay contract isn't ambiguous by itself, so we calculate for the continuation\<close>
"calculateNonAmbiguousInterval n t (Pay _ _ _ _ c) = calculateNonAmbiguousInterval n t c" |
\<comment> \<open>If we branch, we intersect the result of both possibilites. \<close>
\<comment> \<open>FIXME: Note that not knowing which branch can be selected beforehand means that we return a smaller TimeInterval than
possible. Maybe we could improve this by using the actual Input instead of the number of inputs\<close>
"calculateNonAmbiguousInterval n t (If _ ct cf) = intersectInterval 
                                                           (calculateNonAmbiguousInterval n t ct)
                                                           (calculateNonAmbiguousInterval n t cf)" |
\<comment> \<open>We treat the When contract in two parts. The base case (when no actions are available) and a recursive
case, when we have a particular action \<close>
"calculateNonAmbiguousInterval n t (When [] timeout tcont) =
  (if t < timeout
  \<comment> \<open>If the When's timeout is in the future, we can generate a non-ambiguous time interval
      by restricting the endTime to be strictly lower than the timeout\<close>
   then (Unbounded, Bounded (timeout - 1))
  \<comment> \<open>If the timeout is in the past, we need to restrict the startTime to be larger or equal than
     the timeout\<close>
   else intersectInterval (Bounded timeout, Unbounded) (calculateNonAmbiguousInterval n t tcont))" |

"calculateNonAmbiguousInterval n t (When (Case _ cont  # restCases) timeout tcont) =  
  (if gtIfNone n 0
\<comment> \<open>If n is none (check all) or n > 0 we recursively calculate the intersection for all the continuations\<close>
   then intersectInterval (calculateNonAmbiguousInterval (subIfSome n 1) t cont)
                         (calculateNonAmbiguousInterval n t (When restCases timeout tcont))
\<comment> \<open>If n \<le> 0 we don't calculate for the current case and we iterate until we reach the base case\<close>  
\<comment> \<open>TODO: we should be able to change restCases for [] to check the base case directly\<close>
   else calculateNonAmbiguousInterval n t (When restCases timeout tcont))" |
\<comment> \<open>A Let or Assert contracts aren't ambiguous by themselves, so we calculate for the continuation\<close>
"calculateNonAmbiguousInterval n t (Let _ _ c) = calculateNonAmbiguousInterval n t c" |
"calculateNonAmbiguousInterval n t (Assert _ c) = calculateNonAmbiguousInterval n t c"


theorem inIntervalIdempotentToIntersectInterval :
  "inInterval (min1, max1) (min2, max2) =
     (intersectInterval (Bounded min1, Bounded max1) (min2, max2) = (Bounded min1, Bounded max1))"
  by (cases min2;cases max2;auto) 

lemma inIntervalIdempotency1 :
  assumes "inInterval (x, y) (intersectInterval b c)"
  shows   "inInterval (x, y) b"
proof (cases b)
  case [simp]: (Pair b1 b2)
  thus ?thesis proof (cases c)
    case (Pair c1 c2)
    thus ?thesis using assms by (cases c1; cases c2; cases b1; cases b2; simp)
  qed
qed


lemma inIntervalIdempotency2 :
  assumes "inInterval (x, y) (intersectInterval b c)"
  shows   "inInterval (x, y) c"
proof (cases b)
  case [simp]: (Pair b1 b2)
  thus ?thesis proof (cases c)
    case (Pair c1 c2)
    thus ?thesis using assms by (cases c1; cases c2; cases b1; cases b2; simp)
  qed
qed


lemma compatibleIdempotencyWhen :
  "b \<le> a2 \<Longrightarrow> b \<le> a1 \<Longrightarrow>
   inInterval (a1, a2) (calculateNonAmbiguousInterval n ct (When a b c)) \<Longrightarrow>
   inInterval (a1, a2) (calculateNonAmbiguousInterval n ct c)"
  apply (induction a)
  apply (smt (verit, best) OptBoundTimeInterval.inInterval.simps(2) calculateNonAmbiguousInterval.simps(4) inIntervalIdempotency2)
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
    apply (smt (verit, del_insts) OptBoundTimeInterval.inInterval.elims(3) Semantics.ReduceStepResult.inject calculateNonAmbiguousInterval.simps(3) Semantics.reduceContractStep.simps(3) inIntervalIdempotency1 inIntervalIdempotency2)
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
  apply (metis Semantics.ReduceStepResult.inject calculateNonAmbiguousInterval.simps(6) Semantics.reduceContractStep.simps(5))
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
  by (smt (verit, ccfv_threshold) geIfNone.elims(1) geIfNone.simps(2) subIfSome.elims impossible_Cons of_nat_le_iff)


lemma reduceStep_ifCaseLtCt_aux : "inInterval (a, b) (calculateNonAmbiguousInterval n ct (When x41 x42 x43)) \<Longrightarrow>
                                   a \<le> b \<Longrightarrow> b < x42 \<Longrightarrow> ct < x42"
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
            using gtIfNone.elims(3) fact(2) of_nat_le_iff by fastforce
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
  using geIfNone.simps(2) calculateNonAmbiguousIntervalAvoidsAmbiguousInterval by blast

corollary calculateNonAmbiguousIntervalAvoidsAmbiguousInterval_unbounded :
  "inInterval (interval tx) (calculateNonAmbiguousInterval None ct c) \<Longrightarrow>
   computeTransaction tx s c \<noteq> TransactionError TEAmbiguousTimeIntervalError"
  by (meson geIfNone.simps(1) calculateNonAmbiguousIntervalAvoidsAmbiguousInterval)

end
