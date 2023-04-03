theory SmallStepF
imports Main Util.MList Util.SList ListTools Semantics "HOL-Library.Product_Lexorder" "HOL.Product_Type" "HOL-IMP.Star"
begin

type_synonym Configuration = "Contract * State * Environment * (ReduceWarning list) * (Payment list)"

inductive
  small_step_reduce :: "Configuration \<Rightarrow> Configuration \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
CloseRefund:  "refundOne (accounts s) = Some ((party, token, money), newAccount) \<Longrightarrow>
  (Close, s, env, warns, payments) \<rightarrow>
  (Close, (s\<lparr>accounts := newAccount\<rparr>), env, warns @ [ReduceNoWarning], payments @ [Payment party (Party party) token money])" |
PayNonPositive: "evalValue env s val \<le> 0 \<Longrightarrow>
  (Pay accId payee token val cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceNonPositivePay accId payee token (evalValue env s val)], payments)" |
\<comment>\<open>TODO: Partial external payment\<close>
PayPositivePartialWithPayment: "\<lbrakk>
  \<comment>\<open>TODO: We may be able to remove this using validAndPositive_state\<close>
  evalValue env s val > 0;
  moneyInAccount accId token (accounts s) = availableMoney; 
  evalValue env s val > availableMoney;
  updateMoneyInAccount accId token 0 (accounts s) = newAccs;
  giveMoney accId payee token (availableMoney) newAccs = (ReduceWithPayment payment, finalAccs)
  \<rbrakk> \<Longrightarrow>
  (Pay accId payee token val cont, s, env, warns, payments) \<rightarrow>
  ((cont, s\<lparr>accounts := finalAccs\<rparr>, env, warns @ [ReducePartialPay accId payee token availableMoney (evalValue env s val)], payments @ [payment]))" |
\<comment>\<open>TODO: Partial internal payment\<close>
PayPositivePartialWithoutPayment: "\<lbrakk>
  \<comment>\<open>TODO: We may be able to remove this using validAndPositive_state\<close>
  evalValue env s val > 0;
  moneyInAccount accId token (accounts s) = availableMoney;
  evalValue env s val > availableMoney;
  updateMoneyInAccount accId token 0 (accounts s) = newAccs;  
  giveMoney accId payee token (availableMoney) newAccs = (ReduceNoPayment, finalAccs)
  \<rbrakk> \<Longrightarrow>
  (Pay accId payee token val cont, s, env, warns, payments) \<rightarrow>
  ((cont, s\<lparr>accounts := finalAccs\<rparr>, env, warns @ [ReducePartialPay accId payee token availableMoney (evalValue env s val)], payments))" |
\<comment>\<open>TODO: Full external payment\<close>
PayPositiveFullWithPayment: "\<lbrakk>evalValue env s val > 0;
  moneyInAccount accId token (accounts s) = availableMoney;
  evalValue env s val \<le> availableMoney;
  availableMoney - (evalValue env s val) = newBalance;
  updateMoneyInAccount accId token newBalance (accounts s) = newAccs;
  giveMoney accId payee token (evalValue env s val) newAccs = (ReduceWithPayment payment, finalAccs)
  \<rbrakk> \<Longrightarrow>
  (Pay accId payee token val cont, s, env, warns, payments) \<rightarrow>
  (cont, s\<lparr>accounts := finalAccs\<rparr>, env, warns @ [ReduceNoWarning], payments @ [payment])" |
\<comment>\<open>TODO: Full internal payment\<close>
PayPositiveFullWithoutPayment: "\<lbrakk>evalValue env s val > 0;
  moneyInAccount accId token (accounts s) = availableMoney;
  evalValue env s val \<le> availableMoney;
  availableMoney - (evalValue env s val) = newBalance;
  updateMoneyInAccount accId token newBalance (accounts s) = newAccs;
  giveMoney accId payee token (evalValue env s val) newAccs = (ReduceNoPayment, finalAccs)
  \<rbrakk> \<Longrightarrow>
  (Pay accId payee token val cont, s, env, warns, payments) \<rightarrow>
  (cont, s\<lparr>accounts := finalAccs\<rparr>, env, warns @ [ReduceNoWarning], payments)"  |
IfTrue: "evalObservation env s obs \<Longrightarrow>
  (If obs cont1 cont2, s, env, warns, payments) \<rightarrow>
  (cont1, s, env, warns @ [ReduceNoWarning], payments)" |
IfFalse: "\<not>evalObservation env s obs \<Longrightarrow>
  (If obs cont1 cont2, s, env, warns, payments) \<rightarrow>
  (cont2, s, env, warns @ [ReduceNoWarning], payments)" |
WhenTimeout: "\<lbrakk>timeInterval env = (startTime, endTime);
  endTime \<ge> timeout;
  startTime \<ge> timeout\<rbrakk> \<Longrightarrow>
  (When cases timeout cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceNoWarning], payments)"|
LetShadow: "\<lbrakk> lookup valId (boundValues s) = Some oldVal; 
  evalValue env s val = newVal
  \<rbrakk> \<Longrightarrow>
  (Let valId val cont, s, env, warns, payments) \<rightarrow>
  (cont, s\<lparr> boundValues := MList.insert valId newVal (boundValues s)\<rparr>, env, warns @ [ReduceShadowing valId oldVal newVal], payments)" |
LetNoShadow: "lookup valId (boundValues s) = None \<Longrightarrow>
  (Let valId val cont, s, env, warns, payments) \<rightarrow>
  (cont, s\<lparr> boundValues := MList.insert valId (evalValue env s val) (boundValues s)\<rparr>, env, warns @ [ReduceNoWarning], payments)"  |
AssertTrue: "evalObservation env s obs \<Longrightarrow>
  (Assert obs cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceNoWarning], payments)" |
AssertFalse: "\<not>evalObservation env s obs \<Longrightarrow>
  (Assert obs cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceAssertionFailed], payments)"

abbreviation
  small_step_reduces :: "Configuration \<Rightarrow> Configuration \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step_reduce x y"

(*Small Step Induction from FaustusSemantics*)
thm small_step_reduce.induct
lemmas small_step_reduce_induct = small_step_reduce.induct[split_format(complete)]
thm small_step_reduce_induct
declare small_step_reduce.intros[simp,intro]

(*Needed to use Elimination rules for smallStepReductionImpReduceStep lemma*)
inductive_cases CloseE[elim]: "(Close, s, env, warns, payments) \<rightarrow> ct"
thm CloseE
inductive_cases PayE[elim!]: "(Pay accId payee token val cont, s, env, warns, payments) \<rightarrow> ct"
thm PayE
inductive_cases IfE[elim!]: "(If obs cont1 cont2, s, env, warns, payments) \<rightarrow> ct"
thm IfE
inductive_cases WhenE[elim!]: "(When cases timeout cont, s, env, warns, payments) \<rightarrow> ct"
thm WhenE
inductive_cases LetE[elim!]: "(Let valId val cont, s, env, warns, payments) \<rightarrow> ct"
thm LetE
inductive_cases AssertE[elim!]: "(Assert obs cont, s, env, warns, payments) \<rightarrow> ct"
thm AssertE

(*Warning Lemmas*)


text \<open>If we have a valid transition, the warnings doesn't have an effect on the other components 
of the configuration\<close>
lemma smallStepWarningsAreArbitrary:
"(c, s, e, w, p) \<rightarrow> (c', s', e', w', p') \<Longrightarrow>
  (\<forall>w'' . \<exists>w''' . (c, s, e, w'', p) \<rightarrow> (c', s', e', w''', p'))"
  apply (induction c s e w p c' s' e' w' p' rule: small_step_reduce_induct)
  by (blast | auto)+


lemma smallStepStarWarningsAreArbitrary:
  "(c, s, e, w, p) \<rightarrow>* (c', s', e', w'', p') \<Longrightarrow>
    (\<forall>w'' . \<exists>w''' . (c, s, e, w'', p) \<rightarrow>* (c', s', e', w''', p'))"
apply (induction rule: star.induct[of "small_step_reduce", split_format(complete)], auto)
  by (meson smallStepWarningsAreArbitrary star.step)

text "A configuration cs is final if there is no transition that can be made."
definition "finalConfiguration cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma finalD:
"finalConfiguration (contract, s, e, w, p) \<Longrightarrow>
  contract = Close \<or> (\<exists> cases timeout continue . contract = When cases timeout continue)"
  apply (auto simp add: finalConfiguration_def)
  apply (cases contract, auto)
     apply (meson PayNonPositive PayPositiveFullWithPayment PayPositiveFullWithoutPayment PayPositivePartialWithPayment PayPositivePartialWithoutPayment giveMoney.elims not_less)
    apply (meson IfFalse IfTrue)
   apply (meson LetShadow option.exhaust_sel small_step_reduce.intros(11))
  by (meson small_step_reduce.intros(12) small_step_reduce.intros(13))

(*BEGIN proof of Reduce Step is a Small Step Reduction in Marlowe*)
lemma reduceStepIsSmallStepReduction:
assumes "reduceContractStep env state contract = Reduced warning paymentReduceResult newState continueContract"
shows "\<exists> appendPayment .(contract, state, env, initialWarnings, initialPayments) \<rightarrow> (continueContract, newState, env, initialWarnings @ [warning], initialPayments @ appendPayment)"
proof (cases contract paymentReduceResult rule: Contract.exhaust[case_product ReduceEffect.exhaust])
  case Close_ReduceNoPayment
  then show ?thesis using assms apply auto
    by (cases "refundOne (accounts state)", auto)
next
  case (Close_ReduceWithPayment reducePayment)
  then show ?thesis using assms apply auto
(*Current place that's stuck.*)
    by (cases "refundOne (accounts state)", auto)
next
  case (Pay_ReduceNoPayment accId payee token val cont)
  then show ?thesis using assms apply auto
    apply (cases "evalValue env state val \<le> 0", auto)
     apply (metis PayNonPositive append_Nil2)
    subgoal premises ps proof (cases "lookup (accId, token) (accounts state)")
      case None
      moreover have "(min 0 (evalValue env state val)) = 0" using ps(4) by auto
      ultimately show ?thesis using ps apply auto
        subgoal premises ps proof (cases "giveMoney payee token 0 (MList.delete (accId, token) (accounts state))")
          case (Pair payment finalAccs)
          moreover from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                     initialWarnings, initialPayments) \<rightarrow>
                   (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                    initialWarnings @ [ReducePartialPay accId payee token 0 (evalValue env state val)],
                    initialPayments @ [])" using ps calculation by auto
          ultimately show ?thesis using ps by (smt ReduceStepResult.inject State.simps(6) State.surjective old.prod.case)
        qed
        done
    next
      case (Some availableBal)
      moreover have "availableBal \<le> evalValue env state val \<Longrightarrow> min availableBal (evalValue env state val) = availableBal" by simp
      moreover have "\<not>(availableBal \<le> evalValue env state val) \<Longrightarrow> min availableBal (evalValue env state val) = (evalValue env state val)" by simp
      ultimately show ?thesis using ps apply auto
        apply (cases "availableBal \<le> evalValue env state val", auto)
        subgoal premises ps proof (cases "giveMoney payee token availableBal (MList.delete (accId, token) (accounts state))")
          case (Pair payment finalAccs)
          then show ?thesis using ps apply auto
            apply (cases "availableBal < (evalValue env state val)", auto)
            subgoal premises ps proof -
              from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                             initialWarnings, initialPayments) \<rightarrow>
                           (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                            initialWarnings @ [ReducePartialPay accId payee token availableBal (evalValue env state val)],
                            initialPayments @ [])" by auto
              then show ?thesis by meson
            qed
            subgoal premises ps proof -
              from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                              initialWarnings, initialPayments) \<rightarrow>
                             (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                              initialWarnings @ [ReduceNoWarning], initialPayments @ [])" by auto
              then show ?thesis by meson
            qed
            done
        qed
        subgoal premises ps proof (cases "giveMoney payee token (evalValue env state val) (MList.insert (accId, token) (availableBal - (evalValue env state val)) (accounts state))")
          case (Pair payment finalAccs)
          then show ?thesis using ps apply auto
            subgoal premises ps proof -
              from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                              initialWarnings, initialPayments) \<rightarrow>
                             (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                              initialWarnings @ [ReduceNoWarning], initialPayments @ [])" by auto
              then show ?thesis by meson
            qed
            done
        qed
        done
    qed
    done
next
  case (Pay_ReduceWithPayment accId payee token val cont payment)
  then show ?thesis using assms apply auto
    apply (cases "evalValue env state val \<le> 0", auto)
    subgoal premises ps proof (cases "lookup (accId, token) (accounts state)")
      case None
      moreover from ps have "min 0 (evalValue env state val) = 0" by simp
      ultimately show ?thesis using ps apply auto
        subgoal premises ps proof (cases "giveMoney payee token 0 (MList.delete (accId, token) (accounts state))")
          case (Pair reduceEffect finalAccs)
          moreover from ps calculation have "(Contract.Pay accId payee token val continueContract, state, env,
                              initialWarnings, initialPayments) \<rightarrow>
                             (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                              initialWarnings @ [ReducePartialPay accId payee token 0 (evalValue env state val)],
                              initialPayments @ [payment])" by auto
          (*by auto before elimination rules*)
          ultimately show ?thesis using ps by (auto, meson)
        qed
        done
    next
      case (Some bal)
      then show ?thesis using ps apply auto
        apply (cases "bal \<le> evalValue env state val", auto)
        subgoal premises ps proof -
          from ps have "min bal (evalValue env state val) = bal" by simp
          then show ?thesis using ps apply auto
            subgoal premises ps proof (cases "giveMoney payee token bal (MList.delete (accId, token) (accounts state))")
              case (Pair reduceEffect finalAccs)
              then show ?thesis using ps apply auto
                apply (cases "bal < evalValue env state val", auto)
                subgoal premises ps proof -
                  from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                                initialWarnings, initialPayments) \<rightarrow>
                               (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                                initialWarnings @ [ReducePartialPay accId payee token bal (evalValue env state val)],
                                initialPayments @ [payment])" by simp
                  then show ?thesis by meson
                qed
                subgoal premises ps proof -
                  from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                                initialWarnings, initialPayments) \<rightarrow>
                               (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                                initialWarnings @ [ReduceNoWarning], initialPayments @ [payment])" by simp
                  then show ?thesis by meson
                qed
                done
            qed
            done
        qed
        subgoal premises ps proof -
          from ps have "min bal (evalValue env state val) = evalValue env state val" by simp
          then show ?thesis using ps apply auto
            subgoal premises ps proof (cases "giveMoney payee token (evalValue env state val) (MList.insert (accId, token) (bal - (evalValue env state val)) (accounts state))")
              case (Pair reduceEffect finalAccs)
              moreover from ps calculation have "(Contract.Pay accId payee token val continueContract, state, env,
                                  initialWarnings, initialPayments) \<rightarrow>
                                 (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                                  initialWarnings @ [ReduceNoWarning], initialPayments @ [payment])" by auto
              (*used calculation by auto before elimination rules*)
              then show ?thesis using ps by (auto, meson)
            qed
            done
        qed
        done
    qed
    done

next
  case (If_ReduceNoPayment x31 x32 x33)
  then show ?thesis using assms apply auto
     apply (metis IfTrue append_Nil2)
    by (metis IfFalse append.right_neutral)
next
  case (If_ReduceWithPayment x31 x32 x33 x2)
  then show ?thesis using assms by auto
next
  case (When_ReduceNoPayment x41 timeout x43)
  then show ?thesis using assms apply auto
    subgoal premises ps proof (cases "slotInterval env")
      case (Pair ss es)
      then show ?thesis using ps apply auto
        apply (cases "es < timeout", auto)
        apply (cases "timeout \<le> ss", auto)
        by (smt WhenTimeout append_Nil2)
    qed
    done
(*Removed LetC and UseC cases*)
next
  case (When_ReduceWithPayment x41 x42 x43 x2)
  then show ?thesis using assms apply auto
  by (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject Pair_inject ReduceEffect.distinct(1) fixInterval.cases old.prod.case)
next
  case (Let_ReduceNoPayment vid x52 x53)
  then show ?thesis using assms apply auto
    apply (cases "lookup vid (boundValues state)", auto)
     apply (metis LetNoShadow append_Nil2)
    by (metis (no_types, lifting) ReduceStepResult.inject LetShadow State.unfold_congs(3) append_Nil2)
next
  case (Let_ReduceWithPayment vid x52 x53 x2)
  then show ?thesis using assms apply auto
    apply (cases "lookup vid (boundValues state)", auto)
    by (meson ReduceStepResult.inject ReduceEffect.distinct(1))
next
  case (Assert_ReduceNoPayment x61 x62)
  then show ?thesis using assms apply auto
     apply (metis AssertTrue append.right_neutral)
    by (metis AssertFalse append_Nil2)
next
  case (Assert_ReduceWithPayment x61 x62 x2)
  then show ?thesis using assms by auto
next
qed

lemma reduceStepIsSmallStepReductionNoPayment:
assumes "reduceContractStep env state contract = Reduced warning ReduceNoPayment newState continueContract"
shows "(contract, state, env, initialWarnings, initialPayments) \<rightarrow> (continueContract, newState, env, initialWarnings @ [warning], initialPayments)"
proof (cases contract)
  case Close
  then show ?thesis using assms apply auto
    by (cases "refundOne (accounts state)", auto)
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms apply auto
    apply (cases "evalValue env state val \<le> 0", auto)
    subgoal premises ps proof (cases "lookup (accId, token) (accounts state)")
      case None
      moreover have "(min 0 (evalValue env state val)) = 0" using ps by auto
      ultimately show ?thesis using ps apply auto
        subgoal premises ps proof (cases "giveMoney payee token 0 (MList.delete (accId, token) (accounts state))")
          case (Pair payment finalAccs)
          moreover from ps have "(Contract.Pay accId payee token val continueContract, state, env,
                     initialWarnings, initialPayments) \<rightarrow>
                   (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                    initialWarnings @ [ReducePartialPay accId payee token 0 (evalValue env state val)],
                    initialPayments @ [])" using ps calculation by auto
          ultimately show ?thesis using ps by simp
        qed
        done
    next
      case (Some availableBal)
      moreover have "availableBal \<le> evalValue env state val \<Longrightarrow> min availableBal (evalValue env state val) = availableBal" by simp
      moreover have "\<not>(availableBal \<le> evalValue env state val) \<Longrightarrow> min availableBal (evalValue env state val) = (evalValue env state val)" by simp
      ultimately show ?thesis using ps apply auto
        apply (cases "availableBal \<le> evalValue env state val", auto)
        subgoal premises ps proof (cases "giveMoney payee token availableBal (MList.delete (accId, token) (accounts state))")
          case (Pair payment finalAccs)
          then show ?thesis using ps by (cases "availableBal < (evalValue env state val)", auto)
        qed
        subgoal premises ps proof (cases "giveMoney payee token (evalValue env state val) (MList.insert (accId, token) (availableBal - (evalValue env state val)) (accounts state))")
          case (Pair payment finalAccs)
          then show ?thesis using ps by auto
        qed
        done
    qed
    done
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When x41 timeout x43)
  then show ?thesis using assms apply auto
    subgoal premises ps proof (cases "slotInterval env")
      case (Pair ss es)
      then show ?thesis using ps apply auto
        apply (cases "es < timeout", auto)
        by (cases "timeout \<le> ss", auto)
    qed
    done
next
  case (Let vid x52 x53)
  then show ?thesis using assms apply auto
    apply (cases "lookup vid (boundValues state)", auto)
    by (metis (no_types, lifting) ReduceStepResult.inject LetShadow State.unfold_congs(3))
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

lemma reduceStepIsSmallStepReductionWithPayment:
assumes "reduceContractStep env state contract = Reduced warning (ReduceWithPayment payment) newState continueContract"
shows "(contract, state, env, initialWarnings, initialPayments) \<rightarrow> (continueContract, newState, env, initialWarnings @ [warning], initialPayments @ [payment])"
proof (cases contract)
  case (Close)
  then show ?thesis using assms by (cases "refundOne (accounts state)", auto)
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms apply auto
    apply (cases "evalValue env state val \<le> 0", auto)
    subgoal premises ps proof (cases "lookup (accId, token) (accounts state)")
      case None
      moreover from ps have "min 0 (evalValue env state val) = 0" by simp
      ultimately show ?thesis using ps apply auto
        subgoal premises ps proof (cases "giveMoney payee token 0 (MList.delete (accId, token) (accounts state))")
          case (Pair reduceEffect finalAccs)
          moreover from ps calculation have "(Contract.Pay accId payee token val continueContract, state, env,
                              initialWarnings, initialPayments) \<rightarrow>
                             (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                              initialWarnings @ [ReducePartialPay accId payee token 0 (evalValue env state val)],
                              initialPayments @ [payment])" by auto
          ultimately show ?thesis using ps by auto
        qed
        done
    next
      case (Some bal)
      then show ?thesis using ps apply auto
        apply (cases "bal \<le> evalValue env state val", auto)
        subgoal premises ps proof -
          from ps have "min bal (evalValue env state val) = bal" by simp
          then show ?thesis using ps apply auto
            subgoal premises ps proof (cases "giveMoney payee token bal (MList.delete (accId, token) (accounts state))")
              case (Pair reduceEffect finalAccs)
              then show ?thesis using ps by (cases "bal < evalValue env state val", auto)
            qed
            done
        qed
        subgoal premises ps proof -
          from ps have "min bal (evalValue env state val) = evalValue env state val" by simp
          then show ?thesis using ps apply auto
            subgoal premises ps proof (cases "giveMoney payee token (evalValue env state val) (MList.insert (accId, token) (bal - (evalValue env state val)) (accounts state))")
              case (Pair reduceEffect finalAccs)
              moreover from ps calculation have "(Contract.Pay accId payee token val continueContract, state, env,
                                  initialWarnings, initialPayments) \<rightarrow>
                                 (continueContract, state\<lparr>accounts := finalAccs\<rparr>, env,
                                  initialWarnings @ [ReduceNoWarning], initialPayments @ [payment])" by auto
              then show ?thesis using ps by (auto, meson)
            qed
            done
        qed
        done
    qed
    done
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When x41 x42 x43)
  then show ?thesis using assms apply auto
  by (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject Pair_inject ReduceEffect.distinct(1) fixInterval.cases old.prod.case)
next
  case (Let vid x52 x53)
  then show ?thesis using assms apply auto
    apply (cases "lookup vid (boundValues state)", auto)
    by (meson ReduceStepResult.inject ReduceEffect.distinct(1))
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

(*BEGIN proof Small Step in Marlowe implies that there is a Reduced Step*)

lemma smallStepReductionAddsOneWarning:
assumes "cs = (contract, state, env, initialWarnings, initialPayments) \<and>
    cs' = (continueContract, newState, newEnv, newWarnings, newPayments) \<and>
    cs \<rightarrow> cs'"
shows "\<exists>newWarning . newWarnings = initialWarnings @ [newWarning]"
proof (cases contract)
  case Close
  then show ?thesis using assms by auto
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms by auto
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When cases timeout cont)
  then show ?thesis using assms by auto
next
  case (Let x51 x52 x53)
  then show ?thesis using assms by auto
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

lemma smallStepReductionImpReduceStep:
assumes "cs = (contract, state, env, initialWarnings, initialPayments) \<and>
    cs' = (continueContract, newState, newEnv, initialWarnings @ [warning], newPayments) \<and>
    cs \<rightarrow> cs'"
shows "\<exists> paymentReduceResult . reduceContractStep env state contract = Reduced warning paymentReduceResult newState continueContract"
proof (cases contract)
  case Close
  then show ?thesis using assms by auto
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms by (auto simp add: min.strict_order_iff min.absorb_iff2)
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When cases timeout cont)
  then show ?thesis using assms by auto
next
  case (Let x51 x52 x53)
  then show ?thesis using assms apply auto
    by metis
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

lemma smallStepReductionGivesOnePaymentMax:
assumes "cs = (contract, state, env, initialWarnings, initialPayments) \<and>
    cs' = (continueContract, newState, newEnv, initialWarnings @ [warning], newPayments) \<and>
    cs \<rightarrow> cs'"
shows "newPayments = initialPayments \<or> (\<exists>newPayment . newPayments = initialPayments @ [newPayment])"
proof (cases contract)
  case Close
  then show ?thesis using assms by auto
next
  case (Pay x21 x22 x23 x24 x25)
  then show ?thesis using assms by auto
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When x41 x42 x43)
  then show ?thesis using assms by auto
next
  case (Let x51 x52 x53)
  then show ?thesis using assms by auto
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

lemma smallStepReductionImpReduceStepNoPayment:
assumes "cs = (contract, state, env, initialWarnings, initialPayments) \<and>
    cs' = (continueContract, newState, newEnv, initialWarnings @ [warning], initialPayments) \<and>
    cs \<rightarrow> cs'"
shows "reduceContractStep env state contract = Reduced warning ReduceNoPayment newState continueContract"
proof (cases contract)
  case Close
  then show ?thesis using assms by auto
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms by (auto simp add: min.strict_order_iff min.absorb_iff2)
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When cases timeout cont)
  then show ?thesis using assms by auto
next
  case (Let x51 x52 x53)
  then show ?thesis using assms apply auto
    by metis
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

lemma smallStepReductionImpReduceStepWithPayment:
assumes "cs = (contract, state, env, initialWarnings, initialPayments) \<and>
    cs' = (continueContract, newState, newEnv, initialWarnings @ [warning], initialPayments @ [newPayment]) \<and>
    cs \<rightarrow> cs'"
shows "reduceContractStep env state contract = Reduced warning (ReduceWithPayment newPayment) newState continueContract"
proof (cases contract)
  case Close
  then show ?thesis using assms by auto
next
  case (Pay accId payee token val cont)
  then show ?thesis using assms by (auto simp add: min.strict_order_iff min.absorb_iff2)
next
  case (If x31 x32 x33)
  then show ?thesis using assms by auto
next
  case (When cases timeout cont)
  then show ?thesis using assms by auto
next
  case (Let x51 x52 x53)
  then show ?thesis using assms by auto
next
  case (Assert x61 x62)
  then show ?thesis using assms by auto
qed

end
