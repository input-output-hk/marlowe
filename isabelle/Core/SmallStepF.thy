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
text \<open>
The following lemma proves that the interpreter and the semantics yield the same 
results
\<close>

fun effectAsPaymentList :: "ReduceEffect \<Rightarrow> Payment list" where
 "effectAsPaymentList ReduceNoPayment = [] "
|"effectAsPaymentList (ReduceWithPayment p) = [p]"

thm Contract.exhaust
lemma reduceStepIsSmallStepReduction:
  assumes "reduceContractStep env prevState prevCont = 
             Reduced newWarning paymentReduceResult newState newCont"
  shows "
        ( prevCont
        , prevState
        , env
        , prevWarnings
        , prevPayments
        ) \<rightarrow> 
          ( newCont
          , newState
          , env
          , prevWarnings @ [newWarning]
          , prevPayments @ effectAsPaymentList paymentReduceResult
          )"
using assms proof (cases prevCont paymentReduceResult rule: Contract.exhaust[case_product ReduceEffect.exhaust])
  case Close_ReduceNoPayment
  then show ?thesis 
    using assms apply auto
    by (cases "refundOne (accounts prevState)", auto)
next
  case (Close_ReduceWithPayment reducePayment)
  then show ?thesis 
    using assms apply auto
    by (cases "refundOne (accounts prevState)", auto)
next
  case (Pay_ReduceNoPayment accId payee token val cont)
  then show ?thesis 
    using assms apply auto
    apply (cases "evalValue env prevState val \<le> 0", auto)
    by (metis Semantics.ReduceEffect.distinct(1) Semantics.ReduceStepResult.inject)   
next
  case (Pay_ReduceWithPayment accId payee token val cont payment)
  then show ?thesis 
  proof (cases "evalValue env prevState val \<le> 0")
    case True
    with assms Pay_ReduceWithPayment  show ?thesis by auto
  next
    case False
    then obtain moneyToPay availableMoney newAccs newBalance paidMoney where 0:
      "moneyToPay = evalValue env prevState val"
      "availableMoney = moneyInAccount accId token (accounts prevState)"
      "paidMoney = min availableMoney moneyToPay"
      "newBalance = availableMoney - paidMoney"
      "newAccs = updateMoneyInAccount accId token newBalance (accounts prevState)"
      by simp_all
   
    have 4: "payment = Payment accId payee token paidMoney" 
      using assms False 0 Pay_ReduceWithPayment
        (* TODO: simplify *)
      apply (simp only: reduceContractStep.simps )
      
      apply (simp only: False Let_def if_False)
      apply (simp only: giveMoney.simps)
      apply (cases payee)
      by auto
    (*
    then obtain finalAccs p2 where 1:
      "(p2, finalAccs) = giveMoney accId payee token (availableMoney) newAccs"
      using False  assms Pay_ReduceWithPayment
      by (metis Semantics.giveMoney.simps)*)
    then obtain finalAccs where 1:
      "(ReduceWithPayment payment, finalAccs) = giveMoney accId payee token (availableMoney) newAccs"
      using False  assms Pay_ReduceWithPayment 0 4
      apply auto
      (* TODO: we ended mob programming here *)

    have 2: "p2 = ReduceWithPayment payment"
      using 0 1 4 False assms Pay_ReduceWithPayment  
      
      apply (cases payee)
      apply (cases "lookup (accId, token) (accounts prevState)")
      
        apply (simp)

       apply auto
      sorry
      
(*    have 3: "availableMoney \<ge> 0" 
      sledgehammer*)
    with False assms Pay_ReduceWithPayment 0 1 2  show ?thesis
      apply auto
      apply (cases "evalValue env prevState val > availableMoney")
       apply auto
      

      sorry
  qed
(*
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
*)

next
  case (When_ReduceNoPayment x41 timeout x43)
  then show ?thesis using assms 
    apply auto
    sorry
(*    subgoal premises ps proof (cases "slotInterval env")
      case (Pair ss es)
      then show ?thesis using ps apply auto
        apply (cases "es < timeout", auto)
        apply (cases "timeout \<le> ss", auto)
        by (smt WhenTimeout append_Nil2)
    qed
    done*)
(*Removed LetC and UseC cases*)
next
  (* TODO: rename variables *)
  case (When_ReduceWithPayment x41 x42 x43 x2)
  then show ?thesis using assms apply auto
  by (smt ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject Pair_inject ReduceEffect.distinct(1) fixInterval.cases old.prod.case)
next
  case (Let_ReduceNoPayment vid x52 x53)
  then show ?thesis using assms apply auto
    sorry    
(*
    apply (cases "lookup vid (boundValues prevState)", auto)
     apply (metis LetNoShadow append_Nil2)
    by (metis (no_types, lifting) ReduceStepResult.inject LetShadow State.unfold_congs(3) append_Nil2)*)
next
  case (Let_ReduceWithPayment vid x52 x53 x2)
  then show ?thesis using assms 
    apply auto
    apply (cases "lookup vid (boundValues prevState)", auto)
    by (meson ReduceStepResult.inject ReduceEffect.distinct(1))
qed auto

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
