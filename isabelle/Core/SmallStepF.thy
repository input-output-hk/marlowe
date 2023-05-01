theory SmallStepF
imports Main Util.MList Util.SList ListTools Semantics "HOL-Library.Product_Lexorder" "HOL.Product_Type" "HOL-IMP.Star" PositiveAccounts
begin

type_synonym Configuration = "Contract * State * Environment * (ReduceWarning list) * (Payment list)"

inductive
  small_step_reduce :: "Configuration \<Rightarrow> Configuration \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where

CloseRefund:  
  "refundOne (accounts s) = Some ((party, token, money), newAccount) \<Longrightarrow>
  ( Close
  , s
  , env
  , warns
  , payments
  ) \<rightarrow>
  ( Close
  , s\<lparr>accounts := newAccount\<rparr>
  , env
  , warns @ [ReduceNoWarning]
  , payments @ [Payment party (Party party) token money]
  )" 

|PayNonPositive: 
  "evalValue env s val \<le> 0 \<Longrightarrow>
  (Pay accId payee token val cont
  , s
  , env
  , warns
  , payments
  ) \<rightarrow>
  ( cont
  , s
  , env
  , warns @ [ReduceNonPositivePay accId payee token (evalValue env s val)]
  , payments
  )" 
(*validAndPositive_state s; *)
|PayInternalTransfer: 
 "\<lbrakk> 
    evalValue env state val = moneyToPay;
    moneyToPay > 0;
    moneyInAccount srcAccId token (accounts state) = availableSrcMoney;   
    min availableSrcMoney moneyToPay = paidMoney;  
    Account dstAccId = payee;
    \<comment> \<open>Internal transfer\<close>
    updateMoneyInAccount srcAccId token (availableSrcMoney - paidMoney) (accounts state) 
      = accsWithoutSrc;    
    addMoneyToAccount dstAccId token paidMoney accsWithoutSrc = finalAccs
  \<rbrakk> \<Longrightarrow>
  ( Pay srcAccId payee token val cont
  , state
  , env
  , warns
  , payments
  ) \<rightarrow>
  ( cont
  , state\<lparr>accounts := finalAccs\<rparr>
  , env
  , warns @ [ if paidMoney < moneyToPay
              then ReducePartialPay srcAccId payee token paidMoney moneyToPay
              else ReduceNoWarning
            ]
  , payments @ [Payment srcAccId payee token paidMoney]
  )" 
(* validAndPositive_state s;*)
|PayExternal: 
 "\<lbrakk>
    evalValue env state val = moneyToPay;
    moneyToPay > 0;
    moneyInAccount srcAccId token (accounts state) = availableSrcMoney;   
    min availableSrcMoney moneyToPay = paidMoney;  
    Party external = payee;
    \<comment> \<open>If the payment is external, the funds are removed from the source account, but \<close>
    \<comment> \<open>the actual payment is expected to occur outside of these semantics\<close>
    updateMoneyInAccount srcAccId token (availableSrcMoney - paidMoney) (accounts state) 
      = accsWithoutSrc
  \<rbrakk> \<Longrightarrow>
  ( Pay srcAccId payee token val cont
  , state
  , env
  , warns
  , payments
  ) \<rightarrow>
  ( cont
  , state\<lparr>accounts := accsWithoutSrc\<rparr>
  , env
  , warns @ [ if paidMoney < moneyToPay
              then ReducePartialPay srcAccId payee token paidMoney moneyToPay
              else ReduceNoWarning
            ]
  , payments @ [Payment srcAccId payee token paidMoney]
  )" 
|IfTrue: 
 "evalObservation env s obs \<Longrightarrow>
  (If obs cont1 cont2, s, env, warns, payments) \<rightarrow>
  (cont1, s, env, warns @ [ReduceNoWarning], payments)" 
|IfFalse: 
 "\<not>evalObservation env s obs \<Longrightarrow>
  (If obs cont1 cont2, s, env, warns, payments) \<rightarrow>
  (cont2, s, env, warns @ [ReduceNoWarning], payments)" 
|WhenTimeout: 
 "\<lbrakk> timeInterval env = (startTime, endTime);
\<comment> \<open>TODO: Shouldn't this be startTime \<le> endTime \<le> timeout? \<close>
    endTime \<ge> timeout;
    startTime \<ge> timeout
  \<rbrakk> \<Longrightarrow>
  (When cases timeout cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceNoWarning], payments)"

|LetShadow: 
 "\<lbrakk> lookup valId (boundValues s) = Some oldVal;
    evalValue env s val = newVal
  \<rbrakk> \<Longrightarrow>
  ( Let valId val cont
  , s
  , env
  , warns
  , payments
  ) \<rightarrow>
  ( cont
  , s\<lparr> boundValues := MList.insert valId newVal (boundValues s)\<rparr>
  , env
  , warns @ [ReduceShadowing valId oldVal newVal]
  , payments
  )" 

|LetNoShadow: "lookup valId (boundValues s) = None \<Longrightarrow>
  ( Let valId val cont
  , s
  , env
  , warns
  , payments) \<rightarrow>
  ( cont
  , s \<lparr> boundValues := MList.insert valId (evalValue env s val) (boundValues s)\<rparr>
  , env
  , warns @ [ReduceNoWarning]
  , payments
  )"  

|AssertTrue: "evalObservation env s obs \<Longrightarrow>
  (Assert obs cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceNoWarning], payments)" 

|AssertFalse: "\<not>evalObservation env s obs \<Longrightarrow>
  (Assert obs cont, s, env, warns, payments) \<rightarrow>
  (cont, s, env, warns @ [ReduceAssertionFailed], payments)"
thm PayInternalTransfer[of env s2 v m sc t asr pm dstAccId payee accsWithoutSrc finalAccs cont2 prevWarnings prevPayments ]
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

declare finalConfiguration_def [simp add]

fun isClose :: "Contract \<Rightarrow> bool" where 
"isClose Close = True" 
|"isClose _ = False"

fun isWhen :: "Contract \<Rightarrow> bool" where 
"isWhen (When _ _ _) = True" 
|"isWhen _ = False"


lemma finalD:
(*  assumes "validAndPositive_state s"*)
  assumes "finalConfiguration (contract, s, e, w, p)"
  shows   "isClose contract \<or> isWhen contract"  
proof (cases contract)
  case (Pay accId payee token val cont)
  then obtain moneyToPay where moneyToPay: "evalValue e s val = moneyToPay" 
    by simp
  
  then have "finalConfiguration (contract, s, e, w, p) = False"
  proof (cases "moneyToPay \<le> 0")
    case True
    with Pay moneyToPay show "?thesis"
      by (meson PayNonPositive finalConfiguration_def)
  next
    case False
    have 0: "moneyToPay > 0" 
      using False by linarith
   
    then show ?thesis
      apply (cases payee, auto)      
      using assms(1) Pay moneyToPay by blast+   
  qed
    
  with assms show ?thesis by auto
next
  case (If obs trueCont falseCont)
  then have "finalConfiguration (contract, s, e, w, p) = False"
    apply (cases "evalObservation e s obs", auto)
    by blast+
  with assms show ?thesis by auto
next
  case (Let valId val cont)
  then have "finalConfiguration (contract, s, e, w, p) = False"
    apply (cases "lookup valId (boundValues s)", auto)
    by blast+
  with assms show ?thesis by auto
next
  case (Assert obs cont)
  then have "finalConfiguration (contract, s, e, w, p) = False"
    apply (cases "evalObservation e s obs", auto)
    by blast+
  with assms show ?thesis by auto
qed auto
 

(*BEGIN proof of Reduce Step is a Small Step Reduction in Marlowe*)
text \<open>
The following lemma proves that the interpreter and the semantics yield the same 
results
\<close>

fun effectAsPaymentList :: "ReduceEffect \<Rightarrow> Payment list" where
 "effectAsPaymentList ReduceNoPayment = [] "
|"effectAsPaymentList (ReduceWithPayment p) = [p]"

thm Contract.exhaust

thm PayInternalTransfer[of env2 state2]
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
  case (Pay_ReduceWithPayment srcAccId payee token val cont payment)
  then show ?thesis 
  proof (cases "evalValue env prevState val \<le> 0")
    case True
    with assms Pay_ReduceWithPayment  show ?thesis by auto
  next
    case False
    then obtain moneyToPay availableSrcMoney accsWithoutSrc paidMoney where 0:
      "moneyToPay = evalValue env prevState val"
      "availableSrcMoney = moneyInAccount srcAccId token (accounts prevState)"
      "paidMoney = min availableSrcMoney moneyToPay"
      "accsWithoutSrc = updateMoneyInAccount srcAccId token (availableSrcMoney - paidMoney) (accounts prevState)"
      by simp_all
    have 9: "cont = newCont" 
      using assms Pay_ReduceWithPayment(1) False 
      apply (cases "payee")
      by (auto simp add: Let_def )
      
    have 4: "payment = Payment srcAccId payee token paidMoney" 
      using assms False 0 Pay_ReduceWithPayment
        (* TODO: simplify *)
      apply (simp only: reduceContractStep.simps )
      
      apply (simp only: False Let_def if_False)
      apply (simp only: giveMoney.simps)
      apply (cases payee)
      by auto

    with False have 5: "moneyToPay > 0" 
      by (simp add: "0"(1))

    have 7: "paymentReduceResult = ReduceWithPayment (Payment srcAccId payee token paidMoney)"
      using assms  Pay_ReduceWithPayment 4
      by force
    have 8: "newWarning = (if paidMoney < moneyToPay
              then ReducePartialPay srcAccId payee token paidMoney moneyToPay
              else ReduceNoWarning)"
         using assms  Pay_ReduceWithPayment 
         by (smt (verit, best) "0"(1) "0"(2) "0"(3) False Semantics.ReduceStepResult.inject Semantics.giveMoney.simps Semantics.reduceContractStep.simps(2) case_prod_conv)

    show ?thesis proof (cases "payee")
      case (Account dstAccId)
      obtain finalAccs where 6:
          "finalAccs = addMoneyToAccount dstAccId token paidMoney accsWithoutSrc"
        by simp

      (* TODO: simplify *)
      have 10: "newState= prevState\<lparr>accounts := finalAccs\<rparr>"
        using assms Pay_ReduceWithPayment(1)
        apply (simp only: reduceContractStep.simps)
        apply (simp only: Let_def)
        apply (simp only: False)
        apply (simp only: if_False)
        apply (simp only: giveMoney.simps)
        apply (simp only: Let_def)
        apply (simp only: Account)
        apply (simp only: Payee.case)

        using "0"(1) "0"(2) "0"(3) "0"(4) "6" by force

      thm  PayInternalTransfer[of env prevState val moneyToPay srcAccId token availableSrcMoney paidMoney dstAccId payee accsWithoutSrc finalAccs newCont prevWarnings prevPayments ]
      show ?thesis
        apply (subst 7)
        apply (subst 8)
        apply (subst effectAsPaymentList.simps)
        apply (subst 10)
        apply (subst Pay_ReduceWithPayment)
        apply (subst 9)
        apply (subst  PayInternalTransfer[of env prevState val moneyToPay srcAccId token availableSrcMoney paidMoney dstAccId payee accsWithoutSrc finalAccs newCont prevWarnings prevPayments ] )
        using 0 5 6 Account by auto
    next
      case (Party external)
      have 11: "newState= prevState\<lparr>accounts := accsWithoutSrc\<rparr>"
        using assms Pay_ReduceWithPayment(1) 
        apply (simp only: reduceContractStep.simps)
        apply (simp only: Let_def)
        apply (simp only: False)
        apply (simp only: if_False)
        apply (simp only: giveMoney.simps)
        apply (simp only: Let_def)
        apply (simp only: Party)
        apply (simp only: Payee.case)
        using "0"(1) "0"(2) "0"(3) "0"(4) by force
 
      thm  PayExternal[of env prevState val moneyToPay srcAccId token availableSrcMoney paidMoney external payee accsWithoutSrc newCont prevWarnings prevPayments]      
      show ?thesis 
        apply (subst 11)
        apply (subst Pay_ReduceWithPayment)
        apply (subst 9)
        apply (subst 8)
        apply (subst 7)
        apply (subst effectAsPaymentList.simps)
        apply (subst PayExternal[of env prevState val moneyToPay srcAccId token availableSrcMoney paidMoney external payee accsWithoutSrc newCont prevWarnings prevPayments])
        using 0 5 Party by auto
    qed
  qed


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
