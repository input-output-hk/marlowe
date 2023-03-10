(*<*)
theory SmallStepReduceContract
  imports Semantics "HOL-IMP.Star"

begin
(*>*)

section "Small step semantics for reduce contract step"

record RCSmallStepConf =
  contract :: Contract
  warnings :: "ReduceWarning set"
  environment :: Environment
  payments :: "Payment set"
  state :: State
  


(*<*)
inductive small_step_reduce_contract :: "RCSmallStepConf \<Rightarrow> RCSmallStepConf \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>r" 55)
where
CloseBS: 
\<open>   refundOne (accounts s) = Some ((rAccId, rTok, rVal), newAccount) \<Longrightarrow>
    \<lparr> contract = Close
    , warnings = warn
    , environment = env
    , payments = pays
    , state = s    
    \<rparr> \<rightarrow>\<^sub>r
    \<lparr> contract = Close
    , warnings = warn
    , environment = env
    , payments = pays \<union> {Payment rAccId (Party rAccId) rTok rVal}
    , state = s \<lparr> accounts := newAccount\<rparr>
    \<rparr>
\<close>
| IfTrue:
\<open>
  evalObservation env s obs \<Longrightarrow>
    \<lparr> contract = If obs trueC falseC
    , warnings = warn
    , environment = env
    , payments = pays
    , state = s
    \<rparr> \<rightarrow>\<^sub>r
    \<lparr> contract = trueC
    , warnings = warn
    , environment = env
    , payments = pays
    , state = s 
    \<rparr>
\<close>



(* Borrowed from IMP-Hol Theory, working with a Tuple for the input is nice for using
the arrow syntax, but it doesn't work nice when you are proving things with big_step.induct
as the variables are not replaced automatically. Using the big_step_induct theory instead fixes
that. *)

lemmas small_step_reduce_contract_induct = small_step_reduce_contract.induct[split_format(complete)]

thm small_step_reduce_contract.induct
thm small_step_reduce_contract_induct

abbreviation small_steps_reduce_contract :: "RCSmallStepConf \<Rightarrow> RCSmallStepConf \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>r*" 55) where 
  "x \<rightarrow>\<^sub>r* y \<equiv> star small_step_reduce_contract x y "


lemma small_steps_reduce_contract_deterministic:
  "cs \<rightarrow>\<^sub>r cs' \<Longrightarrow> cs \<rightarrow>\<^sub>r cs'' \<Longrightarrow> cs'' = cs'"
  proof (induction arbitrary: cs'' rule: small_step_reduce_contract.induct)
    case (CloseBS s rAccId rTok rVal newAccount warn env pays)
    let ?cs = "\<lparr>contract = Close, warning = warn, environment = env, payments = pays, state = s\<rparr>"
    from CloseBS show ?case
     
      sorry
  next
    case (IfTrue env s obs trueC falseC warn pays)
    then show ?case 
      using SmallStepReduceContract.small_step_reduce_contract.cases by auto
  qed

section "Reduce contract step" 

fun reduceEffectAsPaymentSet :: "ReduceEffect \<Rightarrow> Payment set" where 
  "reduceEffectAsPaymentSet ReduceNoPayment = {}"
| "reduceEffectAsPaymentSet (ReduceWithPayment p) = {p}"

fun reduceContractStepResult_equiv :: "ReduceStepResult \<Rightarrow> RCSmallStepConf \<Rightarrow> bool" (infixl "\<equiv>\<^sub>\<rightarrow>" 50) where
  "NotReduced \<equiv>\<^sub>\<rightarrow> bs = False "
| "AmbiguousTimeIntervalReductionError  \<equiv>\<^sub>\<rightarrow> bs = False "
| "Reduced rWarn rEff rState rContract  \<equiv>\<^sub>\<rightarrow> bs \<longleftrightarrow> 
    (rContract = contract bs 
      \<and> {rWarn} = warnings bs
      \<and> reduceEffectAsPaymentSet rEff = payments bs
      \<and> rState = state bs
    )"



(*<*)

lemma reduceContractUntilQuiscentOnCloseMakesPayments :
  assumes "accounts inState \<noteq> []"
  shows "reduceContractUntilQuiescent env inState Close
       = ContractQuiescent reduced [] pays newState Close"
  sorry

theorem computeTransactionAbidesBigStep : "(c, tx, s) \<rightarrow> out \<Longrightarrow> computeTransaction tx s c \<equiv>\<^sub>\<rightarrow> out" 
proof (induction out   rule: small_step_induct )
  case (CloseBS tx s)
  then obtain env newState where 0: "fixInterval (interval tx) s = IntervalTrimmed env newState"     
    using fixedTransaction_implies_IntervalTrimmed 
    by blast
  then show ?case 
    apply (subst computeTransaction.simps)
    apply (subst Let_def)
    apply (subst 0)
    apply (subst IntervalResult.case)
    apply (subst applyAllInputs.simps)
    apply (subst applyAllLoop.simps)
    apply auto
    sorry
next
  case (IfTrue tx s env fixSta obs trueC falseC)
  then show ?case sorry
next
  case (IfFalse tx s env fixSta obs trueC falseC)
  then show ?case sorry
qed
(*>*)
(*
lemma bigStepImpliesSuccessfullComputeTransaction :
  "(c, tx, s) \<Rightarrow> bs \<Longrightarrow>
  \<exists> to. computeTransaction tx s c = TransactionOutput to" 
proof (induct bs rule: big_step_induct )
  case (CloseBS tx s)
  then obtain fixEnv fixState where 0: "fixInterval (interval tx) s = IntervalTrimmed fixEnv fixState" 
    using fixedTransaction_implies_IntervalTrimmed by blast

  then show ?case 
    apply (simp only: computeTransaction.simps)
    apply (subst Let_def)
    apply (subst IntervalResult.case)
    apply auto
    sorry
next
  case (IfTrue tx s env fixSta obs tc bs fc)
  then show ?case sorry
qed

theorem computeTransactionFollowsBigStep : "(tx, s, c) \<Rightarrow> out \<Longrightarrow> computeTransaction tx s c = out" 
proof (induction out   rule: big_step.induct )
  case (CloseWOAccounts s tx)
  then show ?case sorry
next
  case (CloseWAccounts s tx)
  then show ?case sorry
qed
*)

(*
  fix tx s  i
  assume "accounts s = []" and "tx =  \<lparr> interval = i, inputs = [] \<rparr>"
  
  then show "computeTransaction tx s Close = out"
    apply (subst computeTransaction.simps)
    apply (subst Let_def)
    sorry
next
  case (CloseWAccounts s tx)
  then show ?case sorry
qed
*)
(*
theorem computeTransactionFollowsBigStep : " (tx, s, c) \<Rightarrow> out \<Longrightarrow> (tx, s, c) \<Rightarrow> out' \<Longrightarrow> out = out'" 
proof (induction arbitrary: out' rule: big_step.induct )
*)

section "inference rule latex testing"

text
\<open>
 
\begin{center}
  @{thm[mode=Rule,margin=100](lhs) IfFalse} {\sc IfFalse}
\end{center}
\<close>

text
\<open>
 
\begin{center}
  @{thm[mode=Rule,margin=100](rhs) IfFalse} {\sc IfFalse}
\end{center}
\<close>

text
\<open>
 
\begin{center}
  @{thm[mode=Rule,margin=100](concl) IfFalse} {\sc IfFalse}
\end{center}
\<close>

thm (prem) IfFalse
thm (concl) IfFalse
end

