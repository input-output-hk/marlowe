(*<*)
theory SmallStep
  imports Semantics

begin
(*>*)

section "Small step semantics"

record SmallStepResult =
  warnings :: "TransactionWarning set" 
  payments :: "Payment set" 
  state :: State
  contract :: Contract


(*<*)
inductive small_step :: "(Contract \<times> Transaction \<times> State ) \<Rightarrow> SmallStepResult \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
CloseBS: 
\<open>
  \<lbrakk>fixedTransaction tx s; inputs tx = [] \<rbrakk> \<Longrightarrow>
  (Close, tx, s) \<rightarrow>
    \<lparr> warnings = Set.empty
    , payments = accountsAsPayments (accounts s)
    , state = s \<lparr> accounts := []\<rparr>
    , contract = Close
    \<rparr>
\<close>
| IfTrue:
\<open>
 \<lbrakk> fixInterval (interval tx) s = IntervalTrimmed env fixSta
 ; evalObservation env fixSta obs 
 \<rbrakk> \<Longrightarrow>
  (If obs trueC falseC, tx, s) \<rightarrow> 
    \<lparr> warnings = Set.empty
    , payments = Set.empty
    , state = s 
    \<comment> \<open>Compute transaction goes a little bit further than this, it goes until quiscent\<close>
    , contract = trueC
    \<rparr>
\<close>
| IfFalse:
\<open>
 \<lbrakk> fixInterval (interval tx) s = IntervalTrimmed env fixSta
 ; \<not> evalObservation env fixSta obs 
 \<rbrakk> \<Longrightarrow>
  (If obs trueC falseC, tx, s) \<rightarrow> 
    \<lparr> warnings = Set.empty
    , payments = Set.empty
    , state = s 
    , contract = falseC
    \<rparr>
\<close>



(* Borrowed from IMP-Hol Theory, working with a Tuple for the input is nice for using
the arrow syntax, but it doesn't work nice when you are proving things with big_step.induct
as the variables are not replaced automatically. Using the big_step_induct theory instead fixes
that. *)

lemmas small_step_induct = small_step.induct[split_format(complete)]

thm small_step.induct
thm small_step_induct

(*>*)

text 
\<open>
\begin{center}
  @{thm[mode=Rule,margin=50] CloseBS} {\sc CloseBS}
\end{center}

  \<close>

text
\<open>
\begin{center}
  @{thm[mode=Rule] IfTrue} {\sc IfTrue}
\end{center}
\<close>

text
\<open>
 
\begin{center}
  @{thm[mode=Rule,margin=100] IfFalse} {\sc IfFalse}
\end{center}
\<close>

section "Compute transaction" 

text "To prove that when execute the \<^emph>\<open>computeTransaction\<close> command the SmallStep semantics are followed, we need to
define an equivalence function between a \<^term>\<open>TransactionOutput\<close> and a \<^term>\<open>BigStepResult\<close>"
fun transactionOutputBigStep_equiv :: "TransactionOutput \<Rightarrow> SmallStepResult \<Rightarrow> bool" (infixl "\<equiv>\<^sub>\<rightarrow>" 50) where
  "TransactionError err \<equiv>\<^sub>\<rightarrow> bs = False "
| "TransactionOutput to  \<equiv>\<^sub>\<rightarrow> bs \<longleftrightarrow> 
    (txOutContract to = contract bs 
      \<and> set (txOutWarnings to) = warnings bs
      \<and> set (txOutPayments to) = payments bs
      \<and> txOutState to = state bs
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

