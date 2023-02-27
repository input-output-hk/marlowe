(*<*)
theory BigStep
  imports Semantics

begin
(*>*)

section "Big step semantics"

record BigStepResult =
  warnings :: "TransactionWarning set" 
  payments :: "Payment set" 
  state :: State


(*<*)
inductive big_step :: "(Contract \<times> Transaction \<times> State ) \<Rightarrow> BigStepResult \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
CloseBS: 
\<open>
  \<lbrakk>fixedTransaction tx s; inputs tx = [] \<rbrakk> \<Longrightarrow>
  (Close, tx, s) \<Rightarrow>
    \<lparr> warnings = Set.empty
    , payments = accountsAsPayments (accounts s)
    , state = s \<lparr> accounts := []\<rparr>
    \<rparr>
\<close>
| IfTrue:
\<open>
 \<lbrakk> fixInterval (interval tx) s = IntervalTrimmed env fixSta
 ; evalObservation env fixSta obs 
 ; (trueC, tx, fixSta) \<Rightarrow> bs
 \<rbrakk> \<Longrightarrow>
  (If obs trueC falseC, tx, s) \<Rightarrow> bs
\<close>


(* Borrowed from IMP-Hol Theory, working with a Tuple for the input is nice for using
the arrow syntax, but it doesn't work nice when you are proving things with big_step.induct
as the variables are not replaced automatically. Using the big_step_induct theory instead fixes
that. *)

lemmas big_step_induct = big_step.induct[split_format(complete)]

thm big_step_induct
thm big_step.induct

(*>*)

text 
\<open>
\begin{center}
  @{thm[mode=Rule] CloseBS} {\sc CloseBS}
\end{center}

  \<close>

text
\<open>
\begin{center}
  @{thm[mode=Rule] IfTrue} {\sc IfTrue}
\end{center}
\<close>

section "Play trace" 

text "To prove that when execute the \<^emph>\<open>playTrace\<close> command the BigStep semantics are followed, we need to
define an equivalence function between a \<^term>\<open>TransactionOutput\<close> and a \<^term>\<open>BigStepResult\<close>"
fun transactionOutputBigStep_equiv :: "TransactionOutput \<Rightarrow> BigStepResult \<Rightarrow> bool" (infixl "\<equiv>\<^sub>\<Rightarrow>" 50) where
  "TransactionError err \<equiv>\<^sub>\<Rightarrow> bs = False "
| "TransactionOutput to  \<equiv>\<^sub>\<Rightarrow> bs \<longleftrightarrow> 
    (txOutContract to = Close 
      \<and> set (txOutWarnings to) = warnings bs
      \<and> set (txOutPayments to) = payments bs
      \<and> txOutState to = state bs
    )"

(*
theorem playTraceAbidesBigStep : "(tx, s, c) \<Rightarrow> out \<Longrightarrow> playTrace 0 c tx  s c = out" 
proof (induction out   rule: big_step.induct )
  case (CloseWOAccounts s tx)
  then show ?case sorry
next
  case (CloseWAccounts s tx)
  then show ?case sorry
qed
*)
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
end

