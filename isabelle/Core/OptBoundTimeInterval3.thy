theory OptBoundTimeInterval3
  imports SemanticsTypes
begin

section "Time Interval"
text
\<open>
A BEndpoint represents either an Unbounded (-\<infinity> or \<infinity>) endpoint or a closed bounded (inclusive)
endpoint.
\<close>
datatype BEndpoint =
  Unbounded
  | Bounded POSIXTime

text
\<open>
An Optionally bounded TimeInterval, is a normal TimeInterval  that might be unbounded on the
left or right.
\<close>
type_synonym OptBoundTimeInterval = "BEndpoint \<times> BEndpoint"

text
\<open>
We can think of an \<^emph>\<open>OptBoundTimeInterval\<close> as sets with four possible options:
\<^item> Totally unbound: (-\<infinity>, \<infinity>)
\<^item> Left bound [low, \<infinity>)
\<^item> Right bound (-\<infinity>, high]
\<^item> Bound [low, high].
\<close>
fun bToSet :: "OptBoundTimeInterval => POSIXTime set" where
   "bToSet (Unbounded, Unbounded)   = {x. True}"
 | "bToSet (Bounded l, Unbounded)   = {l..}"
 | "bToSet (Unbounded, Bounded r) = {..r}"
 | "bToSet (Bounded l, Bounded r) = {l..r}"


subsection "Interval intesection"

text
\<open>
The interval intersection is achieved by calculating the maximum lower bound and the minimum
higher bound, favouring Bounded to Unbounded endpoits.
\<close>
fun maxLow :: "BEndpoint \<Rightarrow> BEndpoint \<Rightarrow> BEndpoint" where
  "maxLow Unbounded y = y"
| "maxLow x Unbounded = x"
| "maxLow (Bounded x) (Bounded y) = Bounded (max x y)"


fun minHigh :: "BEndpoint \<Rightarrow> BEndpoint \<Rightarrow> BEndpoint" where
  "minHigh Unbounded y = y"
| "minHigh x Unbounded = x"
| "minHigh (Bounded x) (Bounded y) = Bounded (min x y)"

fun intersectInterval :: "OptBoundTimeInterval \<Rightarrow> OptBoundTimeInterval \<Rightarrow> OptBoundTimeInterval"
where
 "intersectInterval (low1, high1) (low2, high2)
    = (maxLow low1 low2, minHigh high1 high2)"


subsubsection "Associativity"
text
\<open>
Every function related to Interval Intersection is associative
\<close>

lemma maxLow_assoc [simp]: "maxLow (maxLow a b) c = maxLow a (maxLow b c)"
(*<*)
  apply (cases a)
   apply simp
  apply (cases b)
   apply simp
  apply (cases c)
  by auto
(*>*)

lemma minHigh_assoc [simp]: "minHigh (minHigh a b) c = minHigh a (minHigh b c)"
(*<*)
  apply (cases a)
   apply simp
    apply (cases b)
   apply simp
  apply (cases c)
  by auto
(*>*)

interpretation semigroup "intersectInterval"
(*<*)
  apply (unfold_locales)
  subgoal for a b c
    by (metis OptBoundTimeInterval3.intersectInterval.simps maxLow_assoc minHigh_assoc surj_pair)
  done
(*>*)

subsubsection "Commutative"
text
\<open>
Every function related to Interval Intersection is commutative
\<close>

lemma maxLow_comm [simp]: "maxLow a b = maxLow b a"
  (*<*)
  apply (cases a)
  apply (metis OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.maxLow.simps(1) OptBoundTimeInterval3.maxLow.simps(2))
   apply auto
   apply (cases b)
  by auto
  (*>*)

lemma minHigh_comm [simp]: "minHigh a b = minHigh b a"
  (*<*)
  apply (cases a)
  apply (metis OptBoundTimeInterval3.BEndpoint.distinct(1) OptBoundTimeInterval3.minHigh.elims)
   apply auto
   apply (cases b)
  by auto
  (*>*)

interpretation abel_semigroup "intersectInterval"
  (*<*)
  apply unfold_locales
  subgoal for a b
    by (metis (no_types, opaque_lifting) OptBoundTimeInterval3.intersectInterval.elims fst_conv maxLow_comm minHigh_comm snd_conv)
  done
  (*>*)


subsubsection "intersectInterval is the same as \<inter>"
text
\<open>
This section proves that the function \<^emph>\<open>intersectInterval\<close> behaves the same as set intersection. In order to
prove that theorem we have the following lemmas
\<close>
lemma (*<*)belongsToSubBelongsToSet_low_1:(*>*)
  "x \<in> bToSet (maxLow l1 l2, r) \<Longrightarrow> x \<in> bToSet (l1, r)"

(*<*)
  apply (cases l1)
   apply auto
   apply (metis BEndpoint.exhaust bToSet.simps(1) bToSet.simps(3) bToSet.simps(4) atLeastAtMost_iff atMost_iff mem_Collect_eq)
  apply (cases l2)
  apply auto
  by (metis Lattices.linorder_class.max.bounded_iff BEndpoint.exhaust bToSet.simps(2) bToSet.simps(4) atLeastAtMost_iff atLeast_iff)
(*>*)

lemma (*<*)belongsToSubBelongsToSet_low_2:(*>*)
  "x \<in> bToSet (maxLow l1 l2, r) \<Longrightarrow> x \<in> bToSet (l2, r)"

(*<*)
  apply (cases l1)
  by auto (smt (verit, best) BEndpoint.exhaust maxLow.simps(1) maxLow.simps(3) belongsToSubBelongsToSet_low_1)
(*>*)

lemma (*<*)belongsToSubBelongsToSet_high_1:(*>*)
  "x \<in> bToSet (l, minHigh r1 r2) \<Longrightarrow> x \<in> bToSet (l, r1)"

(*<*)
  apply (induction r1 arbitrary: l)
   apply auto
     apply (cases r2)
    apply auto
   apply (metis BEndpoint.exhaust bToSet.simps(1) bToSet.simps(2) bToSet.simps(4) UNIV_I UNIV_def atLeastAtMost_iff atLeast_iff)
  by (smt (verit, best) BEndpoint.distinct(1) BEndpoint.inject minHigh.elims bToSet.elims Pair_inject atLeastAtMost_iff atMost_iff)
(*>*)

lemma (*<*)belongsToSubBelongsToSet_high_2:(*>*)
  "x \<in> bToSet (l, minHigh r1 r2) \<Longrightarrow> x \<in> bToSet (l, r2)"

(*<*)
  apply (cases r1)
   apply auto
  by (smt (verit, best) BEndpoint.exhaust minHigh.simps(1) minHigh.simps(3) belongsToSubBelongsToSet_high_1)
(*>*)

lemma (*<*)belongsToSubSet_BelongsToMaxLowSet [simp]:(*>*)
  "x \<in> bToSet (l1, r) \<and> x \<in> bToSet (l2, r) \<Longrightarrow> x \<in> bToSet (maxLow l1 l2, r)"

(*<*)
  apply (cases l1)
   apply auto
  apply (cases l2)
   apply auto
  by linarith
(*>*)

lemma (*<*)belongsToSubSet_BelongsToMinHighSet [simp]:(*>*)
  "x \<in> bToSet (l, r1) \<and> x \<in> bToSet (l, r2) \<Longrightarrow> x \<in> bToSet (l, minHigh r1 r2)"

(*<*)
  apply (cases r1)
   apply auto
  apply (cases r2)
   apply auto
  by linarith
(*>*)

lemma (*<*)belongsToSubSet_BelongsToSet:(*>*)
 "x \<in> bToSet (l1, r1) \<and> x \<in> bToSet (l2, r2) \<Longrightarrow> x \<in> bToSet (maxLow l1 l2, minHigh r1 r2)"

(*<*)
  apply (induction l1 arbitrary: r1)
   apply (auto)
   apply (metis BEndpoint.exhaust minHigh.simps(1) bToSet.simps(2) bToSet.simps(3) bToSet.simps(4) belongsToSubBelongsToSet_high_1 atLeastAtMost_iff atLeast_iff atMost_iff belongsToSubSet_BelongsToMinHighSet)
  apply (induction l2 arbitrary: r2)
   apply auto
  apply (metis BEndpoint.exhaust bToSet.simps(2) bToSet.simps(3) bToSet.simps(4) atLeastAtMost_iff atLeast_iff atMost_iff belongsToSubSet_BelongsToMinHighSet)
  by (metis Lattices.linorder_class.max.absorb_iff2 Lattices.linorder_class.max.commute BEndpoint.exhaust bToSet.simps(2) bToSet.simps(4) atLeastAtMost_iff atLeast_iff belongsToSubSet_BelongsToMinHighSet nle_le)
(*>*)

theorem (*<*)intersectIntervalIsIntersect:(*>*)
  "bToSet (intersectInterval a b) = bToSet a \<inter> bToSet b"

(*<*)
  apply (cases a)
    apply (cases b)
  apply auto
  using belongsToSubBelongsToSet_low_1 belongsToSubBelongsToSet_high_1 apply blast
  using belongsToSubBelongsToSet_low_2 belongsToSubBelongsToSet_high_2 apply blast
  using belongsToSubSet_BelongsToSet by presburger
(*>*)


subsection "In interval"
fun ttoSet :: "TimeInterval \<Rightarrow> POSIXTime set" where
  "ttoSet (l, r) = {l..r}"


end