theory OptBoundTimeInterval3
  imports Semantics
begin

text
\<open>
Represents a closed (inclusive) interval endpoint
\<close>
datatype BEndpoint =
  Unbounded
  | Bounded POSIXTime

type_synonym OptBoundTimeInterval3 = "BEndpoint \<times> BEndpoint"


fun toSet :: "OptBoundTimeInterval3 => POSIXTime set" where
   "toSet (Unbounded, Unbounded)   = {x. True}"
 | "toSet (Bounded l, Unbounded)   = {l..}"
 | "toSet (Unbounded, Bounded r) = {..r}"
 | "toSet (Bounded l, Bounded r) = {l..r}"

fun maxLow :: "BEndpoint \<Rightarrow> BEndpoint \<Rightarrow> BEndpoint" where
  "maxLow Unbounded y = y"
| "maxLow x Unbounded = x"
| "maxLow (Bounded x) (Bounded y) = Bounded (max x y)"
(*
interpretation semigroup maxLow 
  apply (unfold_locales)
  subgoal for a b c
    apply (cases a)
    apply simp
    apply (cases b)
    apply simp
    apply (cases c)
     apply simp   
    by simp
    done
*)
fun minHigh :: "BEndpoint \<Rightarrow> BEndpoint \<Rightarrow> BEndpoint" where
  "minHigh Unbounded y = y"
| "minHigh x Unbounded = x"
| "minHigh (Bounded x) (Bounded y) = Bounded (min x y)"
(*
interpretation semigroup minHigh 
  apply (unfold_locales)
  subgoal for a b c
    apply (cases a)
    apply simp
    apply (cases b)
    apply simp
    apply (cases c)
     apply simp   
    by simp
    done
*)
fun intersectInterval :: "OptBoundTimeInterval3 \<Rightarrow> OptBoundTimeInterval3 \<Rightarrow> OptBoundTimeInterval3"
where
 "intersectInterval (low1, high1) (low2, high2)
    = (maxLow low1 low2, minHigh high1 high2)"
(*
interpretation semigroup "intersectInterval" 
  apply (unfold_locales)
  subgoal for a b c
    apply (cases a)
    subgoal for l1 h1
    apply (cases b)
      subgoal for l2 h2
        apply (cases c)
        subgoal for l3 h3
          apply auto
          apply (cases l1)
            apply simp
          apply (cases l2)         
            apply simp
          apply (cases l3)
            apply simp
           apply simp  
          apply (cases h1)
            apply simp
          apply (cases h2)         
            apply simp
          apply (cases h3)
           apply simp
          by simp 
        done
      done
    done
  done
*)
(*
interpretation abel_semigroup "intersectInterval" 
  apply unfold_locales
  subgoal for a b
    apply (cases a)
    a
*)

(*
lemma zzz4 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet ((Bounded l1), b)"
  by (cases b) auto
*)

lemma a1: " x \<in> toSet (maxLow l1 l2, r) \<Longrightarrow> x \<in> toSet (l1, r)"
  apply (cases l1)
   apply auto
   apply (metis OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.toSet.simps(1) OptBoundTimeInterval3.toSet.simps(3) OptBoundTimeInterval3.toSet.simps(4) atLeastAtMost_iff atMost_iff mem_Collect_eq)
  apply (cases l2)
  apply auto 
  by (metis Lattices.linorder_class.max.bounded_iff OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.toSet.simps(2) OptBoundTimeInterval3.toSet.simps(4) atLeastAtMost_iff atLeast_iff)

lemma a2: " x \<in> toSet (maxLow l1 l2, r) \<Longrightarrow> x \<in> toSet (l2, r)"
  apply (cases l1)
  by auto (smt (verit, best) OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.maxLow.simps(1) OptBoundTimeInterval3.maxLow.simps(3) a1)

lemma a3: " x \<in> toSet (l, minHigh r1 r2) \<Longrightarrow> x \<in> toSet (l, r1)"
  apply (induction r1 arbitrary: l)
   apply auto
     apply (cases r2)
    apply auto  
   apply (metis OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.toSet.simps(1) OptBoundTimeInterval3.toSet.simps(2) OptBoundTimeInterval3.toSet.simps(4) UNIV_I UNIV_def atLeastAtMost_iff atLeast_iff)
  by (smt (verit, best) OptBoundTimeInterval3.BEndpoint.distinct(1) OptBoundTimeInterval3.BEndpoint.inject OptBoundTimeInterval3.minHigh.elims OptBoundTimeInterval3.toSet.elims Pair_inject atLeastAtMost_iff atMost_iff)


lemma a4: " x \<in> toSet (l, minHigh r1 r2) \<Longrightarrow> x \<in> toSet (l, r2)"
  apply (cases r1)
   apply auto
  by (smt (verit, best) OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.minHigh.simps(1) OptBoundTimeInterval3.minHigh.simps(3) a3)


lemma belongsToIntersectBelongsToSetA: "x \<in> toSet (intersectInterval a b) \<Longrightarrow> x \<in> toSet a"
  by (metis OptBoundTimeInterval3.intersectInterval.simps a1 a3 surjective_pairing)

lemma b1 [simp]: "x \<in> toSet (l1, r) \<and> x \<in> toSet (l2, r) \<Longrightarrow> x \<in> toSet (maxLow l1 l2, r)" 
  apply (cases l1)
   apply auto
  apply (cases l2)
   apply auto
  by linarith

lemma b2 [simp]: "x \<in> toSet (l, r1) \<and> x \<in> toSet (l, r2) \<Longrightarrow> x \<in> toSet (l, minHigh r1 r2)" 
  apply (cases r1)
   apply auto
  apply (cases r2)
   apply auto
  by linarith

lemma c1: " x \<in> toSet (l1, r1) \<and> x \<in> toSet (l2, r2) \<Longrightarrow> x \<in> toSet (maxLow l1 l2, minHigh r1 r2)"
  apply (induction l1 arbitrary: r1)
   apply (auto)
   apply (metis OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.minHigh.simps(1) OptBoundTimeInterval3.toSet.simps(2) OptBoundTimeInterval3.toSet.simps(3) OptBoundTimeInterval3.toSet.simps(4) a3 atLeastAtMost_iff atLeast_iff atMost_iff b2)
  apply (induction l2 arbitrary: r2)
   apply auto
  apply (metis OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.toSet.simps(2) OptBoundTimeInterval3.toSet.simps(3) OptBoundTimeInterval3.toSet.simps(4) atLeastAtMost_iff atLeast_iff atMost_iff b2)
  by (metis Lattices.linorder_class.max.absorb_iff2 Lattices.linorder_class.max.commute OptBoundTimeInterval3.BEndpoint.exhaust OptBoundTimeInterval3.toSet.simps(2) OptBoundTimeInterval3.toSet.simps(4) atLeastAtMost_iff atLeast_iff b2 nle_le)  

theorem intersectIntervalIsIntersect: "toSet (intersectInterval a b) = toSet a \<inter> toSet b"
  apply (cases a)
    apply (cases b)
  apply auto
  using a1 a3 apply blast
  using a2 a4 apply blast
  using c1 by presburger


fun ttoSet :: "TimeInterval \<Rightarrow> POSIXTime set" where
  "ttoSet (l, r) = {l..r}"


end