theory OptBoundTimeInterval2
  imports Semantics
begin 

text
\<open>
\<^item> Totally unbound: (-\<infinity>, \<infinity>)
\<^item> Left bound [low, \<infinity>)
\<^item> Right bound (-\<infinity>, high]
\<^item> Bound [low, high].
\<close>

datatype OptBoundTimeInterval2 =
   Unbound
   | LeftBound POSIXTime
   | RightBound POSIXTime
   | Bound POSIXTime POSIXTime

definition s1 :: "int set" where
 "s1 = {3}"

value \<open>2 \<in> s1\<close>
value \<open>3 \<in> s1\<close>
value \<open>4 \<in> s1\<close>

definition s2 :: "int set" where
 "s2 = {..3}"

definition xx :: "int list \<Rightarrow> int \<Rightarrow> bool"
  where
  [code_abbrev]: "xx xs x \<longleftrightarrow> x \<in> set xs"

lemma "(n :: int) \<in> s2 \<longleftrightarrow> (n :: int) \<le> 3"
  apply (simp add: s2_def)
  done

proposition "3 \<in> s2"
  by (simp only: s2_def) auto


fun toSet :: "OptBoundTimeInterval2 => POSIXTime set" where
   "toSet Unbound   = {x. True}"
 | "toSet (LeftBound l) = {l..}"
 | "toSet (RightBound r) = {..r}"
 | "toSet (Bound l r) = {l..r}"

fun intersectInterval :: "OptBoundTimeInterval2 \<Rightarrow> OptBoundTimeInterval2 \<Rightarrow> OptBoundTimeInterval2"
  where
  "intersectInterval Unbound x = x"
| "intersectInterval x Unbound  = x"
| "intersectInterval (LeftBound l1) (LeftBound l2) = LeftBound (max l1 l2)"
| "intersectInterval (LeftBound l) (RightBound r) = Bound l r"
| "intersectInterval (LeftBound l1) (Bound l2 r2) = Bound (max l1 l2) r2"
| "intersectInterval (RightBound r) (LeftBound l) = Bound l r"
| "intersectInterval (RightBound r1) (RightBound r2) = RightBound (min r1 r2)"
| "intersectInterval (RightBound r1) (Bound l2 r2) = Bound l2 (min r1 r2)"
| "intersectInterval (Bound l1 r1) (LeftBound l2) = Bound (max l1 l2) r1"
| "intersectInterval (Bound l1 r1) (RightBound r2) = Bound l1 (min r1 r2)"
| "intersectInterval (Bound l1 r1) (Bound l2 r2) = Bound (max l1 l2) (min r1 r2)"

print_locale! semigroup
(*
interpretation semigroup "intersectInterval"
  apply (unfold_locales)
  subgoal for a b c
  apply (induction a)
  print_context
  print_methods
  apply (simp add: Groups.semigroup.intro)
proof

  apply (unfold_locales)
  sledgehammer
  apply (induct intersectInterval.induct  a)
  print_state
  apply (induct_tac a)
  apply (cut_tac semigroup)
proof

  print_state
  apply (cut_tac assoc)
proof
  assume "\<And>a b c. intersectInterval (intersectInterval a b) c = intersectInterval a (intersectInterval b c)"




  by auto
*)

thm monoid_def
thm monoid.left_neutral
thm monoid.right_neutral


lemma xxx [simp]: "\<exists> x. x \<le> r \<and> x \<in> toSet optInt \<longrightarrow> optInt = RightBound r"
  by (smt (z3))

lemma yyy [simp]: "\<exists> x. x \<ge> l \<and> x \<in> toSet optInt \<longrightarrow> optInt = LeftBound l"
  by (smt (z3))

lemma bbb [simp]: "\<exists> e. e < l \<and> e > r \<and> e \<notin> toSet optInt \<longrightarrow> optInt = Bound l r"
  by blast

lemma zzz [simp]: "\<exists>x. x \<in> toSet optInt \<longleftrightarrow> optInt = Unbound"
  apply (cases optInt)
     apply auto[1]
    apply (metis Semantics.toSet.simps(1) Semantics.toSet.simps(2) UNIV_I UNIV_def atLeast_iff yyy)
   apply (metis Semantics.toSet.simps(1) Semantics.toSet.simps(3) UNIV_I UNIV_def atMost_iff xxx)
  by (metis Int_iff Semantics.toSet.simps(1) Semantics.toSet.simps(4) UNIV_I UNIV_def atLeastAtMost_def atMost_iff xxx)

lemma z1 [simp]: "\<exists> l. l \<in> toSet (LeftBound l1) \<longrightarrow> l \<le> l1"
  by auto

lemma z2 [simp]: "\<exists> r. r \<in> toSet (RightBound r1) \<longrightarrow> r \<ge> r1"
  by auto

lemma z3 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet (LeftBound l1)"
  by simp

lemma zzz4 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet (intersectInterval (LeftBound l1) b)"
  by (cases b) auto

lemma aaa4 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet (intersectInterval a (LeftBound l1))"
  by (cases a) auto

lemma zzz5 [simp]: "\<nexists> r. r > r1 \<and> r \<in> toSet (intersectInterval (RightBound r1) b)"
  by (cases b) auto

lemma aaa5 [simp]: "\<nexists> r. r > r1 \<and> r \<in> toSet (intersectInterval a (RightBound r1))"
  by (cases a) auto

lemma zzz6 [simp]: "\<nexists> r. r > r1 \<and> r \<in> toSet (intersectInterval (Bound l r1) b)"
  by (cases b) auto

lemma aaa6 [simp]: "\<nexists> r. r > r1 \<and> r \<in> toSet (intersectInterval a (Bound l r1))"
  by (cases a) auto

lemma zzz7 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet (intersectInterval (Bound l1 r) b)"
  by (cases b) auto


lemma aaa7 [simp]: "\<nexists> l. l < l1 \<and> l \<in> toSet (intersectInterval a (Bound l1 r))"
  by (cases a) auto

lemma ppp1: "intersectInterval a Unbound = a"
  apply (cases a)
  by auto

lemma ppp2: "intersectInterval (LeftBound l) a = intersectInterval a (LeftBound l)"
  apply (cases a)

     apply simp

    apply simp

  using Semantics.intersectInterval.simps(6) Semantics.intersectInterval.simps(8) apply presburger
  by simp

lemma ppp3:  "intersectInterval (RightBound r) a = intersectInterval a (RightBound r)"
  apply (cases a)
     apply auto
  done

lemma ppp4:  "intersectInterval (Bound l r) a = intersectInterval a (Bound l r)"
  apply (cases a)
     apply auto
  done

lemma intersectComm: "intersectInterval a b = intersectInterval b a"
  apply (induction a arbitrary: b)
     apply auto
     apply (metis Semantics.intersectInterval.simps(1) Semantics.intersectInterval.simps(2) Semantics.intersectInterval.simps(3) Semantics.intersectInterval.simps(4) Semantics.toSet.elims)
    apply (simp add: ppp2)
     apply (simp add: ppp3)
  by (simp add: ppp4)

lemma ooo: "x \<in> toSet (Bound l1 r1) \<and> x \<in> toSet (Bound l2 r2) \<longrightarrow> x \<in> toSet (intersectInterval (Bound l1 r1) (Bound l2 r2))"
  by auto


lemma hhh[simp]: " x \<in> toSet (intersectInterval a b) \<Longrightarrow> x \<in> toSet a"
  apply (cases a)
       apply simp
    apply (metis Semantics.toSet.simps(2) atLeast_iff linorder_le_less_linear zzz4)

   apply (metis Semantics.toSet.simps(3) atMost_iff linorder_le_less_linear zzz5)
  apply simp
  apply (cases b)
  by  auto

lemma hhh2: " x \<in> toSet (intersectInterval a b) \<Longrightarrow> x \<in> toSet b"
  apply (cases b)
     apply simp
    apply auto

     apply (metis intersectComm linorder_le_less_linear zzz4)

    apply (metis intersectComm less_le_not_le nle_le zzz5)

   apply (metis intersectComm linorder_le_less_linear zzz7)
  by (metis intersectComm linorder_le_less_linear zzz6)


lemma lolo: "j \<le> x \<Longrightarrow> j \<in> toSet b \<Longrightarrow> j \<in> toSet (intersectInterval (RightBound x) b)"
  apply (cases b)
  apply auto
  done

lemma lolo2: "\<And>x1 x2a j. x1 \<le> j \<Longrightarrow> j \<le> x2a \<Longrightarrow> j \<in> toSet b \<Longrightarrow> j \<in> toSet (intersectInterval (Bound x1 x2a) b)"
  apply (cases b)
  apply auto
  done

lemma hhh3: "j \<in> toSet a \<and> j \<in> toSet b \<Longrightarrow> j \<in> toSet (intersectInterval a b)"
  apply (induction a arbitrary: j )
     apply auto
    apply (cases b)
  apply auto

  using lolo apply blast
  using lolo2 by blast


theorem intersectIntervalIsIntersect: "toSet (intersectInterval a b) = toSet a \<inter> toSet b"
  apply auto
  using hhh2 apply blast
  using hhh3 by blast

(* calculateNonAmigousInterval *)

fun calculateTimeInterval2 :: "int option \<Rightarrow> POSIXTime \<Rightarrow> Contract \<Rightarrow> OptBoundTimeInterval2"
where
"calculateTimeInterval2 _ _ Close = Unbound" |
"calculateTimeInterval2 n t (Pay _ _ _ _ c) = calculateTimeInterval2 n t c" |
"calculateTimeInterval2 n t (If _ ct cf) = intersectInterval (calculateTimeInterval2 n t ct)
                                                           (calculateTimeInterval2 n t cf)" |
"calculateTimeInterval2 n t (When Nil timeout tcont) =
  (if t < timeout
   then RightBound (timeout - 1)
   else intersectInterval (LeftBound timeout) (calculateTimeInterval2 n t tcont))" |
"calculateTimeInterval2 n t (When (Cons (Case _ cont ) tail) timeout tcont) =
  (if gtIfNone n 0
   then intersectInterval (calculateTimeInterval2 (subIfSome n 1) t cont)
                         (calculateTimeInterval2 n t (When tail timeout tcont))
   else calculateTimeInterval2 n t (When tail timeout tcont))" |
"calculateTimeInterval2 n t (Let _ _ c) = calculateTimeInterval2 n t c" |
"calculateTimeInterval2 n t (Assert _ c) = calculateTimeInterval2 n t c"

\<comment> \<open>Esto tiene problemas al tratar de evaluarse, pero permite razonarse con proposiciones.\<close>
fun setFromContract :: "Contract \<Rightarrow> POSIXTime set" where
  "setFromContract Close = {2}"
| "setFromContract _ = {..3}"

proposition "c \<noteq> Close  \<Longrightarrow> 1 \<in> setFromContract c "
  apply (cases c)
  apply meson
  apply auto
  done

end