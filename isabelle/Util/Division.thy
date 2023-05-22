\<comment> \<open>This module contains helpers around integer division\<close>
theory Division

imports Main

begin

text \<open>The \<^emph>\<open>quot\<close> operator is a form of partial division. It is built on top
of Isabelle's partial division operator but with some modifications that
affect rounding.\<close>

fun quot :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "quot" 70) where
"x quot y = (if (x < 0) = (y < 0) then x div y else -(abs x div abs y))"


text \<open>With the \<^emph>\<open>div\<close> operator, if the numerator is lower than the denominator
(in absolute), then the division is rounded to \<^term>\<open>-1\<close>. With the \<^emph>\<open>quot\<close>
operator that division is rounded to zero. For example:\<close>
proposition "2 div -3  = (-1 :: int)"
            "-2 div 3  = (-1 :: int)"
            "2 quot -3 = 0"
            "-2 quot 3 = 0"
  by simp_all

text "More generally"

lemma quot_rounds_to_zero :
  assumes "\<bar>n\<bar> < \<bar>d\<bar>"
    shows "n quot d = 0"
  using assms by auto


lemma quot_by_zero_is_zero : "n quot 0 = 0"
  by auto

lemma quotMultiplyEquivalence : "c \<noteq> 0 \<Longrightarrow> (c * a) quot (c * b) = a quot b"
  apply auto
  apply (simp_all add: mult_less_0_iff)
  apply (metis div_mult_mult1 less_irrefl mult_minus_right)
  apply (smt div_minus_minus mult_minus_right nonzero_mult_div_cancel_left zdiv_zmult2_eq)
  apply (metis div_minus_right div_mult_mult1 mult_minus_right)
  by (metis div_mult_mult1 less_irrefl mult_minus_right)

section "Unused"

text \<open>The following functions and lemmas are not used by the rest of the theories.\<close>

fun signum :: "int \<Rightarrow> int" where
"signum x = (if x > 0 then 1 else if x = 0 then 0 else -1)"

fun rem :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "rem" 70) where
"x rem y = x - (x quot y) * y"

fun quotRem :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" (infixl "quotRem" 70) where
"x quotRem y = (x quot y, x rem y)"

lemma remMultiplyEquivalence : "c \<noteq> 0 \<Longrightarrow> (c * a) rem (c * b) = c * (a rem b)"
proof -
  assume "c \<noteq> 0"
  then have "\<And>i ia. c * i quot (c * ia) = i quot ia"
    using quotMultiplyEquivalence by presburger
  then show ?thesis
    by (simp add: right_diff_distrib')
qed

lemma signEqualityPreservation : "(a :: int) \<noteq> 0 \<Longrightarrow> (b :: int) \<noteq> 0 \<Longrightarrow> (c :: int) \<noteq> 0 \<Longrightarrow> ((c * a < 0) = (c * b < 0)) = ((a < 0) = (b < 0))"
  by (smt mult_neg_pos mult_nonneg_nonneg mult_nonpos_nonpos mult_pos_neg)

lemma divMultiply : "(c :: int) \<noteq> 0 \<Longrightarrow> (c * a) div (c * b) = a div b"
  by simp
lemma divAbsMultiply : "(c :: int) \<noteq> 0 \<Longrightarrow> \<bar>c * a\<bar> div \<bar>c * b\<bar> = \<bar>a\<bar> div \<bar>b\<bar>"
  by (simp add: abs_mult)

lemma addMultiply : "\<bar>(c :: int) * a + x * (c * b)\<bar> = \<bar>c * (a + x * b)\<bar>"
  by (simp add: distrib_left mult.left_commute)

lemma addAbsMultiply : "\<bar>(c :: int) * a + x * (c * b)\<bar> = \<bar>c * (a + x * b)\<bar>"
  by (simp add: distrib_left mult.left_commute)

lemma subMultiply : "\<bar>(c :: int) * a - x * (c * b)\<bar> = \<bar>c * (a - x * b)\<bar>"
  by (simp add: mult.left_commute right_diff_distrib')

lemma ltMultiply : "(c :: int) \<noteq> 0 \<Longrightarrow> (\<bar>x\<bar> * 2 < \<bar>b\<bar>) = (\<bar>c * x\<bar> * 2 < \<bar>c * b\<bar>)"
  by (simp add: abs_mult)

lemma remMultiplySmalle_aux : "(a :: int) \<noteq> 0 \<Longrightarrow> (b :: int) \<noteq> 0 \<Longrightarrow> (c :: int) \<noteq> 0 \<Longrightarrow> (\<bar>a - a div b * b\<bar> * 2 < \<bar>b\<bar>) = (\<bar>c * a - c * a div (c * b) * (c * b)\<bar> * 2 < \<bar>c * b\<bar>)"
  apply (subst divMultiply)
  apply simp
  apply (subst subMultiply)
  using ltMultiply by blast

lemma remMultiplySmalle_aux2 : "(a :: int) \<noteq> 0 \<Longrightarrow> (b :: int) \<noteq> 0 \<Longrightarrow> (c :: int) \<noteq> 0 \<Longrightarrow> (\<bar>a + \<bar>a\<bar> div \<bar>b\<bar> * b\<bar> * 2 < \<bar>b\<bar>) = (\<bar>c * a + \<bar>c * a\<bar> div \<bar>c * b\<bar> * (c * b)\<bar> * 2 < \<bar>c * b\<bar>)"
  apply (subst divAbsMultiply)
  apply simp
  apply (subst addMultiply)
  using ltMultiply by blast

lemma remMultiplySmaller : "c \<noteq> 0 \<Longrightarrow> (\<bar>a rem b\<bar> * 2 < \<bar>b\<bar>) = (\<bar>(c * a) rem (c * b)\<bar> * 2 < \<bar>c * b\<bar>)"
  apply (cases "b = 0")
  apply simp
  apply (cases "a = 0")
  apply (simp add: mult_less_0_iff)
  apply (simp only:quot.simps rem.simps)
  apply (subst signEqualityPreservation[of a b c])
  apply simp
  apply simp
  apply simp
  apply (cases "(a < 0) = (b < 0)")
  apply (simp only:if_True refl)
  using remMultiplySmalle_aux apply blast
  apply (simp only:if_False refl)
  by (metis (no_types, opaque_lifting) diff_minus_eq_add mult_minus_left remMultiplySmalle_aux2)
end