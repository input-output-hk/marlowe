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
end