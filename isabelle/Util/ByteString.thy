(*<*)
theory ByteString
  imports "HOL-Library.Word"
begin
(*>*)

chapter \<open>ByteString \label{sec:bytestring}\<close>

section "Definition"

text \<open>Conceptually, a \<^term>\<open>ByteString\<close> is defined as a list of 8-bit words.\<close>

datatype (plugins del: "size") ByteString = ByteString "(8 word) list"


definition emptyByteString :: "ByteString" where
"emptyByteString = ByteString []"

fun singletonByteString :: "8 word \<Rightarrow> ByteString" where
"singletonByteString w = ByteString [w]"

fun consByteString :: "8 word \<Rightarrow> ByteString \<Rightarrow> ByteString" where
"consByteString w (ByteString t) = ByteString (w # t)"

fun appendByteStrings :: "ByteString \<Rightarrow> ByteString \<Rightarrow> ByteString" where
"appendByteStrings (ByteString a) (ByteString b) = ByteString (a @ b)"

fun innerListByteString :: "ByteString \<Rightarrow> 8 word list" where
"innerListByteString (ByteString x) = x"

lemma lazyConsByteString : "consByteString w t = ByteString (w # innerListByteString t)"
  by (metis consByteString.simps innerListByteString.elims)

lemma intToWordToUint : "x \<ge> 0 \<Longrightarrow> x < 256 \<Longrightarrow> uint (word_of_int x :: 8 word) = (x :: int)"
  apply (simp only:uint_word_of_int)
  by auto

lemma appendByteStringsAssoc : "appendByteStrings (appendByteStrings x y) z = appendByteStrings x (appendByteStrings y z)"
  by (metis append.assoc appendByteStrings.simps innerListByteString.elims)

fun lengthByteString :: "ByteString \<Rightarrow> nat" where
"lengthByteString (ByteString x) = length x"

fun takeByteString :: "nat \<Rightarrow> ByteString \<Rightarrow> ByteString" where
"takeByteString n (ByteString x) = ByteString (take n x)"

fun dropByteString :: "nat \<Rightarrow> ByteString \<Rightarrow> ByteString" where
"dropByteString n (ByteString x) = ByteString (drop n x)"

lemma appendTakeDropByteString : "appendByteStrings (takeByteString n x) (dropByteString n x) = x"
  by (metis appendByteStrings.simps append_take_drop_id dropByteString.simps innerListByteString.cases takeByteString.simps)


text \<open>The \<^term>\<open>BS\<close> helper allows to create a \<^term>\<open>ByteString\<close> out of a regular \<^term>\<open>string\<close>.\<close>

fun BS :: "string \<Rightarrow> ByteString" where
  "BS str = ByteString (map of_char str)"


text \<open>For example \<^term>\<open>BS ''abc''\<close> is evaluated to @{value "BS ''abc''"}\<close>


subsection \<open>Size\<close>

instantiation ByteString :: size
begin

definition size_ByteString where
  size_ByteString_overloaded_def: "size_ByteString = lengthByteString"
instance ..

end


section \<open>Ordering\<close>

text \<open>We define the \<^term>\<open>less\<close> and \<^term>\<open>less_eq\<close> functions that provide \<^term>\<open>ord\<close>ering.\<close>

instantiation ByteString :: ord 
begin 

fun less_eq_BS' :: "(8 word) list \<Rightarrow> (8 word) list \<Rightarrow> bool" where 
"less_eq_BS' Nil Nil = True" |
"less_eq_BS' (Cons _ _) Nil = False" |
"less_eq_BS' Nil (Cons _ _) = True" |
"less_eq_BS' (Cons h1 t1) (Cons h2 t2) =
   (if h2 < h1 then False
    else (if h1 = h2 then less_eq_BS' t1 t2 else True))"

definition "a \<le> b = less_eq_BS' (innerListByteString a) (innerListByteString b)"

definition less_ByteString :: "ByteString \<Rightarrow> ByteString \<Rightarrow> bool" where
  "less_ByteString a b \<longleftrightarrow> \<not> (b \<le> a)"

(*<*)
instance proof
qed
(*>*)
end

text \<open>And we also prove that ByteString has total order.\<close>
(*<*)
lemma oneLessEqBS' : "\<not> less_eq_BS' bs2 bs1 \<Longrightarrow> less_eq_BS' bs1 bs2"
  apply (induction bs1 bs2 rule:less_eq_BS'.induct)
  apply simp_all
  by (metis order_less_imp_not_less)

lemma less_eq_BS_trans' : "less_eq_BS' x y \<Longrightarrow> less_eq_BS' y z \<Longrightarrow> less_eq_BS' x z"
  apply (induction x z arbitrary:y rule:less_eq_BS'.induct)
    apply auto
  subgoal for hx tx y
    by (metis less_eq_BS'.elims(2) list.distinct(1))
  subgoal for t1 h2 t2 y
    by (metis (mono_tags, opaque_lifting) less_eq_BS'.simps(2) less_eq_BS'.simps(4) list.exhaust not_less_iff_gr_or_eq)
  subgoal for h1 t1 h2 t2 y
    by (smt (verit, del_insts) less_eq_BS'.elims(2) list.distinct(1) list.sel(1) not_less_iff_gr_or_eq order_less_trans)
  done

lemma byteStringLessEqTwiceEq' : "less_eq_BS' x y \<Longrightarrow> less_eq_BS' y x \<Longrightarrow> x = y"
  apply (induction x y rule:less_eq_BS'.induct)
  apply auto
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  done
(*>*)

instantiation "ByteString" :: linorder
begin
instance
proof
  fix x y z :: ByteString
  show byteStringLinOrder: "x \<le> y \<or> y \<le> x"
    (*<*)using less_eq_ByteString_def oneLessEqBS' by blast(*>*)
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    (*<*)using byteStringLinOrder less_ByteString_def by presburger(*>*)
  show "x \<le> x" 
    (*<*)by (metis less_eq_ByteString_def oneLessEqBS')(*>*)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    (*<*)using less_eq_BS_trans' less_eq_ByteString_def by blast(*>*)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" 
    (*<*)by (metis byteStringLessEqTwiceEq' innerListByteString.elims less_eq_ByteString_def)(*>*)
qed
end
(*<*)
end
(*>*)




