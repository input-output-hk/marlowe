theory Serialisation
  imports "HOL-Word.Word"
begin

type_synonym ByteString = "(8 word) list"

fun positiveIntToByteString :: "int \<Rightarrow> ByteString" where
"positiveIntToByteString x =
  (if x < 128 then [word_of_int x] else (word_of_int ((x mod 128) + 128)) # positiveIntToByteString (x div 128))"

fun byteStringToPositiveInt :: "ByteString \<Rightarrow> (int \<times> ByteString) option" where
"byteStringToPositiveInt Nil = None" |
"byteStringToPositiveInt (Cons xw rest) =
  (let x = uint xw in
    (if x < 128
     then (Some (x, rest))
     else (case byteStringToPositiveInt rest of
             None \<Rightarrow> None
           | Some (y, extra) \<Rightarrow> Some ((x - 128) + 128 * y, extra))))"

lemma intToWordToUint : "x \<ge> 0 \<Longrightarrow> x < 256 \<Longrightarrow> uint (word_of_int x :: 8 word) = (x :: int)"
  apply (simp only:uint_word_of_int)
  by auto

lemma smallerIntInductionRestrictedToNat : "(\<And> x :: nat. (\<And> y :: nat . y < x \<Longrightarrow> P (int y)) \<Longrightarrow> P (int x)) \<Longrightarrow> P (int z)"
  apply (induct rule:Orderings.wellorder_class.less_induct)
  by auto

lemma smallerIntInduction : "(\<And> x :: int. x \<ge> 0 \<Longrightarrow> (\<And> y :: int . 0 \<le> y \<Longrightarrow> y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> z \<ge> 0 \<Longrightarrow> P z"
  apply (cases z)
  subgoal for n
    by (metis (mono_tags) nat_int nat_less_iff of_nat_0_le_iff smallerIntInductionRestrictedToNat zero_le_imp_eq_int)
  by linarith

lemma positiveIntToByteStringToPositiveInt_inductionStep : "0 \<le> x \<Longrightarrow> (\<And>ya. 0 \<le> ya \<Longrightarrow> ya < x \<Longrightarrow> byteStringToPositiveInt (positiveIntToByteString ya @ y) = Some (ya, y))
                                                                  \<Longrightarrow> byteStringToPositiveInt (positiveIntToByteString x @ y) = Some (x, y)"
  apply (cases "x < 128")
  by (simp_all add:Let_def uint_word_of_int)

lemma positiveIntToByteStringToPositiveInt : "(x :: int) \<ge> 0 \<Longrightarrow> byteStringToPositiveInt ((positiveIntToByteString x) @ y) = Some (x, y)"
  apply (rule smallerIntInduction[of "\<lambda> x. byteStringToPositiveInt (positiveIntToByteString x @ y) = Some (x, y)"])
  using positiveIntToByteStringToPositiveInt_inductionStep apply blast
  by simp

fun intToByteString :: "int \<Rightarrow> ByteString" where
"intToByteString x = (if x \<ge> 0 then positiveIntToByteString (x * 2) else positiveIntToByteString (- (x * 2 + 1)))"

fun byteStringToInt :: "ByteString \<Rightarrow> (int \<times> ByteString) option" where
"byteStringToInt x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, extra) \<Rightarrow> Some (if (y mod 2 = 0) then y div 2 else (- (y div 2 + 1)), extra))"

lemma intToByteStringToInt : "byteStringToInt ((intToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  by (simp_all del:byteStringToPositiveInt.simps positiveIntToByteString.simps add:positiveIntToByteStringToPositiveInt)

fun addByteString :: "ByteString \<Rightarrow> ByteString \<Rightarrow> ByteString" where
"addByteString bs1 bs2 = positiveIntToByteString (int (length bs1)) @ bs1 @ bs2"

fun getByteString :: "ByteString \<Rightarrow> (ByteString \<times> ByteString) option" where
"getByteString bs =
  (case byteStringToPositiveInt bs of
     Some (val, rest) \<Rightarrow> if int (length rest) < val
                         then None
                         else Some (take (nat val) rest, drop (nat val) rest)
   | None \<Rightarrow> None
  )"

lemma addAndGetByteString : "getByteString (addByteString x y) = Some (x, y)"
  by (simp del:positiveIntToByteString.simps add:positiveIntToByteStringToPositiveInt)


fun less_eq_BS :: "ByteString \<Rightarrow> ByteString \<Rightarrow> bool" where
"less_eq_BS Nil Nil = True" |
"less_eq_BS (Cons _ _) Nil = False" |
"less_eq_BS Nil (Cons _ _) = True" |
"less_eq_BS (Cons h1 t1) (Cons h2 t2) =
   (if h2 < h1 then False
    else (if h1 = h2 then less_eq_BS t1 t2 else True))"

fun less_BS :: "ByteString \<Rightarrow> ByteString \<Rightarrow> bool" where
"less_BS a b = (\<not> (less_eq_BS b a))"

lemma oneLessEqBS : "\<not> less_eq_BS bs2 bs1 \<Longrightarrow> less_eq_BS bs1 bs2"
  apply (induction bs1 bs2 rule:less_eq_BS.induct)
  apply simp_all
  by (metis le_less not_le)

lemma lineaBS : "less_eq_BS x y \<or> less_eq_BS y x"
  using oneLessEqBS by blast


lemma byteStringOrder : "less_eq_BS x y \<Longrightarrow> less_eq_BS y z \<Longrightarrow> less_eq_BS x z"
  apply (induction x z arbitrary:y rule:less_eq_BS.induct)
    apply auto
  subgoal for hx tx y
    by (metis less_eq_BS.elims(2) list.distinct(1))
  subgoal for t1 h2 t2 y
    by (metis (full_types) byteStringToPositiveInt.cases less_eq_BS.simps(2) less_eq_BS.simps(4) not_less_iff_gr_or_eq)
  subgoal for h1 t1 h2 t2 y
    by (metis (mono_tags, hide_lams) \<open>\<And>ya tx hx. \<lbrakk>less_eq_BS (hx # tx) ya; less_eq_BS ya []\<rbrakk> \<Longrightarrow> False\<close> byteStringToPositiveInt.cases less_eq_BS.simps(4) not_le not_less_iff_gr_or_eq order_trans)
  done

lemma byteStringLessEqTwiceEq : "less_eq_BS x y \<Longrightarrow> less_eq_BS y x \<Longrightarrow> x = y"
  apply (induction x y rule:less_eq_BS.induct)
  apply auto
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  done

end