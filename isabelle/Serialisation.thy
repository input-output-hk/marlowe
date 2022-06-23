theory Serialisation
  imports "HOL-Library.Word"
begin

type_synonym ByteString = "(8 word) list"

lemma intToWordToUint : "x \<ge> 0 \<Longrightarrow> x < 256 \<Longrightarrow> uint (word_of_int x :: 8 word) = (x :: int)"
  apply (simp only:uint_word_of_int)
  by auto

fun positiveIntToByteString :: "int \<Rightarrow> ByteString" where
"positiveIntToByteString x =
  (if x < 128 then [word_of_int x] else (word_of_int ((x mod 128) + 128)) # positiveIntToByteString ((x div 128) - 1))"

fun byteStringToPositiveInt :: "ByteString \<Rightarrow> (int \<times> ByteString) option" where
"byteStringToPositiveInt Nil = None" |
"byteStringToPositiveInt (Cons xw rest) =
  (let x = uint xw in
    (if x < 128
     then (Some (x, rest))
     else (case byteStringToPositiveInt rest of
             None \<Rightarrow> None
           | Some (y, extra) \<Rightarrow> Some ((x - 128) + 128 * (y + 1), extra))))"

lemma smallerIntInductionRestrictedToNat : "(\<And> x :: nat. (\<And> y :: nat . y < x \<Longrightarrow> P (int y)) \<Longrightarrow> P (int x)) \<Longrightarrow> P (int z)"
  apply (induct rule:Orderings.wellorder_class.less_induct)
  by auto

lemma smallerIntInduction : "(\<And> x :: int. x \<ge> 0 \<Longrightarrow> (\<And> y :: int . 0 \<le> y \<Longrightarrow> y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> z \<ge> 0 \<Longrightarrow> P z"
  apply (cases z)
  subgoal for n
    
    by (metis (mono_tags) nat_int nat_less_iff of_nat_0_le_iff smallerIntInductionRestrictedToNat zero_le_imp_eq_int)
  by linarith

lemma fold_sig_bit_in_word_of_int : "word_of_int (x mod 128) + 128 = word_of_int (x mod 128 + 128)"
  by auto

lemma positiveIntToByteStringToPositiveInt_inductionStep : "0 \<le> (x :: int) \<Longrightarrow> (\<And>ya. 0 \<le> ya \<Longrightarrow> ya < x \<Longrightarrow> byteStringToPositiveInt (positiveIntToByteString ya @ y) = Some (ya, y))
                                                                  \<Longrightarrow> byteStringToPositiveInt (positiveIntToByteString x @ y) = Some (x, y)"
  apply (cases "x < 128")
  apply (simp add:take_bit_eq_mod intToWordToUint Let_def)
  apply (simp only:positiveIntToByteString.simps[of x] if_False intToWordToUint)
  apply (simp del:positiveIntToByteString.simps add:Let_def intToWordToUint positiveIntToByteString.simps[of "-1"] )
  apply (simp only:fold_sig_bit_in_word_of_int intToWordToUint)
  by simp

theorem positiveIntToByteStringToPositiveInt : "(x :: int) \<ge> 0 \<Longrightarrow> byteStringToPositiveInt ((positiveIntToByteString x) @ y) = Some (x, y)"
  apply (rule smallerIntInduction[of "\<lambda> x. byteStringToPositiveInt (positiveIntToByteString x @ y) = Some (x, y)"])
  using positiveIntToByteStringToPositiveInt_inductionStep apply blast
  by simp

lemma byteStringToPositiveIntIsPositive : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow> a \<ge> 0"
  apply (induction x arbitrary:a b rule:byteStringToPositiveInt.induct)
  apply simp
  subgoal for xw rest a b
    apply (cases "uint xw < 128")
    apply auto
    apply (cases "byteStringToPositiveInt rest")
    by auto
  done

lemma unitRestoration : "a \<ge> 0 \<Longrightarrow> xh \<ge> 128 \<Longrightarrow> xh < 256 \<Longrightarrow> (xh + 128 * aaa) mod 128 + 128 = (xh :: int)"
  apply simp
  by (smt (z3) Euclidean_Division.pos_mod_bound mod_double_modulus mod_pos_pos_trivial)

lemma inductiveStepInjection_aux : "Some (xh - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow> xh < 256 \<Longrightarrow> xh \<ge> (128 :: int) \<Longrightarrow>
                                    byteStringToPositiveInt xt = Some (aaa, aab) \<Longrightarrow> a \<ge> 128 \<Longrightarrow> byteStringToPositiveInt xt = Some (a div 128 - 1, b)"
  by auto

lemma inductiveStepInjection_aux2 : "(\<And>a b. byteStringToPositiveInt xt = Some (a, b) \<Longrightarrow> positiveIntToByteString a @ b = xt) \<Longrightarrow>
    Some (uint (xh :: 8 word) - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow> uint xh \<ge> 128 \<Longrightarrow> byteStringToPositiveInt xt = Some aa \<Longrightarrow> aa = (aaa, aab) \<Longrightarrow> a \<ge> 128 \<Longrightarrow> positiveIntToByteString (a div 128 - 1) @ b = xt"
  subgoal premises fact
    apply (rule fact(1))
    apply (rule inductiveStepInjection_aux[of "uint xh" aaa aab a b xt])
    using fact(2) apply blast
  apply (cases "xh")
       apply auto
    subgoal for n2
      by (simp add: intToWordToUint take_bit_eq_mod)
      apply (simp add: fact(3))
     apply (simp add: fact(4) fact(5))
    by (simp add: fact(6))
  done

lemma splitAnd1 : "b \<Longrightarrow> c \<Longrightarrow> b \<and> c"
  by simp

lemma splitAnd2 : "(a \<Longrightarrow> b) \<Longrightarrow> (a \<Longrightarrow> c) \<Longrightarrow> a \<longrightarrow> b \<and> c"
  by simp

lemma nat_mod_id : "(n :: nat) < 256 \<Longrightarrow> n mod 2 ^ 8 = n"
  by auto

lemma inductiveStepInjection : "(\<And>a b. byteStringToPositiveInt xt = Some (a, b) \<Longrightarrow> positiveIntToByteString a @ b = xt) \<Longrightarrow>
    Some (uint xh - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow>
    \<not> uint (xh :: 8 word) < 128 \<Longrightarrow> byteStringToPositiveInt xt = Some aa \<Longrightarrow> aa = (aaa, aab) \<Longrightarrow> (a < 128 \<longrightarrow> word_of_int a = xh \<and> b = xt) \<and> (\<not> a < 128 \<longrightarrow> word_of_int (a mod 128 + 128) = xh \<and> positiveIntToByteString (a div 128 - 1) @ b = xt)"
  apply (rule splitAnd1)
  using byteStringToPositiveIntIsPositive apply fastforce
  apply (rule splitAnd2)
   apply (cases "xh")
  subgoal for n
    apply auto[1]
    apply (simp only:"take_bit_eq_mod")
    apply (subst nat_mod_id)
    apply fastforce
    apply (subst fold_sig_bit_in_word_of_int)
    by (metis nat_mod_id linorder_not_le mod_mult_self2 of_int_of_nat_eq of_nat_less_iff of_nat_numeral unitRestoration zero_le)
  apply (rule inductiveStepInjection_aux2)
  by auto

theorem byteStrintToPositiveInt_inverseRoundtrip : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow> positiveIntToByteString a @ b = x"
  apply (induction x arbitrary:a b)
   apply simp
  subgoal for xh xt a b
    apply (simp only:positiveIntToByteString.simps[of a] byteStringToPositiveInt.simps)
    apply (cases "uint xh < 128")
     apply (simp del:positiveIntToByteString.simps byteStringToPositiveInt.simps)
    using word_of_int_uint apply blast
     apply (simp del:positiveIntToByteString.simps byteStringToPositiveInt.simps)
    apply (cases "byteStringToPositiveInt xt")
    apply simp
    subgoal for aa
      apply (cases aa)
      subgoal for aaa aab
        apply (subst fold_sig_bit_in_word_of_int)
        apply (rule inductiveStepInjection)
        by auto
      done
    done
  done

lemma byteStringToPositiveInt_injective : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow> byteStringToPositiveInt y = Some (a, b) \<Longrightarrow> x = y"
  using byteStrintToPositiveInt_inverseRoundtrip by blast

lemma byteStringToPositiveInt_injective2 : "x \<noteq> y \<Longrightarrow> (byteStringToPositiveInt x \<noteq> byteStringToPositiveInt y) \<or> (byteStringToPositiveInt x = None) \<or> (byteStringToPositiveInt y = None)"
  using byteStringToPositiveInt_injective by force

fun intToByteString :: "int \<Rightarrow> ByteString" where
"intToByteString x = (if x \<ge> 0 then positiveIntToByteString (x * 2) else positiveIntToByteString (- (x * 2 + 1)))"

fun byteStringToInt :: "ByteString \<Rightarrow> (int \<times> ByteString) option" where
"byteStringToInt x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, extra) \<Rightarrow> Some (if (y mod 2 = 0) then y div 2 else (- (y div 2 + 1)), extra))"

theorem intToByteStringToInt : "byteStringToInt ((intToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  by (simp_all del:byteStringToPositiveInt.simps positiveIntToByteString.simps add:positiveIntToByteStringToPositiveInt)


theorem byteStringToInt_inverseRoundtrip : "byteStringToInt x = Some (a, b) \<Longrightarrow> intToByteString a @ b = x"
  apply (simp only:byteStringToInt.simps intToByteString.simps)
  apply (cases "byteStringToPositiveInt x")
  apply simp
  subgoal for aa
    apply (cases aa)
    subgoal for aaa aab
      apply (auto simp del:byteStringToPositiveInt.simps positiveIntToByteString.simps simp add:byteStrintToPositiveInt_inverseRoundtrip)
      apply (simp add: byteStringToPositiveIntIsPositive)
      apply (smt byteStringToPositiveIntIsPositive)
      by (metis add.commute byteStrintToPositiveInt_inverseRoundtrip diff_add_cancel minus_mod_eq_mult_div mult.commute)
    done
  done

lemma byteStringToInt_injective : "byteStringToInt x = Some (a, b) \<Longrightarrow> byteStringToInt y = Some (a, b) \<Longrightarrow> x = y"
  using byteStringToInt_inverseRoundtrip by blast

lemma byteStringToInt_injective2 : "x \<noteq> y \<Longrightarrow> (byteStringToInt x \<noteq> byteStringToInt y) \<or> (byteStringToInt x = None) \<or> (byteStringToInt y = None)"
  using byteStringToInt_injective by force

fun packByteString :: "ByteString \<Rightarrow> ByteString" where
"packByteString bs = positiveIntToByteString (int (length bs)) @ bs"

fun getByteString :: "ByteString \<Rightarrow> (ByteString \<times> ByteString) option" where
"getByteString bs =
  (case byteStringToPositiveInt bs of
     Some (val, rest) \<Rightarrow> if int (length rest) < val
                         then None
                         else Some (take (nat val) rest, drop (nat val) rest)
   | None \<Rightarrow> None
  )"

lemma addAndGetByteString : "getByteString (packByteString x @ y) = Some (x, y)"
  by (simp del:positiveIntToByteString.simps add:positiveIntToByteStringToPositiveInt)

lemma addAndGetByteString_inverseRoundtrip : "getByteString x = Some (y, z) \<Longrightarrow> packByteString y @ z = x"
  apply (simp only:getByteString.simps packByteString.simps split:option.splits prod.splits)
   apply blast
   subgoal for x2 x1 x2a
    apply (cases "int (length x2a) < x1")
      apply (simp_all del:byteStringToPositiveInt.simps positiveIntToByteString.simps split:option.splits prod.splits)
     apply (subst byteStrintToPositiveInt_inverseRoundtrip[of x])
     using byteStringToPositiveIntIsPositive apply fastforce
     by blast
   done

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
    by (metis (mono_tags, opaque_lifting) \<open>\<And>ya tx hx. \<lbrakk>less_eq_BS (hx # tx) ya; less_eq_BS ya []\<rbrakk> \<Longrightarrow> False\<close> byteStringToPositiveInt.cases less_eq_BS.simps(4) not_le not_less_iff_gr_or_eq order_trans)
  done

lemma byteStringLessEqTwiceEq : "less_eq_BS x y \<Longrightarrow> less_eq_BS y x \<Longrightarrow> x = y"
  apply (induction x y rule:less_eq_BS.induct)
  apply auto
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  subgoal for h1 t1 h2 t2
    by (meson not_less_iff_gr_or_eq)
  done

lemma byteStringToPositiveInt_reduceslist : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (induction x rule:byteStringToPositiveInt.induct)
  apply simp
  subgoal for xw rest
    apply (simp add:Let_def refl)
    apply (cases "byteStringToPositiveInt rest")
     apply (smt le_imp_less_Suc le_less option.distinct(1) option.inject option.simps(4) prod.inject)
    subgoal for aa
      apply (cases "uint xw < 128")
       apply (auto split:prod.splits)
      using byteStrintToPositiveInt_inverseRoundtrip by fastforce
    done
  done

lemma byteStringToInt_reduceslist : "byteStringToInt x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  using byteStringToInt_inverseRoundtrip by fastforce


lemma getByteString_reduceslist : "getByteString x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  using addAndGetByteString_inverseRoundtrip by fastforce


fun listToByteString_aux :: "('a \<Rightarrow> ByteString) \<Rightarrow> 'a list \<Rightarrow> ByteString" where
"listToByteString_aux f (Cons h t) = f h @ listToByteString_aux f t" |
"listToByteString_aux f Nil = Nil"

fun listToByteString :: "('a \<Rightarrow> ByteString) \<Rightarrow> 'a list \<Rightarrow> ByteString" where
"listToByteString f l = (let listLength = length l in positiveIntToByteString (int listLength) @ listToByteString_aux f l)"

fun byteStringToList_aux :: "(ByteString \<Rightarrow> ('a \<times> ByteString) option) \<Rightarrow> int \<Rightarrow> ByteString \<Rightarrow> ('a list \<times> ByteString) option" where
"byteStringToList_aux f n bs =
  (if n > 0
   then (case f bs of
           None \<Rightarrow> None
         | Some (a, nbs) \<Rightarrow> (case byteStringToList_aux f (n - 1) nbs of
                               None \<Rightarrow> None
                             | Some (lr, fbs) \<Rightarrow> Some (a # lr, fbs)))
   else (Some (Nil, bs)))"

fun byteStringToList :: "(ByteString \<Rightarrow> ('a \<times> ByteString) option) \<Rightarrow> ByteString \<Rightarrow> ('a list \<times> ByteString) option" where
"byteStringToList f bs =
  (case byteStringToPositiveInt bs of
     None \<Rightarrow> None
   | Some (listLength, nbs) \<Rightarrow> byteStringToList_aux f listLength nbs)"

theorem listToByteStringTolist : "(\<And> x y. decode ((encode x) @ y) = Some (x, y)) \<Longrightarrow> byteStringToList decode ((listToByteString encode x) @ y) = Some (x, y)"
  oops

theorem byteStringToList_inverseRoundtrip : "(\<And> x a b. decode x = Some (a, b) \<Longrightarrow> encode a @ b = x) \<Longrightarrow> byteStringToList decode x = Some (a, b) \<Longrightarrow> listToByteString encode a @ b = x"
  oops


end
