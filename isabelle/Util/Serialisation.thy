theory Serialisation
  imports "HOL-Library.Word" ByteString
begin

fun positiveIntToByteStringAux :: "int \<Rightarrow> 8 word list" where
"positiveIntToByteStringAux x =
  (if x < 128 then [word_of_int x] else (word_of_int ((x mod 128) + 128)) # (positiveIntToByteStringAux ((x div 128) - 1)))"

fun positiveIntToByteString :: "int \<Rightarrow> ByteString" where
"positiveIntToByteString x = ByteString (positiveIntToByteStringAux x)"

fun byteStringToPositiveIntAux :: "8 word list \<Rightarrow> (int \<times> 8 word list) option" where
"byteStringToPositiveIntAux Nil = None" |
"byteStringToPositiveIntAux (Cons xw rest) =
  (let x = uint xw in
    (if x < 128
     then (Some (x, rest))
     else (case byteStringToPositiveIntAux rest of
             None \<Rightarrow> None
           | Some (y, extra) \<Rightarrow> Some ((x - 128) + 128 * (y + 1), extra))))"

fun byteStringToPositiveInt :: "ByteString \<Rightarrow> (int \<times> ByteString) option" where
"byteStringToPositiveInt (ByteString x) =
   (case byteStringToPositiveIntAux x of
      Some (y, rest) \<Rightarrow> Some (y, ByteString rest)
    | None \<Rightarrow> None)"

lemma packByteStringToPositveIntLazy : "(case byteStringToPositiveIntAux (innerListByteString x) of
                                          Some (y, rest) \<Rightarrow> Some (y, ByteString rest)
                                        | None \<Rightarrow> None) = byteStringToPositiveInt x"
  by (metis byteStringToPositiveInt.simps innerListByteString.elims)

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

lemma distrib_cons_append_bytestrings : "appendByteStrings (consByteString x y) z = consByteString x (appendByteStrings y z)"
  by (metis appendByteStrings.simps append_Cons byteStringToPositiveInt.cases consByteString.simps)

lemma positiveIntToByteStringToPositiveIntAux_inductionStep : "0 \<le> (x :: int) \<Longrightarrow> (\<And>ya. 0 \<le> ya \<Longrightarrow> ya < x \<Longrightarrow> byteStringToPositiveIntAux ((positiveIntToByteStringAux ya) @ y) = Some (ya, y))
                                                                    \<Longrightarrow> byteStringToPositiveIntAux ((positiveIntToByteStringAux x) @ y) = Some (x, y)"
  apply (cases "x < 128")
  apply (simp add:take_bit_eq_mod intToWordToUint Let_def)
  apply (simp only:positiveIntToByteStringAux.simps[of x] if_False intToWordToUint)
  apply (simp del:positiveIntToByteStringAux.simps add:Let_def intToWordToUint )
  apply (simp only:fold_sig_bit_in_word_of_int intToWordToUint)
  by simp


lemma positiveIntToByteStringToPositiveIntAux : "(x :: int) \<ge> 0 \<Longrightarrow> byteStringToPositiveIntAux ((positiveIntToByteStringAux x) @ y) = Some (x, y)"
  apply (rule smallerIntInduction[of "\<lambda> x. byteStringToPositiveIntAux (positiveIntToByteStringAux x @ y) = Some (x, y)"])
  using positiveIntToByteStringToPositiveIntAux_inductionStep apply blast
  by simp

theorem positiveIntToByteStringToPositiveInt : "(x :: int) \<ge> 0 \<Longrightarrow> byteStringToPositiveInt (appendByteStrings (positiveIntToByteString x) y) = Some (x, y)"
  apply (cases y)
  subgoal for ys
    apply (simp only:byteStringToPositiveInt.simps appendByteStrings.simps positiveIntToByteString.simps)
    using positiveIntToByteStringToPositiveIntAux by auto
  done

lemma byteStringToPositiveIntAuxIsPositive : "byteStringToPositiveIntAux x = Some (a, b) \<Longrightarrow> a \<ge> 0"
  apply (induction x arbitrary:a b rule:byteStringToPositiveIntAux.induct)
  apply simp
  subgoal for xw rest a b
    apply (cases "uint xw < 128")
    apply auto
    apply (cases "byteStringToPositiveIntAux rest")
    by auto
  done

lemma byteStringToPositiveIntIsPositive : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow> a \<ge> 0"
  apply (cases x)
  subgoal sx
  by (metis (no_types, lifting) byteStringToPositiveInt.simps byteStringToPositiveIntAuxIsPositive case_prod_conv option.distinct(1) option.exhaust option.inject option.simps(4) option.simps(5) prod.inject surj_pair)
  done

lemma unitRestoration : "a \<ge> 0 \<Longrightarrow> xh \<ge> 128 \<Longrightarrow> xh < 256 \<Longrightarrow> (xh + 128 * aaa) mod 128 + 128 = (xh :: int)"
  apply simp
  by (smt (z3) Euclidean_Division.pos_mod_bound mod_double_modulus mod_pos_pos_trivial)

lemma inductiveStepInjection_aux : "Some (xh - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow> xh < 256 \<Longrightarrow> xh \<ge> (128 :: int) \<Longrightarrow>
                                    byteStringToPositiveIntAux xt = Some (aaa, aab) \<Longrightarrow> a \<ge> 128 \<Longrightarrow> byteStringToPositiveIntAux xt = Some (a div 128 - 1, b)"
  by auto

lemma inductiveStepInjection_aux2 : "(\<And>a b. byteStringToPositiveIntAux xt = Some (a, b) \<Longrightarrow> positiveIntToByteStringAux a @ b = xt) \<Longrightarrow>
    Some (uint (xh :: 8 word) - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow> uint xh \<ge> 128 \<Longrightarrow> byteStringToPositiveIntAux xt = Some aa \<Longrightarrow> aa = (aaa, aab) \<Longrightarrow> a \<ge> 128 \<Longrightarrow> positiveIntToByteStringAux (a div 128 - 1) @ b = xt"
  subgoal premises fact
    apply (rule fact(1))
    apply (rule inductiveStepInjection_aux[of "uint xh" aaa aab a b xt])
    using fact(2) apply blast
  apply (cases "xh")
       apply auto
    subgoal for n2
      by (metis intToWordToUint less_imp_of_nat_less of_int_of_nat_eq of_nat_0_le_iff of_nat_numeral)
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

lemma inductiveStepInjection : "(\<And>a b. byteStringToPositiveIntAux xt = Some (a, b) \<Longrightarrow> positiveIntToByteStringAux a @ b = xt) \<Longrightarrow>
    Some (uint xh - 128 + 128 * (aaa + 1), aab) = Some (a, b) \<Longrightarrow>
    \<not> uint (xh :: 8 word) < 128 \<Longrightarrow> byteStringToPositiveIntAux xt = Some aa \<Longrightarrow> aa = (aaa, aab) \<Longrightarrow> (a < 128 \<longrightarrow> word_of_int a = xh \<and> b = xt) \<and> (\<not> a < 128 \<longrightarrow> word_of_int (a mod 128 + 128) = xh \<and> positiveIntToByteStringAux (a div 128 - 1) @ b = xt)"
  apply (rule splitAnd1)
  using byteStringToPositiveIntAuxIsPositive apply fastforce
  apply (rule splitAnd2)
   apply (cases "xh")
  subgoal for n
    apply auto[1]
    by (metis fold_sig_bit_in_word_of_int intToWordToUint less_imp_of_nat_less mod_mult_self2 of_int_of_nat_eq of_nat_0_le_iff of_nat_numeral unitRestoration verit_comp_simplify1(3))
  apply (rule inductiveStepInjection_aux2)
  by auto

lemma byteStrintToPositiveIntAux_inverseRoundtrip : "byteStringToPositiveIntAux x = Some (a, b) \<Longrightarrow> positiveIntToByteStringAux a @ b = x"
  apply (induction x arbitrary:a b)
   apply simp
  subgoal for xh xt a b
    apply (simp only:positiveIntToByteStringAux.simps[of a] byteStringToPositiveIntAux.simps)
    apply (cases "uint xh < 128")
     apply (simp del:positiveIntToByteStringAux.simps byteStringToPositiveIntAux.simps)
    using word_of_int_uint apply blast
     apply (simp del:positiveIntToByteStringAux.simps byteStringToPositiveIntAux.simps)
    apply (cases "byteStringToPositiveIntAux xt")
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

theorem byteStrintToPositiveInt_inverseRoundtrip : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow> appendByteStrings (positiveIntToByteString a) b = x"
  apply (cases x)
  apply (cases b)
  subgoal for sx sb
    apply (simp only:positiveIntToByteString.simps appendByteStrings.simps byteStringToPositiveInt.simps)
    by (smt (verit, ccfv_SIG) byteStrintToPositiveIntAux_inverseRoundtrip case_prod_conv innerListByteString.simps not_None_eq option.collapse option.distinct(1) option.inject option.simps(4) option.simps(5) prod.inject surj_pair)
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

theorem intToByteStringToInt : "byteStringToInt (appendByteStrings (intToByteString x) y) = Some (x, y)"
  apply (cases x)
  by (simp_all del:byteStringToPositiveInt.simps positiveIntToByteString.simps add:positiveIntToByteStringToPositiveInt)


theorem byteStringToInt_inverseRoundtrip : "byteStringToInt x = Some (a, b) \<Longrightarrow> appendByteStrings (intToByteString a) b = x"
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
"packByteString bs = appendByteStrings (positiveIntToByteString (int (lengthByteString bs))) bs"

fun getByteString :: "ByteString \<Rightarrow> (ByteString \<times> ByteString) option" where
"getByteString bs =
  (case byteStringToPositiveInt bs of
     Some (val, rest) \<Rightarrow> if int (lengthByteString rest) < val
                         then None
                         else Some (takeByteString (nat val) rest, dropByteString (nat val) rest)
   | None \<Rightarrow> None
  )"

lemma appendTakeByteStrings : "lengthByteString x = n \<Longrightarrow> takeByteString n (appendByteStrings x y) = x"
  by (metis appendByteStrings.elims append_eq_conv_conj lengthByteString.simps takeByteString.simps)

lemma appendDropByteStrings : "lengthByteString x = n \<Longrightarrow> dropByteString n (appendByteStrings x y) = y"
  by (metis appendByteStrings.elims append_eq_conv_conj dropByteString.elims innerListByteString.simps lengthByteString.elims)

lemma appendLength : "lengthByteString x + lengthByteString y = lengthByteString (appendByteStrings x y)"
  apply (cases x)
  apply (cases y)
  by simp

lemma addAndGetByteString : "getByteString (appendByteStrings (packByteString x) y) = Some (x, y)"
  apply (simp only:getByteString.simps)
  apply (cases "byteStringToPositiveInt (appendByteStrings (packByteString x) y)")
  using appendByteStringsAssoc positiveIntToByteStringToPositiveInt apply force
  subgoal for a
    apply (simp only:option.cases)
    apply (cases a)
    subgoal for fa sa
      apply (auto split:prod.split simp only:)
      apply (cases "int (lengthByteString sa) < fa")
       apply (simp only:if_True)
  apply (smt (verit, del_insts) add.right_neutral add_mono_thms_linordered_semiring(1) appendByteStringsAssoc appendLength byteStrintToPositiveInt_inverseRoundtrip innerListByteString.elims le_zero_eq nat_int nat_le_eq_zle nat_le_linear of_nat_0_le_iff of_nat_0_le_iff of_nat_eq_iff option.inject packByteString.simps positiveIntToByteStringToPositiveInt prod.inject semiring_1_class.of_nat_0 split_nat)
      using appendByteStringsAssoc appendDropByteStrings appendTakeByteStrings positiveIntToByteStringToPositiveInt by fastforce
    done
  done

lemma resultOfTakeByteStringHasLength : "lengthByteString (takeByteString n x) = min n (lengthByteString x)"
  by (metis innerListByteString.elims lengthByteString.simps length_take min.commute takeByteString.simps)

lemma takeLengthIfLongEnough : "takeByteString n x = y \<Longrightarrow> lengthByteString x \<ge> n \<Longrightarrow> lengthByteString y = n" 
  by (metis min.absorb1 resultOfTakeByteStringHasLength)

lemma addAndGetByteString_inverseRoundtrip : "getByteString x = Some (y, z) \<Longrightarrow> appendByteStrings (packByteString y) z = x"
  apply (simp only:getByteString.simps packByteString.simps split:option.splits prod.splits)
   apply blast
  subgoal for x2 x1 x2a
    apply (cases "int (lengthByteString x2a) < x1")
     apply (simp del:byteStringToPositiveInt.simps positiveIntToByteString.simps split:option.splits prod.splits)
     apply (simp only:if_False)
     apply (simp only:appendByteStringsAssoc)
     thm byteStrintToPositiveInt_inverseRoundtrip[of x "int (lengthByteString y)" z]
     apply (subst byteStrintToPositiveInt_inverseRoundtrip[of x "int (lengthByteString y)" "appendByteStrings y z"])
     using appendTakeDropByteString byteStringToPositiveIntIsPositive takeLengthIfLongEnough apply force
     by blast
   done

lemma byteStringToPositiveIntAux_reduceslist : "byteStringToPositiveIntAux x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (induction x rule:byteStringToPositiveIntAux.induct)
  apply simp
  subgoal for xw rest
    apply (simp add:Let_def refl)
    apply (cases "byteStringToPositiveIntAux rest")
     apply (smt le_imp_less_Suc le_less option.distinct(1) option.inject option.simps(4) prod.inject)
    subgoal for aa
      apply (cases "uint xw < 128")
       apply (auto split:prod.splits)
      using byteStrintToPositiveIntAux_inverseRoundtrip by fastforce
    done
  done

lemma byteStringToPositiveInt_reduceslist : "byteStringToPositiveInt x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (cases x)
  apply (simp only:byteStringToPositiveInt.simps)
  subgoal for sx
    apply (cases "byteStringToPositiveIntAux sx")
     apply simp
    using byteStringToPositiveIntAux_reduceslist size_ByteString_overloaded_def by force
  done

lemma byteStringToInt_reduceslist : "byteStringToInt x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (cases x)
  apply (simp only:byteStringToInt.simps)
  subgoal for sx
    apply (cases "byteStringToPositiveInt (ByteString sx)")
     apply simp
    subgoal for sxaa
      apply (cases sxaa)
      apply simp
  using byteStringToPositiveInt.simps byteStringToPositiveInt_reduceslist by presburger
  done
  done

lemma getByteString_reduceslist : "getByteString x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  by (smt (verit, ccfv_threshold) addAndGetByteString_inverseRoundtrip add_diff_cancel_right' appendLength byteStringToPositiveInt_reduceslist cancel_comm_monoid_add_class.diff_cancel linorder_neqE_nat nat_int nat_zero_as_int not_add_less2 of_nat_0_le_iff of_nat_0_less_iff packByteString.simps positiveIntToByteStringToPositiveInt size_ByteString_overloaded_def)

fun listToByteString_aux :: "('a \<Rightarrow> ByteString) \<Rightarrow> 'a list \<Rightarrow> ByteString" where
"listToByteString_aux f (Cons h t) = appendByteStrings (f h) (listToByteString_aux f t)" |
"listToByteString_aux f Nil = emptyByteString"

fun listToByteString :: "('a \<Rightarrow> ByteString) \<Rightarrow> 'a list \<Rightarrow> ByteString" where
"listToByteString f l = (let listLength = length l in appendByteStrings (positiveIntToByteString (int listLength)) (listToByteString_aux f l))"

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

theorem listToByteStringTolist : "(\<And> x y. decode (appendByteStrings (encode x) y) = Some (x, y)) \<Longrightarrow> byteStringToList decode (appendByteStrings(listToByteString encode x) y) = Some (x, y)"
  oops

theorem byteStringToList_inverseRoundtrip : "(\<And> x a b. decode x = Some (a, b) \<Longrightarrow> appendByteStrings (encode a) b = x) \<Longrightarrow> byteStringToList decode x = Some (a, b) \<Longrightarrow> appendByteStrings (listToByteString encode a) b = x"
  oops


end
