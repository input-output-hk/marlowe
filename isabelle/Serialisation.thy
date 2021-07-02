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

end