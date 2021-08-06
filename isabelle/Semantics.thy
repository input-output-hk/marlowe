theory Semantics
imports Main MList SList ListTools "HOL-Library.Product_Lexorder" Serialisation
begin

type_synonym Slot = int

type_synonym PubKey = ByteString

type_synonym Ada = int
type_synonym CurrencySymbol = ByteString
type_synonym TokenName = ByteString

type_synonym ChoiceName = ByteString
type_synonym NumAccount = int
type_synonym Timeout = Slot
type_synonym Money = Ada
type_synonym ChosenNum = int

datatype Party = PubKey ByteString
               | Role TokenName

type_synonym AccountId = Party

(* BEGIN Proof of linorder for Party *)
fun less_eq_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where
"less_eq_Party (PubKey _) (Role _) = True" |
"less_eq_Party (Role _) (PubKey _) = False" |
"less_eq_Party (PubKey x) (PubKey y) = less_eq_BS x y" |
"less_eq_Party (Role x) (Role y) = less_eq_BS x y"

fun less_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where
"less_Party a b = (\<not> (less_eq_Party b a))"

instantiation "Party" :: "ord"
begin
definition "a \<le> b = less_eq_Party a b"
definition "a < b = less_Party a b"
instance
proof
qed
end

lemma linearParty : "x \<le> y \<or> y \<le> (x::Party)"
  apply (cases x)
  subgoal for x
    apply (cases y)
    subgoal for y
      using less_eq_Party.simps(3) less_eq_Party_def oneLessEqBS by blast
    subgoal for y
      by (simp add: less_eq_Party_def)
    done
  subgoal for x
    apply (cases y)
    subgoal for y
      by (simp add: less_eq_Party_def)
    subgoal for y
      using less_eq_Party.simps(4) less_eq_Party_def oneLessEqBS by blast
    done
  done

instantiation "Party" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: Party))"
    by (meson less_Party.simps less_Party_def less_eq_Party_def linearParty)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: Party)" by (meson linearParty)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: Party)"
    apply (auto simp add:less_eq_Party_def)
    apply (cases x)
     apply (cases y)
      apply (cases z)
    using byteStringOrder less_eq_Party.simps(3) apply blast
      apply simp_all
     apply (metis Party.exhaust less_eq_Party.simps(1) less_eq_Party.simps(2))
     apply (cases y)
      apply (cases z)
      apply simp_all
    by (metis Party.exhaust byteStringOrder less_eq_Party.simps(2) less_eq_Party.simps(4))
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Party)"
    apply (auto simp add:less_eq_Party_def)
    apply (cases x)
     apply (cases y)
    apply (simp add: byteStringLessEqTwiceEq)
     apply simp
     apply (cases y)
     apply simp
    by (simp add: byteStringLessEqTwiceEq)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Party)" by simp
next
  fix x y
  from linearParty have "x \<le> y \<or> y \<le> (x :: Party)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for Party *)

fun partyToByteString :: "Party \<Rightarrow> ByteString" where
"partyToByteString (PubKey x) = (positiveIntToByteString 0) @ (packByteString x)" |
"partyToByteString (Role x) = (positiveIntToByteString 1) @ (packByteString x)"

fun byteStringToParty :: "ByteString \<Rightarrow> (Party \<times> ByteString) option" where
"byteStringToParty x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow> (case getByteString t1 of
                        None \<Rightarrow> None
                      | Some (z, t2) \<Rightarrow> (if y = 0
                                         then Some (PubKey z, t2)
                                         else (if y = 1
                                               then Some (Role z, t2)
                                               else None))))"

lemma partyToByteStringToParty : "byteStringToParty ((partyToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  subgoal for x
    apply (cases "byteStringToPositiveInt (positiveIntToByteString 0 @ packByteString x @ y)")
    apply simp
    subgoal for a
      apply (cases a)
      subgoal for aa ab
      apply (simp del:byteStringToPositiveInt.simps positiveIntToByteString.simps packByteString.simps getByteString.simps)
        using positiveIntToByteStringToPositiveInt by force
      done
    done
  subgoal for x
    apply (cases "byteStringToPositiveInt (positiveIntToByteString 1 @ packByteString x @ y)")
    apply (simp del:byteStringToPositiveInt.simps positiveIntToByteString.simps packByteString.simps getByteString.simps)
    apply simp
    subgoal for a
      apply (cases a)
      subgoal for aa ab
      apply (simp del:byteStringToPositiveInt.simps positiveIntToByteString.simps packByteString.simps getByteString.simps)
        using positiveIntToByteStringToPositiveInt by force
      done
    done
  done


lemma byteStringToParty_inverseRoundtrip : "byteStringToParty x = Some (a, b) \<Longrightarrow> partyToByteString a @ b = x"
  apply (simp del:byteStringToPositiveInt.simps getByteString.simps split:option.splits prod.splits)
  subgoal for x2 x1 x2a x2b x1a x2c
    apply (cases "x1 = 0")
    apply (simp del:byteStringToPositiveInt.simps getByteString.simps split:option.splits prod.splits)
    apply (metis addAndGetByteString_inverseRoundtrip append_eq_appendI byteStrintToPositiveInt_inverseRoundtrip partyToByteString.simps(1))
    apply (cases "x1 = 1")
    apply (metis addAndGetByteString_inverseRoundtrip append_eq_appendI byteStrintToPositiveInt_inverseRoundtrip old.prod.inject option.inject partyToByteString.simps(2))
    by simp
  done

lemma byteStringToParty_reduceslist : "byteStringToParty x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (induction x rule:byteStringToParty.induct)
  subgoal for x
    apply (simp only:byteStringToParty.simps[of x])
    apply (cases "byteStringToPositiveInt x")
     apply simp
    subgoal for y
      apply (cases y)
      subgoal for ya yb
        apply (simp only:option.case prod.case)
        apply (cases "getByteString yb")
         apply simp
        subgoal for z
          apply (cases z)
          subgoal for za zb
            apply (simp only:option.case prod.case)
            by (metis byteStringToPositiveInt_reduceslist getByteString_reduceslist le_less le_less_trans option.distinct(1) option.inject snd_conv)
          done
        done
      done
    done
  done

datatype Token = Token CurrencySymbol TokenName

(* BEGIN Proof of linorder for Token *)
fun less_eq_Tok :: "Token \<Rightarrow> Token \<Rightarrow> bool" where
"less_eq_Tok (Token a b) (Token c d) =
   (if less_BS a c then True
    else (if (less_BS c a) then False else less_eq_BS b d))"

fun less_Tok :: "Token \<Rightarrow> Token \<Rightarrow> bool" where
"less_Tok a b = (\<not> (less_eq_Tok b a))"

instantiation "Token" :: "ord"
begin
definition "a \<le> b = less_eq_Tok a b"
definition "a < b = less_Tok a b"
instance
proof
qed
end

lemma linearToken : "x \<le> y \<or> y \<le> (x::Token)"
  by (smt Token.simps(1) less_eq_Tok.elims(3) less_eq_Token_def lineaBS)

instantiation "Token" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: Token))"
    by (meson less_Tok.simps less_Token_def less_eq_Token_def linearToken)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: Token)" by (meson linearToken)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: Token)"
    by (smt byteStringOrder less_BS.simps less_eq_Tok.elims(2) less_eq_Tok.simps less_eq_Token_def oneLessEqBS)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Token)"
    by (smt Token.simps(1) byteStringLessEqTwiceEq less_BS.simps less_eq_Tok.elims(2) less_eq_Token_def oneLessEqBS)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Token)" by simp
next
  fix x y
  from linearToken have "x \<le> y \<or> y \<le> (x :: Token)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for Token *)

fun tokenToByteString :: "Token \<Rightarrow> ByteString" where
"tokenToByteString (Token tn cs) = (packByteString tn) @ (packByteString cs)"

fun byteStringToToken :: "ByteString \<Rightarrow> (Token \<times> ByteString) option" where
"byteStringToToken x =
  (case getByteString x of
      None \<Rightarrow> None
    | Some (tn, t1) \<Rightarrow> (case getByteString t1 of
                          None \<Rightarrow> None
                        | Some (cs, t2) \<Rightarrow> Some (Token tn cs, t2)))"

lemma tokenToByteStringToToken : "byteStringToToken ((tokenToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  subgoal for tn cs
    apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  using addAndGetByteString by auto
  done

lemma byteStringToToken_inverseRoundtrip : "byteStringToToken x = Some (a, b) \<Longrightarrow> tokenToByteString a @ b = x"
  apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  using addAndGetByteString_inverseRoundtrip append_assoc by blast


lemma byteStringToToken_reduceslist : "byteStringToToken x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  by (meson dual_order.strict_trans getByteString_reduceslist)

datatype ChoiceId = ChoiceId ChoiceName Party

(* BEGIN Proof of linorder for ChoiceId *)
fun less_eq_ChoId :: "ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> bool" where
"less_eq_ChoId (ChoiceId a b) (ChoiceId c d) =
   (if less_BS a c then True
    else (if (less_BS c a) then False else b \<le> d))"

fun less_ChoId :: "ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> bool" where
"less_ChoId a b = (\<not> (less_eq_ChoId b a))"

instantiation "ChoiceId" :: "ord"
begin
definition "a \<le> b = less_eq_ChoId a b"
definition "a < b = less_ChoId a b"
instance
proof
qed
end

lemma linearChoiceId : "x \<le> y \<or> y \<le> (x::ChoiceId)"
  by (smt ChoiceId.simps(1) leI less_eq_ChoId.elims(3) less_eq_ChoiceId_def order_le_less)

instantiation "ChoiceId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: ChoiceId))"
    by (meson less_ChoId.elims(2) less_ChoId.elims(3) less_ChoiceId_def less_eq_ChoiceId_def linearChoiceId)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: ChoiceId)" by (meson linearChoiceId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: ChoiceId)"
    apply (cases x)
    apply (cases y)
    apply (cases z)
    apply (simp only:less_eq_ChoiceId_def)
    by (smt byteStringOrder less_BS.simps less_eq_ChoId.simps oneLessEqBS order.trans)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ChoiceId)"
    by (smt byteStringLessEqTwiceEq eq_iff less_BS.simps less_eq_ChoId.elims(2) less_eq_ChoId.simps less_eq_ChoiceId_def oneLessEqBS)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ChoiceId)" by simp
next
  fix x y
  from linearChoiceId have "x \<le> y \<or> y \<le> (x :: ChoiceId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for ChoiceId *)

fun choiceIdToByteString :: "ChoiceId \<Rightarrow> ByteString" where
"choiceIdToByteString (ChoiceId cn co) = (packByteString cn) @ (partyToByteString co)"

fun byteStringToChoiceId :: "ByteString \<Rightarrow> (ChoiceId \<times> ByteString) option" where
"byteStringToChoiceId x =
  (case getByteString x of
      None \<Rightarrow> None
    | Some (cn, t1) \<Rightarrow> (case byteStringToParty t1 of
                          None \<Rightarrow> None
                        | Some (co, t2) \<Rightarrow> Some (ChoiceId cn co, t2)))"

lemma choiceIdToByteStringToChoiceId : "byteStringToChoiceId ((choiceIdToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  subgoal for cn co
    apply (auto simp only:choiceIdToByteString.simps byteStringToChoiceId.simps split:option.splits prod.splits)
    using addAndGetByteString partyToByteStringToParty by auto
  done

lemma byteStringToChoiceId_inverseRoundtrip : "byteStringToChoiceId x = Some (a, b) \<Longrightarrow> choiceIdToByteString a @ b = x"
  apply (auto simp only:choiceIdToByteString.simps byteStringToChoiceId.simps split:option.splits prod.splits)
  using addAndGetByteString_inverseRoundtrip append_assoc byteStringToParty_inverseRoundtrip by blast

lemma byteStringToChoiceId_reduceslist : "byteStringToChoiceId x = Some (a, b) \<Longrightarrow>
                                                       size b < size x"
  apply (simp only:byteStringToChoiceId.simps split:option.splits prod.splits)
   apply auto
  using byteStringToParty_reduceslist getByteString_reduceslist by fastforce


(* datatype OracleId = OracleId PubKey

(* BEGIN Proof of linorder for OracleId *)
fun less_eq_OraId :: "OracleId \<Rightarrow> OracleId \<Rightarrow> bool" where
"less_eq_OraId (OracleId a) (OracleId b) = (a \<le> b)"

fun less_OraId :: "OracleId \<Rightarrow> OracleId \<Rightarrow> bool" where
"less_OraId (OracleId a) (OracleId b) = (a < b)"

instantiation "OracleId" :: "ord"
begin
definition "a \<le> b = less_eq_OraId a b"
definition "a < b = less_OraId a b"
instance
proof
qed
end

lemma linearOracleId : "x \<le> y \<or> y \<le> (x::OracleId)"
  by (smt OracleId.inject less_eq_OraId.elims(3) less_eq_OracleId_def)

instantiation "OracleId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: OracleId))"
    by (metis OracleId.exhaust dual_order.order_iff_strict less_OraId.simps less_OracleId_def less_eq_OraId.simps less_eq_OracleId_def not_le)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: OracleId)" by (meson linearOracleId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: OracleId)"
    by (smt OracleId.inject less_eq_OraId.elims(2) less_eq_OraId.elims(3) less_eq_OracleId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: OracleId)"
    by (smt less_eq_OraId.elims(2) less_eq_OraId.simps less_eq_OracleId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: OracleId)" by simp
next
  fix x y
  from linearOracleId have "x \<le> y \<or> y \<le> (x :: OracleId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for OracleId *)
*)

datatype ValueId = ValueId ByteString

(* BEGIN Proof of linorder for ValueId *)
fun less_eq_ValId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where
"less_eq_ValId (ValueId a) (ValueId b) = less_eq_BS a b"

fun less_ValId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where
"less_ValId (ValueId a) (ValueId b) = less_BS a b"

instantiation "ValueId" :: "ord"
begin
definition "a \<le> b = less_eq_ValId a b"
definition "a < b = less_ValId a b"
instance
proof
qed
end

lemma linearValueId : "x \<le> y \<or> y \<le> (x::ValueId)"
  by (metis ValueId.simps(1) less_eq_ValId.elims(3) less_eq_ValueId_def oneLessEqBS)

instantiation "ValueId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: ValueId))"
    by (metis ValueId.exhaust less_BS.simps less_ValId.simps less_ValueId_def less_eq_ValId.simps less_eq_ValueId_def linearValueId)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: ValueId)" by (meson linearValueId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: ValueId)"
    by (smt ValueId.simps(1) byteStringOrder less_eq_ValId.elims(2) less_eq_ValId.elims(3) less_eq_ValueId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ValueId)"
    by (metis ValueId.simps(1) byteStringLessEqTwiceEq less_eq_ValId.elims(2) less_eq_ValueId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ValueId)" by simp
next
  fix x y
  from linearValueId have "x \<le> y \<or> y \<le> (x :: ValueId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for ValueId *)

fun valueIdToByteString :: "ValueId \<Rightarrow> ByteString" where
"valueIdToByteString (ValueId n) = packByteString n"

fun byteStringToValueId :: "ByteString \<Rightarrow> (ValueId \<times> ByteString) option" where
"byteStringToValueId x =
  (case getByteString x of
      None \<Rightarrow> None
    | Some (n, t) \<Rightarrow> Some (ValueId n, t))"

lemma valueIdToByteStringToValueId : "byteStringToValueId ((valueIdToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  subgoal for n
    using addAndGetByteString by auto
  done

lemma byteStringToValueId_inverseRoundtrip : "byteStringToValueId x = Some (a, b) \<Longrightarrow> valueIdToByteString a @ b = x"
  apply (auto simp only:valueIdToByteString.simps byteStringToValueId.simps split:option.splits prod.splits)
  using addAndGetByteString_inverseRoundtrip by blast

lemma byteStringToValueId_reduceslist : "byteStringToValueId x = Some (a, b) \<Longrightarrow>
                                                       size b < size x"
  apply (simp only:byteStringToValueId.simps split:option.splits prod.splits)
   apply auto
  using byteStringToParty_reduceslist getByteString_reduceslist by fastforce

datatype Value = AvailableMoney AccountId Token
               | Constant int
               | NegValue Value
               | AddValue Value Value
               | SubValue Value Value
               | MulValue Value Value
               | Scale int int Value
               | ChoiceValue ChoiceId
               | SlotIntervalStart
               | SlotIntervalEnd
               | UseValue ValueId
               | Cond Observation Value Value
and Observation = AndObs Observation Observation
                     | OrObs Observation Observation
                     | NotObs Observation
                     | ChoseSomething ChoiceId
                     | ValueGE Value Value
                     | ValueGT Value Value
                     | ValueLT Value Value
                     | ValueLE Value Value
                     | ValueEQ Value Value
                     | TrueObs
                     | FalseObs

fun valueToByteString :: "Value \<Rightarrow> ByteString" and
    observationToByteString :: "Observation \<Rightarrow> ByteString" where
"valueToByteString (AvailableMoney accId token) =
   positiveIntToByteString 0 @ partyToByteString accId @ tokenToByteString token" |
"valueToByteString (Constant integer) = positiveIntToByteString 1 @ intToByteString integer" |
"valueToByteString (NegValue val) = positiveIntToByteString 2 @ valueToByteString val" |
"valueToByteString (AddValue lhs rhs) =
    positiveIntToByteString 3 @ valueToByteString lhs @ valueToByteString rhs" |
"valueToByteString (SubValue lhs rhs) =
    positiveIntToByteString 4 @ valueToByteString lhs @ valueToByteString rhs" |
"valueToByteString (MulValue lhs rhs) =
    positiveIntToByteString 5 @ valueToByteString lhs @ valueToByteString rhs" |
"valueToByteString (Scale n d rhs) = 
    positiveIntToByteString 6 @ intToByteString n @ intToByteString d @ valueToByteString rhs" |
"valueToByteString (ChoiceValue choId) =
    positiveIntToByteString 7 @ choiceIdToByteString choId" |
"valueToByteString (SlotIntervalStart) = positiveIntToByteString 8" |
"valueToByteString (SlotIntervalEnd) = positiveIntToByteString 9" |
"valueToByteString (UseValue valId) = positiveIntToByteString 10 @ valueIdToByteString valId" |
"valueToByteString (Cond cond thn els) =
    positiveIntToByteString 11 @ observationToByteString cond @ valueToByteString thn @ valueToByteString els" |
"observationToByteString (NotObs subObs) =
    positiveIntToByteString 0 @ observationToByteString subObs" |
"observationToByteString (AndObs lhs rhs) =
    positiveIntToByteString 1 @ observationToByteString lhs @ observationToByteString rhs" |
"observationToByteString (OrObs lhs rhs) =
    positiveIntToByteString 2 @ observationToByteString lhs @ observationToByteString rhs" |
"observationToByteString (ChoseSomething choId) =
    positiveIntToByteString 3 @ choiceIdToByteString choId" |
"observationToByteString TrueObs = positiveIntToByteString 4" |
"observationToByteString FalseObs = positiveIntToByteString 5" |
"observationToByteString (ValueGE lhs rhs) =
    positiveIntToByteString 6 @ valueToByteString lhs @ valueToByteString rhs" |
"observationToByteString (ValueGT lhs rhs) =
    positiveIntToByteString 7 @ valueToByteString lhs @ valueToByteString rhs" |
"observationToByteString (ValueLT lhs rhs) =
    positiveIntToByteString 8 @ valueToByteString lhs @ valueToByteString rhs" |
"observationToByteString (ValueLE lhs rhs) =
    positiveIntToByteString 9 @ valueToByteString lhs @ valueToByteString rhs" |
"observationToByteString (ValueEQ lhs rhs) =
    positiveIntToByteString 10 @ valueToByteString lhs @ valueToByteString rhs"

function (domintros) byteStringToValue :: "ByteString \<Rightarrow> (Value \<times> ByteString) option" and
    byteStringToObservation :: "ByteString \<Rightarrow> (Observation \<times> ByteString) option" where
"byteStringToValue x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow>
   (if y < 6
   then 
     (if y < 3
     then 
       (if y < 1
       then 
         (case byteStringToParty t1 of None \<Rightarrow> None | Some (accId, t2) \<Rightarrow>
         (case byteStringToToken t2 of None \<Rightarrow> None | Some (token, t3) \<Rightarrow>
               Some (AvailableMoney accId token, t3)))
       else 
         (if y < 2
         then (case byteStringToInt t1 of None \<Rightarrow> None | Some (amount, t2) \<Rightarrow>
                    Some (Constant amount, t2))
         else (case byteStringToValue t1 of None \<Rightarrow> None | Some (subVal, t2) \<Rightarrow>
                    Some (NegValue subVal, t2))))
     else
      (case byteStringToValue t1 of None \<Rightarrow> None | Some (lhs, t2) \<Rightarrow>
      (case byteStringToValue t2 of None \<Rightarrow> None | Some (rhs, t3) \<Rightarrow>
       (if y < 5
       then
         (if y < 4
         then Some (AddValue lhs rhs, t3)
         else Some (SubValue lhs rhs, t3))
       else Some (SubValue lhs rhs, t3)))))
   else 
     (if y < 9
     then 
       (if y < 8
       then 
         (if y < 7
         then (case byteStringToInt t1 of None \<Rightarrow> None | Some (n, t2) \<Rightarrow>
              (case byteStringToInt t2 of None \<Rightarrow> None | Some (d, t3) \<Rightarrow>
              (case byteStringToValue t3 of None \<Rightarrow> None | Some (rhs, t4) \<Rightarrow>
                    Some (Scale n d rhs, t4))))
         else (case byteStringToChoiceId t1 of None \<Rightarrow> None | Some (choId, t2) \<Rightarrow>
                    Some (ChoiceValue choId, t2)))
       else Some (SlotIntervalStart, t1))
     else 
       (if y < 11
       then 
         (if y < 10
         then Some (SlotIntervalEnd, t1)
         else (case byteStringToValueId t1 of None \<Rightarrow> None | Some (valId, t2) \<Rightarrow>
                    Some (UseValue valId, t2)))
       else 
         (if y = 11
         then (case byteStringToObservation t1 of None \<Rightarrow> None | Some (obs, t2) \<Rightarrow>
              (case byteStringToValue t2 of None \<Rightarrow> None | Some (thn, t3) \<Rightarrow>
              (case byteStringToValue t3 of None \<Rightarrow> None | Some (els, t4) \<Rightarrow>
                    Some (Cond obs thn els, t4))))
         else None)))))" |
"byteStringToObservation x = 
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow>
   (if y < 6
    then 
     (if y < 3
      then
       (case byteStringToObservation t1 of None \<Rightarrow> None | Some (lhs, t2) \<Rightarrow>
       (if y < 1
        then Some (NotObs lhs, t2)
        else 
         (case byteStringToObservation t2 of None \<Rightarrow> None | Some (rhs, t3) \<Rightarrow>
         (if y < 2
          then Some (AndObs lhs rhs, t3)
          else Some (OrObs lhs rhs, t3)))))
      else 
       (if y < 4
        then 
         (case byteStringToChoiceId t1 of None \<Rightarrow> None | Some (choId, t2) \<Rightarrow>
          Some (ChoseSomething choId, t2))
        else 
         (if y < 5
          then Some (TrueObs, t1)
          else Some (FalseObs, t1))))
    else 
      (case byteStringToValue t1 of None \<Rightarrow> None | Some (lhs, t2) \<Rightarrow>
      (case byteStringToValue t2 of None \<Rightarrow> None | Some (rhs, t3) \<Rightarrow>
      
     (if y < 9
      then 
       (if y < 7
        then Some (ValueGE lhs rhs, t3)
        else 
         (if y < 8
          then Some (ValueGT lhs rhs, t3)
          else Some (ValueLT lhs rhs, t3)))
      else 
       (if y < 10
        then Some (ValueLE lhs rhs, t3)
        else 
         (if y = 10
          then Some (ValueEQ lhs rhs, t3)
          else None)))))))"
  by pat_completeness auto

(*
lemma byteStringToValue_byteStringToObservation_preduceslist : "byteStringToValue_byteStringToObservation_dom (Inl a) \<Longrightarrow> byteStringToValue a = Some (aa, ab) \<Longrightarrow> length ab < length a"
                                                              "byteStringToValue_byteStringToObservation_dom (Inr b) \<Longrightarrow> byteStringToObservation b = Some (ba, bb) \<Longrightarrow> length bb < length b"
  apply (rule byteStringToValue_byteStringToObservation.pinduct[of a])
  apply simp
  subgoal for x
    apply (cases "byteStringToPositiveInt a")
    apply (metis (no_types, lifting) byteStringToValue.psimps option.case_eq_if option.simps(3))
    subgoal for ac
      apply (cases ac)
      subgoal for aca acb
        sorry
      sorry
    sorry
  sorry

termination byteStringToValue
  apply (relation "measure (\<lambda> x . length (case x of Inl y \<Rightarrow> y | Inr z \<Rightarrow> z))")
  apply simp
  using byteStringToPositiveInt_reduceslist apply auto[1]
  using byteStringToInt_reduceslist apply auto[1]
  using byteStringToValue_byteStringToObservation_preduceslist byteStrintToPositiveInt_inverseRoundtrip apply fastforce
  apply (metis (mono_tags, lifting) byteStringToInt_inverseRoundtrip byteStringToInt_reduceslist byteStrintToPositiveInt_inverseRoundtrip in_measure length_append old.sum.simps(5) trans_less_add2)
  using byteStringToInt_reduceslist apply auto[1]
  subgoal for x x2 xa y x2a xb ya
  by (smt byteStringToPositiveInt_injective byteStringToValue_byteStringToObservation_preduceslist(2) in_measure length_append old.sum.simps(5) positiveIntToByteStringToPositiveInt trans_less_add2)
  subgoal for x x2 xa y x2a xb ya x2b xc yb
  using byteStringToValue_byteStringToObservation_preduceslist(1) byteStringToValue_byteStringToObservation_preduceslist(2) byteStrintToPositiveInt_inverseRoundtrip by fastforce
  using byteStringToPositiveInt_reduceslist apply auto[1]
  using byteStringToPositiveInt_reduceslist byteStringToValue_byteStringToObservation_preduceslist(2) apply fastforce
  using byteStringToPositiveInt_reduceslist apply auto[1]
  by (smt byteStringToPositiveInt_injective byteStringToValue_byteStringToObservation_preduceslist(1) in_measure length_append old.sum.simps(5) old.sum.simps(6) positiveIntToByteStringToPositiveInt trans_less_add2)
*)
termination byteStringToValue
  sorry

lemma byteStringToValue_byteStringToObservation_reduceslist_AvailableMoney : "(case byteStringToParty bb of None \<Rightarrow> None | Some (accId, t2) \<Rightarrow> (case byteStringToToken t2 of None \<Rightarrow> None | Some (token, t3) \<Rightarrow> Some (AvailableMoney accId token, t3))) = Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> ba < 6 \<Longrightarrow> ba < 3 \<Longrightarrow> ba < 1 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToParty bb")
  apply simp
  subgoal for a
    apply (cases a)
    subgoal for aa ab
      apply (cases "byteStringToToken ab")
       apply simp
      subgoal for c
      apply (cases c)
        subgoal for ca cb
          using byteStringToParty_reduceslist byteStringToPositiveInt_reduceslist byteStringToToken_reduceslist by fastforce
        done
      done
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_Constant : "(case byteStringToInt bb of None \<Rightarrow> None | Some (amount, t2) \<Rightarrow> Some (Constant amount, t2)) = Some (aa, ab) \<Longrightarrow> byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToInt bb")
   apply (metis option.distinct(1) option.simps(4))
  subgoal for c
    apply (cases c)
    subgoal for ca cb
      by (metis (mono_tags, lifting) Pair_inject byteStringToInt_reduceslist byteStrintToPositiveInt_inverseRoundtrip length_append old.prod.case option.inject option.simps(5) trans_less_add2)
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_NegValue : "(\<And>x2 xa y aa ab. Some (ba, bb) = Some x2 \<Longrightarrow> (xa, y) = x2 \<Longrightarrow> xa < 6 \<Longrightarrow> xa < 3 \<Longrightarrow> \<not> xa < 1 \<Longrightarrow> \<not> xa < 2 \<Longrightarrow> byteStringToValue y = Some (aa, ab) \<Longrightarrow> length ab < length y) \<Longrightarrow>
    (case byteStringToValue bb of None \<Rightarrow> None | Some (subVal, t2) \<Rightarrow> Some (NegValue subVal, t2)) = Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> ba < 6 \<Longrightarrow> ba < 3 \<Longrightarrow> \<not> ba < 1 \<Longrightarrow> \<not> ba < 2 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToValue bb")
   apply simp
  subgoal for a
    apply (cases a)
    subgoal for aa ab
    apply (simp only:refl option.case prod.case)
      using byteStrintToPositiveInt_inverseRoundtrip by fastforce
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_Value_operands : "(\<And>x2 xa y aa ab. Some (ba, bb) = Some x2 \<Longrightarrow> (xa, y) = x2 \<Longrightarrow> xa < 6 \<Longrightarrow> \<not> xa < 3 \<Longrightarrow> byteStringToValue y = Some (aa, ab) \<Longrightarrow> length ab < length y) \<Longrightarrow>
    (\<And>x2 xa y x2a xb ya aa ab. Some (ba, bb) = Some x2 \<Longrightarrow> (xa, y) = x2 \<Longrightarrow> xa < 6 \<Longrightarrow> \<not> xa < 3 \<Longrightarrow> byteStringToValue y = Some x2a \<Longrightarrow> (xb, ya) = x2a \<Longrightarrow> byteStringToValue ya = Some (aa, ab) \<Longrightarrow> length ab < length ya) \<Longrightarrow>
       (case byteStringToValue bb of None \<Rightarrow> None
     | Some (lhs, t2) \<Rightarrow> (case byteStringToValue t2 of None \<Rightarrow> None | Some (rhs, t3) \<Rightarrow> if ba < 5 then if ba < 4 then Some (AddValue lhs rhs, t3) else Some (SubValue lhs rhs, t3) else Some (SubValue lhs rhs, t3))) =
    Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> ba < 6 \<Longrightarrow> \<not> ba < 3 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToValue bb")
  apply (metis (no_types, lifting) option.distinct(1) option.simps(4))
    subgoal for c
      apply (cases c)
      subgoal for ca cb
   apply (cases "byteStringToValue cb")
    apply simp
    subgoal for d
      apply (cases d)
      subgoal for da db
        apply (simp only:refl option.case prod.case if_False)
        by (smt Pair_inject byteStrintToPositiveInt_inverseRoundtrip le_add2 length_append not_less not_less_iff_gr_or_eq option.inject order_trans)
      done
    done
  done
  done


lemma byteStringToValue_byteStringToObservation_reduceslist_Scale : "(\<And>x2 xa y x2a xb ya x2b xc yb aa ab.
        Some (ba, bb) = Some x2 \<Longrightarrow>
        (xa, y) = x2 \<Longrightarrow> \<not> xa < 6 \<Longrightarrow> xa < 9 \<Longrightarrow> xa < 8 \<Longrightarrow> xa < 7 \<Longrightarrow> byteStringToInt y = Some x2a \<Longrightarrow> (xb, ya) = x2a \<Longrightarrow> byteStringToInt ya = Some x2b \<Longrightarrow> (xc, yb) = x2b \<Longrightarrow> byteStringToValue yb = Some (aa, ab) \<Longrightarrow> length ab < length yb) \<Longrightarrow>
(case byteStringToInt bb of None \<Rightarrow> None | Some (n, t2) \<Rightarrow> (case byteStringToInt t2 of None \<Rightarrow> None | Some (d, t3) \<Rightarrow> (case byteStringToValue t3 of None \<Rightarrow> None | Some (rhs, t4) \<Rightarrow> Some (Scale n d rhs, t4)))) = Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> \<not> ba < 6 \<Longrightarrow> ba < 9 \<Longrightarrow> ba < 8 \<Longrightarrow> ba < 7 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToInt bb")
  apply simp
  subgoal for c
    apply (cases c)
    subgoal for ca cb
     apply (cases "byteStringToInt cb")
       apply auto[1]
      subgoal for d
      apply (cases d)
        subgoal for da db
          apply (cases "byteStringToValue db")
           apply simp
          subgoal for e
            apply (cases e)
            subgoal for ea eb
          apply (simp only:prod.case option.case refl)
              apply (rule mp[of "length eb < length x"])
               apply blast
              apply (rule mp[of "length db < length x"])
               apply fastforce
              by (metis byteStringToInt_inverseRoundtrip byteStringToInt_reduceslist byteStrintToPositiveInt_inverseRoundtrip length_append trans_less_add2)
            done
          done
        done
      done
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_ChoiceId : "(case byteStringToChoiceId bb of None \<Rightarrow> None | Some (choId, t2) \<Rightarrow> Some (ChoiceValue choId, t2)) = Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> \<not> ba < 6 \<Longrightarrow> ba < 9 \<Longrightarrow> ba < 8 \<Longrightarrow> \<not> ba < 7 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToChoiceId bb")
  apply simp
  subgoal for c
    apply (cases c)
    subgoal for ca cb
      apply (simp only:prod.case option.case)
      using byteStringToChoiceId_reduceslist byteStringToPositiveInt_reduceslist dual_order.strict_trans by blast
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_UseValue : "(case byteStringToValueId bb of None \<Rightarrow> None | Some (valId, t2) \<Rightarrow> Some (UseValue valId, t2)) = Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (ba, bb) \<Longrightarrow> b = (ba, bb) \<Longrightarrow> \<not> ba < 6 \<Longrightarrow> \<not> ba < 9 \<Longrightarrow> ba < 11 \<Longrightarrow> \<not> ba < 10 \<Longrightarrow> length ab < length x"
  apply (cases "byteStringToValueId bb")
  apply simp
  subgoal for c
    apply (cases c)
    subgoal for ca cb
      apply (simp only:prod.case option.case)
      using byteStringToPositiveInt_reduceslist byteStringToValueId_reduceslist dual_order.strict_trans by blast
    done
  done

lemma byteStringToValue_byteStringToObservation_reduceslist_Cond : "(\<And>x2 y ba bb. Some (da, db) = Some x2 \<Longrightarrow> (11, y) = x2 \<Longrightarrow> byteStringToObservation y = Some (ba, bb) \<Longrightarrow> length bb < length y) \<Longrightarrow>
    (\<And>x2 y x2a xb ya aa ab.
        Some (da, db) = Some x2 \<Longrightarrow> (11, y) = x2 \<Longrightarrow> byteStringToObservation y = Some x2a \<Longrightarrow> (xb, ya) = x2a \<Longrightarrow> byteStringToValue ya = Some (aa, ab) \<Longrightarrow> length ab < length ya) \<Longrightarrow>
    (\<And>x2 y x2a xb ya x2b xc yb aa ab.
        Some (da, db) = Some x2 \<Longrightarrow>
        (11, y) = x2 \<Longrightarrow> byteStringToObservation y = Some x2a \<Longrightarrow> (xb, ya) = x2a \<Longrightarrow> byteStringToValue ya = Some x2b \<Longrightarrow> (xc, yb) = x2b \<Longrightarrow> byteStringToValue yb = Some (aa, ab) \<Longrightarrow> length ab < length yb) \<Longrightarrow>
    (if da = 11 then (case byteStringToObservation db of None \<Rightarrow> None | Some (obs, t2) \<Rightarrow> (case byteStringToValue t2 of None \<Rightarrow> None | Some (thn, t3) \<Rightarrow> (case byteStringToValue t3 of None \<Rightarrow> None | Some (els, t4) \<Rightarrow> Some (Cond obs thn els, t4))))
     else None) =
    Some (aa, ab) \<Longrightarrow>
    byteStringToPositiveInt x = Some (da, db) \<Longrightarrow> d = (da, db) \<Longrightarrow> \<not> da < 6 \<Longrightarrow> \<not> da < 9 \<Longrightarrow> \<not> da < 11 \<Longrightarrow> length ab < length x"
  apply (cases "da = 11")
    apply (simp only:refl if_True)
       apply (cases "byteStringToObservation db")
        apply (simp only:prod.case option.case)
        apply (meson option.distinct(1))
        subgoal for c
          apply (cases c)
          subgoal for ca cb
            apply (cases "byteStringToValue cb")
            apply (simp only:prod.case option.case)
            apply (meson option.distinct(1))
              subgoal for e
              apply (cases e)
                subgoal for ea eb
                  apply (cases "byteStringToValue eb")
                   apply (simp only:prod.case option.case)
                   apply blast
                  subgoal for f
                    apply (cases f)
                    subgoal for fa fb
                      apply (simp only:prod.case option.case)
                    apply (rule mp[of "length fb < length x"])
                     apply blast
                    apply (rule mp[of "length eb < length x"])
                        apply fastforce
                      using byteStrintToPositiveInt_inverseRoundtrip by fastforce
                    done
                  done
                done
              done
            done
          by simp

lemma byteStringToValue_byteStringToObservation_reduceslist : "byteStringToValue a = Some (aa, ab) \<Longrightarrow> length ab < length a"
                                                              "byteStringToObservation b = Some (ba, bb) \<Longrightarrow> length bb < length b"
   apply (induction a and b arbitrary:aa ab and ba bb rule:byteStringToValue_byteStringToObservation.induct)
  (* byteStringToValue_reduceslist *)
  subgoal for x aa ab
    apply (simp only:byteStringToValue.simps[of x])
    apply (cases "byteStringToPositiveInt x")
    apply (simp only:option.case)
    apply blast
    subgoal for d
      apply (cases d)
      subgoal for da db
        apply (simp only:option.case prod.case)
        apply (cases "da < 6")
         apply (simp only:if_True)
          apply (cases "da < 3")
          apply (simp only:if_True)
           apply (cases "da < 1")
           apply (simp only:if_True)
            using byteStringToValue_byteStringToObservation_reduceslist_AvailableMoney apply presburger
              apply (cases "da < 2")
               apply (simp only:if_True)
            apply (metis byteStringToValue_byteStringToObservation_reduceslist_Constant)
              apply (simp only:if_False)
            using byteStringToValue_byteStringToObservation_reduceslist_NegValue apply presburger
             apply (simp only:if_True if_False)
            apply (rule byteStringToValue_byteStringToObservation_reduceslist_Value_operands[of da db aa ab x d])
            apply presburger apply presburger apply blast apply blast apply blast apply linarith apply linarith
        apply (simp only:if_False)
          apply (cases "da < 9")
          apply (simp only:if_True)
           apply (cases "da < 8")
           apply (simp only:if_True)
             apply (cases "da < 7")
               apply (simp only:if_True)
               apply (rule byteStringToValue_byteStringToObservation_reduceslist_Scale[of da db aa ab x])
               apply presburger apply blast apply blast apply blast apply blast apply linarith apply linarith apply linarith
              apply (simp only:if_False)
            using byteStringToValue_byteStringToObservation_reduceslist_ChoiceId apply presburger
              apply (simp only:if_False)
             apply (metis byteStringToPositiveInt_reduceslist option.inject prod.sel(2))
            apply (simp only:if_False)
            apply (cases "da < 11")
            apply (simp only:if_True)
            apply (cases "da < 10")
              apply (simp only:if_True)
            apply (metis byteStringToPositiveInt_reduceslist option.inject prod.sel(2))
             apply (simp only:if_False)
            using byteStringToValue_byteStringToObservation_reduceslist_UseValue apply presburger
            apply (simp only:if_False)
              subgoal premises fact
            apply(rule byteStringToValue_byteStringToObservation_reduceslist_Cond[of da db aa ab x])
                subgoal for x2 y ba bb by (simp add: fact(5))
                subgoal for x2 y x2a xb ya aa ab by (simp add:fact(6))
                subgoal for x2 y x2a xb ya x2b xc yb aa ab by (simp add:fact(7))
                apply (simp_all add:fact)
              done
            done
          done
        done
  (* byteStringToObservation_reduceslist *)
      oops


type_synonym SlotInterval = "Slot \<times> Slot"
type_synonym Bound = "int \<times> int"

fun boundToByteString :: "Bound \<Rightarrow> ByteString" where
"boundToByteString (l, u) = intToByteString l @ intToByteString u"

fun byteStringToBound :: "ByteString \<Rightarrow> (Bound \<times> ByteString) option" where
"byteStringToBound x =
  (case byteStringToInt x of
      None \<Rightarrow> None
    | Some (l, bs1) \<Rightarrow>(case byteStringToInt bs1 of
                      None \<Rightarrow> None
                    | Some (u, bs2) \<Rightarrow> Some ((l, u), bs2)))"

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = any (\<lambda> (l, u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

datatype Action = Deposit AccountId Party Token Value
                | Choice ChoiceId "Bound list"
                | Notify Observation

fun actionToByteString :: "Action \<Rightarrow> ByteString" where
"actionToByteString (Deposit accId party token val) =
   positiveIntToByteString 0 @ partyToByteString accId @ partyToByteString party @ tokenToByteString token @ valueToByteString val" |
"actionToByteString (Choice choId bounds) = positiveIntToByteString 1 @ choiceIdToByteString choId @ listToByteString boundToByteString bounds" |
"actionToByteString (Notify obs) = positiveIntToByteString 2 @ observationToByteString obs"

fun byteStringToAction :: "ByteString \<Rightarrow> (Action \<times> ByteString) option" where
"byteStringToAction x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow>
   (if y < 2
   then
     (if y < 1
     then 
       (if y = 0
       then (case byteStringToParty t1 of None \<Rightarrow> None | Some (accId, t2) \<Rightarrow>
            (case byteStringToParty t2 of None \<Rightarrow> None | Some (party, t3) \<Rightarrow>
            (case byteStringToToken t3 of None \<Rightarrow> None | Some (token, t4) \<Rightarrow>
            (case byteStringToValue t4 of None \<Rightarrow> None | Some (val, t5) \<Rightarrow>
                  Some (Deposit accId party token val, t5)))))
       else None)
     else (case byteStringToChoiceId t1 of None \<Rightarrow> None | Some (choId, t2) \<Rightarrow>
          (case byteStringToList byteStringToBound t2 of None \<Rightarrow> None | Some (bounds, t3) \<Rightarrow>
                Some (Choice choId bounds, t3))))
   else 
     (if y = 3
     then (case byteStringToObservation t1 of None \<Rightarrow> None | Some (obs, t2) \<Rightarrow>
                Some (Notify obs, t2))
     else None)))"

datatype Payee = Account AccountId
               | Party Party

fun payeeToByteString :: "Payee \<Rightarrow> ByteString" where
"payeeToByteString (Account accId) = positiveIntToByteString 0 @ partyToByteString accId" |
"payeeToByteString (Party party) = positiveIntToByteString 1 @ partyToByteString party"

fun byteStringToPayee :: "ByteString \<Rightarrow> (Payee \<times> ByteString) option" where
"byteStringToPayee x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow> (case byteStringToParty t1 of None \<Rightarrow> None | Some (party, t2) \<Rightarrow>
                           if y = 0
                           then (Some (Account party, t2))
                           else (if y = 1
                                 then (Some (Party party, t2))
                                 else None)))"

datatype Case = Case Action Contract
and Contract = Close
             | Pay AccountId Payee Token Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract
             | Assert Observation Contract

function (sequential) caseToByteString :: "Case \<Rightarrow> ByteString" and
                      contractToByteString :: "Contract \<Rightarrow> ByteString" where
"caseToByteString (Case action cont) = actionToByteString action @ contractToByteString cont" |
"contractToByteString Close = positiveIntToByteString 0" |
"contractToByteString (Pay accId payee token val cont) = positiveIntToByteString 1 @ partyToByteString accId @ payeeToByteString payee
                                                       @ tokenToByteString token @ valueToByteString val @ contractToByteString cont" |
"contractToByteString (If obs cont1 cont2) = positiveIntToByteString 2 @ observationToByteString obs @ contractToByteString cont1 @ contractToByteString cont2" |
"contractToByteString (When caseList timeout cont) = positiveIntToByteString 3 @ listToByteString caseToByteString caseList @ intToByteString timeout @ contractToByteString cont" |
"contractToByteString (Let valId val cont) = positiveIntToByteString 4 @ valueIdToByteString valId @ valueToByteString val @ contractToByteString cont" |
"contractToByteString (Assert obs cont) = positiveIntToByteString 5 @ observationToByteString obs @ contractToByteString cont"
  apply auto
  by pat_completeness
termination
  sorry


function (sequential) byteStringToCase :: "ByteString \<Rightarrow> (Case \<times> ByteString) option" and
                      byteStringToContract :: "ByteString \<Rightarrow> (Contract \<times> ByteString) option" where
"byteStringToCase t1 = (case byteStringToAction t1 of None \<Rightarrow> None | Some (action, t2) \<Rightarrow>
                       (case byteStringToContract t2 of None \<Rightarrow> None | Some (cont, t3) \<Rightarrow>
                       Some (Case action cont, t3)))" |
"byteStringToContract x =
  (case byteStringToPositiveInt x of
     None \<Rightarrow> None
   | Some (y, t1) \<Rightarrow>
    (if y < 3
     then (if y < 1
           then (if y = 0
                 then Some (Close, t1)
                 else None)
           else (if y < 2
                 then (case byteStringToParty t1 of None \<Rightarrow> None | Some (accId, t2) \<Rightarrow>
                      (case byteStringToPayee t2 of None \<Rightarrow> None | Some (payee, t3) \<Rightarrow>
                      (case byteStringToToken t3 of None \<Rightarrow> None | Some (token, t4) \<Rightarrow>
                      (case byteStringToValue t4 of None \<Rightarrow> None | Some (val, t5) \<Rightarrow>
                      (case byteStringToContract t5 of None \<Rightarrow> None | Some (cont, t6) \<Rightarrow>
                      Some (Pay accId payee token val cont, t6))))))
                 else (case byteStringToObservation t1 of None \<Rightarrow> None | Some (obs, t2) \<Rightarrow>
                      (case byteStringToContract t2 of None \<Rightarrow> None | Some (cont1, t3) \<Rightarrow>
                      (case byteStringToContract t3 of None \<Rightarrow> None | Some (cont2, t4) \<Rightarrow>
                      Some (If obs cont1 cont2, t4))))))
     else (if y < 5
           then  (if y < 4
                  then (case byteStringToList byteStringToCase t1 of None \<Rightarrow> None | Some (caseList, t2) \<Rightarrow>
                       (case byteStringToInt t2 of None \<Rightarrow> None | Some (timeout, t3) \<Rightarrow>
                       (case byteStringToContract t3 of None \<Rightarrow> None | Some (cont, t4) \<Rightarrow>
                       Some (When caseList timeout cont, t4))))
                  else (case byteStringToValueId t1 of None \<Rightarrow> None | Some (valId, t2) \<Rightarrow>
                       (case byteStringToValue t2 of None \<Rightarrow> None | Some (val, t3) \<Rightarrow>
                       (case byteStringToContract t3 of None \<Rightarrow> None | Some (cont, t4) \<Rightarrow>
                       Some (Let valId val cont, t4)))))
           else (if y = 5
                 then (case byteStringToObservation t1 of None \<Rightarrow> None | Some (obs, t2) \<Rightarrow>
                      (case byteStringToContract t2 of None \<Rightarrow> None | Some (cont, t3) \<Rightarrow>
                      Some (Assert obs cont, t3)))
                 else None))))"
  apply auto
  by pat_completeness
termination
  sorry

type_synonym Accounts = "((AccountId \<times> Token) \<times> Money) list"

record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minSlot :: Slot

fun valid_state :: "State \<Rightarrow> bool" where
"valid_state state = (valid_map (accounts state)
                     \<and> valid_map (choices state)
                     \<and> valid_map (boundValues state))"

record Environment = slotInterval :: SlotInterval

datatype Input = IDeposit AccountId Party Token Money
               | IChoice ChoiceId ChosenNum
               | INotify

(* Processing of slot interval *)
datatype IntervalError = InvalidInterval SlotInterval
                       | IntervalInPastError Slot SlotInterval

datatype IntervalResult = IntervalTrimmed Environment State
                        | IntervalError IntervalError

fun fixInterval :: "SlotInterval \<Rightarrow> State \<Rightarrow> IntervalResult" where
"fixInterval (low, high) state =
   (let curMinSlot = minSlot state in
    let newLow = max low curMinSlot in
    let curInterval = (newLow, high) in
    let env = \<lparr> slotInterval = curInterval \<rparr> in
    let newState = state \<lparr> minSlot := newLow \<rparr> in
    (if (high < low)
     then IntervalError (InvalidInterval (low, high))
     else (if (high < curMinSlot)
           then IntervalError (IntervalInPastError curMinSlot (low, high))
           else IntervalTrimmed env newState)))"

(* EVALUATION *)

fun signum :: "int \<Rightarrow> int" where
"signum x = (if x > 0 then 1 else if x = 0 then 0 else -1)"

fun quot :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "quot" 70) where
"x quot y = (if ((x < 0) = (y < 0)) then x div y else -(abs x div abs y))"

fun rem :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "rem" 70) where
"x rem y = x - (x quot y) * y"

fun quotRem :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" (infixl "quotRem" 70) where
"x quotRem y = (x quot y, x rem y)"

fun evalValue :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> int" and evalObservation :: "Environment \<Rightarrow> State \<Rightarrow> Observation \<Rightarrow> bool" where
"evalValue env state (AvailableMoney accId token) =
    findWithDefault 0 (accId, token) (accounts state)" |
"evalValue env state (Constant integer) = integer" |
"evalValue env state (NegValue val) = uminus (evalValue env state val)" |
"evalValue env state (AddValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs" |
"evalValue env state (SubValue lhs rhs) =
    evalValue env state lhs - evalValue env state rhs" |
"evalValue env state (MulValue lhs rhs) =
    evalValue env state lhs * evalValue env state rhs" |
"evalValue env state (Scale n d rhs) = 
    (let nn = evalValue env state rhs * n in
     let (q, r) = nn quotRem d in
     if abs r * 2 < abs d then q else q + signum nn * signum d)" |
"evalValue env state (ChoiceValue choId) =
    findWithDefault 0 choId (choices state)" |
"evalValue env state (SlotIntervalStart) = fst (slotInterval env)" |
"evalValue env state (SlotIntervalEnd) = snd (slotInterval env)" |
"evalValue env state (UseValue valId) =
    findWithDefault 0 valId (boundValues state)" |
"evalValue env state (Cond cond thn els) =
    (if evalObservation env state cond then evalValue env state thn else evalValue env state els)" |
"evalObservation env state (AndObs lhs rhs) =
    (evalObservation env state lhs \<and> evalObservation env state rhs)" |
"evalObservation env state (OrObs lhs rhs) =
    (evalObservation env state lhs \<or> evalObservation env state rhs)" |
"evalObservation env state (NotObs subObs) =
    (\<not> evalObservation env state subObs)" |
"evalObservation env state (ChoseSomething choId) =
    (member choId (choices state))" |
"evalObservation env state (ValueGE lhs rhs) =
    (evalValue env state lhs \<ge> evalValue env state rhs)" |
"evalObservation env state (ValueGT lhs rhs) =
    (evalValue env state lhs > evalValue env state rhs)" |
"evalObservation env state (ValueLT lhs rhs) =
    (evalValue env state lhs < evalValue env state rhs)" |
"evalObservation env state (ValueLE lhs rhs) =
    (evalValue env state lhs \<le> evalValue env state rhs)" |
"evalObservation env state (ValueEQ lhs rhs) =
    (evalValue env state lhs = evalValue env state rhs)" |
"evalObservation env state TrueObs = True" |
"evalObservation env state FalseObs = False"

lemma evalDoubleNegValue :
  "evalValue env sta (NegValue (NegValue x)) = evalValue env sta x"
  by auto

lemma evalNegValue :
  "evalValue env sta (AddValue x (NegValue x)) = 0"
  by auto

lemma evalMulValue :
  "evalValue env sta (MulValue x (Constant 0)) = 0"
  by auto

lemma evalSubValue :
  "evalValue env sta (SubValue (AddValue x y) y) = evalValue env sta x"
  by auto

lemma evalScaleByZeroIsZero :
  "evalValue env sta (Scale 0 1 x) = 0"
  by auto

lemma evalScaleByOneIsX : "evalValue env sta (Scale 1 1 x) = evalValue env sta x"
  apply simp
  by (smt div_by_1)

lemma evalScaleMultiplies :
  "evalValue env sta (Scale a b (Constant (x * c))) = evalValue env sta (Scale (x * a) b (Constant c))"
  apply (simp only:evalValue.simps)
  by (simp add: mult.commute mult.left_commute)

lemma quotMultiplyEquivalence : "c \<noteq> 0 \<Longrightarrow> (c * a) quot (c * b) = a quot b"
  apply auto
  apply (simp_all add: mult_less_0_iff)
  apply (metis div_mult_mult1 less_irrefl mult_minus_right)
  apply (smt div_minus_minus mult_minus_right nonzero_mult_div_cancel_left zdiv_zmult2_eq)
  apply (metis div_minus_right div_mult_mult1 mult_minus_right)
  by (metis div_mult_mult1 less_irrefl mult_minus_right)

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
  by (metis (no_types, hide_lams) diff_minus_eq_add mult_minus_left remMultiplySmalle_aux2)

lemma evalScaleMultiplyFractByConstant :
  "c \<noteq> 0 \<Longrightarrow> evalValue env sta (Scale (c * a) (c * b) x) = evalValue env sta (Scale a b x)"
  apply (simp only:evalValue.simps Let_def)
  apply (cases "evalValue env sta x * (c * a) quotRem (c * b)")
  apply (cases "evalValue env sta x * a quotRem b")
  subgoal for cq cr q r
    apply (auto split:prod.splits simp only:Let_def)
    apply (cases "\<bar>cr\<bar> * 2 < \<bar>c * b\<bar>")
    apply (simp only:if_True)
    apply (cases "\<bar>r\<bar> * 2 < \<bar>b\<bar>")
    apply (simp only:if_True)
    apply (metis mult.left_commute prod.sel(1) quotMultiplyEquivalence quotRem.simps)
    apply (simp only:if_False)
    apply (metis mult.left_commute quotRem.simps remMultiplySmaller snd_conv)
    apply (cases "\<bar>r\<bar> * 2 < \<bar>b\<bar>")
    apply (simp only:if_False if_True)
    apply (metis mult.left_commute quotRem.simps remMultiplySmaller snd_conv)
    apply (simp only:if_True if_False)
    apply (simp only:quotRem.simps)
    by (smt Pair_inject mult.left_commute mult_cancel_left1 mult_eq_0_iff mult_neg_neg mult_pos_pos quotMultiplyEquivalence signum.simps zero_less_mult_pos zero_less_mult_pos2 zmult_eq_1_iff)
  done

fun refundOne :: "Accounts \<Rightarrow>
                  ((Party \<times> Token \<times> Money) \<times> Accounts) option" where
"refundOne (((accId, tok), money)#rest) =
   (if money > 0 then Some ((accId, tok, money), rest) else refundOne rest)" |
"refundOne [] = None"

lemma refundOneShortens : "refundOne acc = Some (c, nacc) \<Longrightarrow>
                           length nacc < length acc"
  apply (induction acc)
  apply simp
  by (metis Pair_inject length_Cons less_Suc_eq list.distinct(1)
            list.inject option.inject refundOne.elims)

datatype Payment = Payment AccountId Payee Token Money

datatype ReduceEffect = ReduceNoPayment
                      | ReduceWithPayment Payment

fun moneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Accounts \<Rightarrow> Money" where
"moneyInAccount accId token accountsV = findWithDefault 0 (accId, token) accountsV"

fun updateMoneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Money \<Rightarrow>
                             Accounts \<Rightarrow>
                             Accounts" where
"updateMoneyInAccount accId token money accountsV =
  (if money \<le> 0
   then MList.delete (accId, token) accountsV
   else MList.insert (accId, token) money accountsV)"

fun addMoneyToAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Money \<Rightarrow>
                          Accounts \<Rightarrow>
                          Accounts" where
"addMoneyToAccount accId token money accountsV =
  (let balance = moneyInAccount accId token accountsV in
   let newBalance = balance + money in
   if money \<le> 0
   then accountsV
   else updateMoneyInAccount accId token newBalance accountsV)"

fun giveMoney :: "AccountId \<Rightarrow> Payee \<Rightarrow> Token \<Rightarrow> Money \<Rightarrow> Accounts \<Rightarrow>
                  (ReduceEffect \<times> Accounts)" where
"giveMoney accountId payee token money accountsV =
  (let newAccounts = case payee of
                        Party _ \<Rightarrow> accountsV
                      | Account accId \<Rightarrow> addMoneyToAccount accId token money accountsV
   in (ReduceWithPayment (Payment accountId payee token money), newAccounts))"

lemma giveMoneyIncOne : "giveMoney sa p t m a = (e, na) \<Longrightarrow> length na \<le> length a + 1"
  apply (cases p)
  apply (cases "m \<le> 0")
  apply auto
  by (smt Suc_eq_plus1 delete_length insert_length le_Suc_eq)

(* REDUCE *)

datatype ReduceWarning = ReduceNoWarning
                       | ReduceNonPositivePay AccountId Payee Token Money
                       | ReducePartialPay AccountId Payee Token Money Money
                       | ReduceShadowing ValueId int int
                       | ReduceAssertionFailed

datatype ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                          | NotReduced
                          | AmbiguousSlotIntervalReductionError

fun reduceContractStep :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceStepResult" where
"reduceContractStep _ state Close =
  (case refundOne (accounts state) of
     Some ((party, token, money), newAccount) \<Rightarrow>
       let newState = state \<lparr> accounts := newAccount \<rparr> in
       Reduced ReduceNoWarning (ReduceWithPayment (Payment party (Party party) token money)) newState Close
   | None \<Rightarrow> NotReduced)" |
"reduceContractStep env state (Pay accId payee token val cont) =
  (let moneyToPay = evalValue env state val in
   if moneyToPay \<le> 0
   then (let warning = ReduceNonPositivePay accId payee token moneyToPay in
         Reduced warning ReduceNoPayment state cont)
   else (let balance = moneyInAccount accId token (accounts state) in
        (let paidMoney = min balance moneyToPay in
         let newBalance = balance - paidMoney in
         let newAccs = updateMoneyInAccount accId token newBalance (accounts state) in
         let warning = (if paidMoney < moneyToPay
                        then ReducePartialPay accId payee token paidMoney moneyToPay
                        else ReduceNoWarning) in
         let (payment, finalAccs) = giveMoney accId payee token paidMoney newAccs in
         Reduced warning payment (state \<lparr> accounts := finalAccs \<rparr>) cont)))" |
"reduceContractStep env state (If obs cont1 cont2) =
  (let cont = (if evalObservation env state obs
               then cont1
               else cont2) in
   Reduced ReduceNoWarning ReduceNoPayment state cont)" |
"reduceContractStep env state (When _ timeout cont) =
  (let (startSlot, endSlot) = slotInterval env in
   if endSlot < timeout
   then NotReduced
   else (if timeout \<le> startSlot
         then Reduced ReduceNoWarning ReduceNoPayment state cont
         else AmbiguousSlotIntervalReductionError))" |
"reduceContractStep env state (Let valId val cont) =
  (let evaluatedValue = evalValue env state val in
   let boundVals = boundValues state in
   let newState = state \<lparr> boundValues := MList.insert valId evaluatedValue boundVals \<rparr> in
   let warn = case lookup valId boundVals of
                Some oldVal \<Rightarrow> ReduceShadowing valId oldVal evaluatedValue
              | None \<Rightarrow> ReduceNoWarning in
   Reduced warn ReduceNoPayment newState cont)" |
"reduceContractStep env state (Assert obs cont) =
  (let warning = if evalObservation env state obs
                 then ReduceNoWarning
                 else ReduceAssertionFailed
   in Reduced warning ReduceNoPayment state cont)"

datatype ReduceResult = ContractQuiescent "ReduceWarning list" "Payment list"
                                          State Contract
                      | RRAmbiguousSlotIntervalError

fun evalBound :: "State \<Rightarrow> Contract \<Rightarrow> nat" where
"evalBound sta cont = length (accounts sta) + 2 * (size cont)"

lemma reduceContractStepReducesSize_Refund_aux :
  "refundOne (accounts sta) = Some ((party, money), newAccount) \<Longrightarrow>
   length (accounts (sta\<lparr>accounts := newAccount\<rparr>)) < length (accounts sta)"
  by (simp add: refundOneShortens)

lemma reduceContractStepReducesSize_Refund_aux2 :
  "Reduced ReduceNoWarning (ReduceWithPayment (Payment accId (Party party) token money))
          (sta\<lparr>accounts := newAccount\<rparr>) Close =
   Reduced twa tef nsta nc \<Longrightarrow>
   c = Close \<Longrightarrow>
   refundOne (accounts sta) = Some ((party, token, money), newAccount) \<Longrightarrow>
   length (accounts nsta) + 2 * size nc < length (accounts sta)"
  apply simp
  using reduceContractStepReducesSize_Refund_aux by blast

lemma reduceContractStepReducesSize_Refund :
  "(case a of
          ((party, token, money), newAccount) \<Rightarrow>
            Reduced ReduceNoWarning (ReduceWithPayment (Payment accId (Party party) token money))
             (sta\<lparr>accounts := newAccount\<rparr>) Close) =
         Reduced twa tef nsta nc \<Longrightarrow>
         c = Close \<Longrightarrow>
         refundOne (accounts sta) = Some a \<Longrightarrow>
         length (accounts nsta) + 2 * size nc < length (accounts sta)"
  apply (cases a)
  apply simp
  using reduceContractStepReducesSize_Refund_aux2 by fastforce

lemma zeroMinIfGT : "x > 0 \<Longrightarrow> min 0 x = (0 :: int)"
  by simp

lemma reduceContractStepReducesSize_Pay_aux :
  "length z \<le> length x \<Longrightarrow>
   giveMoney accId x22 tok a z = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  by (metis (no_types, lifting) Suc_eq_plus1 giveMoneyIncOne leI le_trans not_less_eq_eq)

lemma reduceContractStepReducesSize_Pay_aux2 :
  "giveMoney accId dst tok a (MList.delete (src, tok) x) = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  using delete_length reduceContractStepReducesSize_Pay_aux by blast

lemma reduceContractStepReducesSize_Pay_aux3 :
  "sta\<lparr>accounts := b\<rparr> = nsta \<Longrightarrow>
   giveMoney accId dst tok a (MList.delete (src, tok) (accounts sta)) = (tef, b) \<Longrightarrow>
   length (accounts nsta) < Suc (Suc (length (accounts sta)))"
  using reduceContractStepReducesSize_Pay_aux2 by fastforce

lemma reduceContractStepReducesSize_Pay_aux4 :
  "lookup (k, tok) x = Some w \<Longrightarrow>
   giveMoney accId dst tok a (MList.insert (k, tok) v x) = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  by (metis One_nat_def add.right_neutral add_Suc_right giveMoneyIncOne insert_existing_length le_imp_less_Suc)

lemma reduceContractStepReducesSize_Pay_aux5 :
"sta\<lparr>accounts := ba\<rparr> = nsta \<Longrightarrow>
 lookup (src, tok) (accounts sta) = Some a \<Longrightarrow>
 giveMoney accId dst tok (evalValue env sta am) (MList.insert (src, tok) (a - evalValue env sta am) (accounts sta)) = (tef, ba) \<Longrightarrow>
 length (accounts nsta) < Suc (Suc (length (accounts sta)))"
  using reduceContractStepReducesSize_Pay_aux4 by fastforce

lemma reduceContractStepReducesSize_Pay_aux6 :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst tok am y \<Longrightarrow>
   evalValue env sta am > 0 \<Longrightarrow>
   lookup (src, tok) (accounts sta) = Some a \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  apply (cases "a < evalValue env sta am")
  apply (simp add:min_absorb1)
  apply (cases "giveMoney src dst tok a (MList.delete (src, tok) (accounts sta))")
  using reduceContractStepReducesSize_Pay_aux3 apply fastforce
  apply (cases "a = evalValue env sta am")
  apply (cases "giveMoney src dst tok (evalValue env sta am) (MList.delete (src, tok) (accounts sta))")
  apply (simp add:min_absorb2)
  using reduceContractStepReducesSize_Pay_aux3 apply fastforce
  apply (cases "giveMoney src dst tok (evalValue env sta am) (MList.insert (src, tok) (a - evalValue env sta am) (accounts sta))")
  apply (simp add:min_absorb2)
  using reduceContractStepReducesSize_Pay_aux5 by fastforce

lemma reduceContractStepReducesSize_Pay :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst tok am y \<Longrightarrow> evalBound nsta nc < evalBound sta c"
  apply (cases "evalValue env sta am \<le> 0")
  apply auto[1]
  apply (cases "lookup (src, tok) (accounts sta)")
  apply (cases "evalValue env sta am > 0")
  apply (cases "giveMoney src dst tok 0 (MList.delete (src, tok) (accounts sta))")
  apply (simp add:zeroMinIfGT)
  using reduceContractStepReducesSize_Pay_aux3 apply fastforce
  apply simp
  using reduceContractStepReducesSize_Pay_aux6 by auto

lemma reduceContractStepReducesSize_When :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = When cases timeout cont \<Longrightarrow>
   slotInterval env = (startSlot, endSlot) \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  apply simp
  apply (cases "endSlot < timeout")
  apply simp
  apply (cases "timeout \<le> startSlot")
  by simp_all

lemma reduceContractStepReducesSize_Let_aux :
  "Reduced (ReduceShadowing vId a (evalValue env sta val)) ReduceNoPayment
         (sta\<lparr>boundValues := MList.insert vId (evalValue env sta val) (boundValues sta)\<rparr>) cont =
    Reduced twa tef nsta nc \<Longrightarrow>
   c = Contract.Let vId val cont \<Longrightarrow>
   lookup vId (boundValues sta) = Some a \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  by auto

lemma reduceContractStepReducesSize_Let :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Contract.Let vId val cont \<Longrightarrow> evalBound nsta nc < evalBound sta c"
  apply (cases "lookup vId (boundValues sta)")
  apply auto[1]
  by (metis ReduceStepResult.inject reduceContractStep.simps(5) reduceContractStepReducesSize_Let_aux)

lemma reduceContractStepReducesSize :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
     (evalBound nsta nc) < (evalBound sta c)"
  apply (cases c)
  apply (cases "refundOne (accounts sta)")
  apply simp
  apply simp
  using reduceContractStepReducesSize_Refund apply fastforce
  using reduceContractStepReducesSize_Pay apply blast
  apply auto[1]
  apply (meson eq_fst_iff reduceContractStepReducesSize_When)
  using reduceContractStepReducesSize_Let apply blast
  by simp

function (sequential) reductionLoop :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceWarning list \<Rightarrow>
                                        Payment list \<Rightarrow> ReduceResult" where
"reductionLoop env state contract warnings payments =
  (case reduceContractStep env state contract of
     Reduced warning effect newState ncontract \<Rightarrow>
       let newWarnings = (if warning = ReduceNoWarning
                          then warnings
                          else warning # warnings) in
       let newPayments = (case effect of
                            ReduceWithPayment payment \<Rightarrow> payment # payments
                          | ReduceNoPayment \<Rightarrow> payments) in
       reductionLoop env newState ncontract newWarnings newPayments
   | AmbiguousSlotIntervalReductionError \<Rightarrow> RRAmbiguousSlotIntervalError
   | NotReduced \<Rightarrow> ContractQuiescent (rev warnings) (rev payments) state contract)"
  by pat_completeness auto
termination reductionLoop
  apply (relation "measure (\<lambda>(_, (state, (contract, _))) . evalBound state contract)")
  apply blast
  using reduceContractStepReducesSize by auto

fun reduceContractUntilQuiescent :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceResult" where
"reduceContractUntilQuiescent env state contract = reductionLoop env state contract [] []"

datatype ApplyWarning = ApplyNoWarning
                      | ApplyNonPositiveDeposit Party AccountId Token int

datatype ApplyResult = Applied ApplyWarning State Contract
                     | ApplyNoMatchError

fun applyCases :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Case list \<Rightarrow> ApplyResult" where
"applyCases env state (IDeposit accId1 party1 tok1 amount)
            (Cons (Case (Deposit accId2 party2 tok2 val) cont) rest) =
  (if (accId1 = accId2 \<and> party1 = party2 \<and> tok1 = tok2
        \<and> amount = evalValue env state val)
   then let warning = if amount > 0
                      then ApplyNoWarning
                      else ApplyNonPositiveDeposit party1 accId2 tok2 amount in
        let newState = state \<lparr> accounts := addMoneyToAccount accId1 tok1 amount (accounts state) \<rparr> in
        Applied warning newState cont
   else applyCases env state (IDeposit accId1 party1 tok1 amount) rest)" |
"applyCases env state (IChoice choId1 choice)
            (Cons (Case (Choice choId2 bounds) cont) rest) =
  (if (choId1 = choId2 \<and> inBounds choice bounds)
   then let newState = state \<lparr> choices := MList.insert choId1 choice (choices state) \<rparr> in
        Applied ApplyNoWarning newState cont
   else applyCases env state (IChoice choId1 choice) rest)" |
"applyCases env state INotify (Cons (Case (Notify obs) cont) rest) =
  (if evalObservation env state obs
   then Applied ApplyNoWarning state cont
   else applyCases env state INotify rest)" |
"applyCases env state (IDeposit accId1 party1 tok1 amount) (Cons _ rest) =
  applyCases env state (IDeposit accId1 party1 tok1 amount) rest" |
"applyCases env state (IChoice choId1 choice) (Cons _ rest) =
  applyCases env state (IChoice choId1 choice) rest" |
"applyCases env state INotify (Cons _ rest) =
  applyCases env state INotify rest" |
"applyCases env state acc Nil = ApplyNoMatchError"

fun applyInput :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Contract \<Rightarrow> ApplyResult" where
"applyInput env state input (When cases t cont) = applyCases env state input cases" |
"applyInput env state input c = ApplyNoMatchError"

datatype TransactionWarning = TransactionNonPositiveDeposit Party AccountId Token int
                            | TransactionNonPositivePay AccountId Payee Token int
                            | TransactionPartialPay AccountId Payee Token Money Money
                            | TransactionShadowing ValueId int int
                            | TransactionAssertionFailed

fun convertReduceWarnings :: "ReduceWarning list \<Rightarrow> TransactionWarning list" where
"convertReduceWarnings Nil = Nil" |
"convertReduceWarnings (Cons ReduceNoWarning rest) =
   convertReduceWarnings rest" |
"convertReduceWarnings (Cons (ReduceNonPositivePay accId payee tok amount) rest) =
   Cons (TransactionNonPositivePay accId payee tok amount)
        (convertReduceWarnings rest)" |
"convertReduceWarnings (Cons (ReducePartialPay accId payee tok paid expected) rest) =
   Cons (TransactionPartialPay accId payee tok paid expected)
        (convertReduceWarnings rest)" |
"convertReduceWarnings (Cons (ReduceShadowing valId oldVal newVal) rest) =
   Cons (TransactionShadowing valId oldVal newVal)
        (convertReduceWarnings rest)" |
"convertReduceWarnings (Cons ReduceAssertionFailed rest) =
   Cons TransactionAssertionFailed (convertReduceWarnings rest)"

fun convertApplyWarning :: "ApplyWarning \<Rightarrow> TransactionWarning list" where
"convertApplyWarning ApplyNoWarning = Nil" |
"convertApplyWarning (ApplyNonPositiveDeposit party accId tok amount) =
   Cons (TransactionNonPositiveDeposit party accId tok amount) Nil"

datatype ApplyAllResult = ApplyAllSuccess "TransactionWarning list" "Payment list"
                                     State Contract
                        | ApplyAllNoMatchError
                        | ApplyAllAmbiguousSlotIntervalError

fun applyAllLoop :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                    TransactionWarning list \<Rightarrow> Payment list \<Rightarrow>
                    ApplyAllResult" where
"applyAllLoop env state contract inputs warnings payments =
   (case reduceContractUntilQuiescent env state contract of
      RRAmbiguousSlotIntervalError \<Rightarrow> ApplyAllAmbiguousSlotIntervalError
    | ContractQuiescent reduceWarns pays curState cont \<Rightarrow>
       (case inputs of
          Nil \<Rightarrow> ApplyAllSuccess (warnings @ (convertReduceWarnings reduceWarns))
                                 (payments @ pays) curState cont
        | Cons input rest \<Rightarrow>
           (case applyInput env curState input cont of
              Applied applyWarn newState cont \<Rightarrow>
                  applyAllLoop env newState cont rest
                               (warnings @ (convertReduceWarnings reduceWarns)
                                         @ (convertApplyWarning applyWarn))
                               (payments @ pays)
            | ApplyNoMatchError \<Rightarrow> ApplyAllNoMatchError)))"

fun applyAllInputs :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                 ApplyAllResult" where
"applyAllInputs env state contract inputs = applyAllLoop env state contract inputs Nil Nil"

type_synonym TransactionSignatures = "Party list"

datatype TransactionError = TEAmbiguousSlotIntervalError
                          | TEApplyNoMatchError
                          | TEIntervalError IntervalError
                          | TEUselessTransaction

record TransactionOutputRecord = txOutWarnings :: "TransactionWarning list"
                                 txOutPayments :: "Payment list"
                                 txOutState :: State
                                 txOutContract :: Contract

datatype TransactionOutput = TransactionOutput TransactionOutputRecord
                           | TransactionError TransactionError

record Transaction = interval :: SlotInterval
                     inputs :: "Input list"

fun computeTransaction :: "Transaction \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> TransactionOutput" where
"computeTransaction tx state contract =
  (let inps = inputs tx in
   case fixInterval (interval tx) state of
     IntervalTrimmed env fixSta \<Rightarrow>
       (case applyAllInputs env fixSta contract inps of
          ApplyAllSuccess warnings payments newState cont \<Rightarrow>
            if ((contract = cont) \<and> ((contract \<noteq> Close) \<or> (accounts state = [])))
            then TransactionError TEUselessTransaction
            else TransactionOutput \<lparr> txOutWarnings = warnings
                                   , txOutPayments = payments
                                   , txOutState = newState
                                   , txOutContract = cont \<rparr>
        | ApplyAllNoMatchError \<Rightarrow> TransactionError TEApplyNoMatchError
        | ApplyAllAmbiguousSlotIntervalError \<Rightarrow> TransactionError TEAmbiguousSlotIntervalError)
     | IntervalError error \<Rightarrow> TransactionError (TEIntervalError error))"

fun playTraceAux :: "TransactionOutputRecord \<Rightarrow> Transaction list \<Rightarrow> TransactionOutput" where
"playTraceAux res Nil = TransactionOutput res" |
"playTraceAux \<lparr> txOutWarnings = warnings
              , txOutPayments = payments
              , txOutState = state
              , txOutContract = cont \<rparr> (Cons h t) =
   (let transRes = computeTransaction h state cont in
    case transRes of
      TransactionOutput transResRec \<Rightarrow> playTraceAux (transResRec \<lparr> txOutPayments := payments @ (txOutPayments transResRec)
                                                                 , txOutWarnings := warnings @ (txOutWarnings transResRec) \<rparr>) t
    | TransactionError _ \<Rightarrow> transRes)"

fun emptyState :: "Slot \<Rightarrow> State" where
"emptyState sl = \<lparr> accounts = MList.empty
                 , choices = MList.empty
                 , boundValues = MList.empty
                 , minSlot = sl \<rparr>"

fun playTrace :: "Slot \<Rightarrow> Contract \<Rightarrow> Transaction list \<Rightarrow> TransactionOutput" where
"playTrace sl c t = playTraceAux \<lparr> txOutWarnings = Nil
                                 , txOutPayments = Nil
                                 , txOutState = emptyState sl
                                 , txOutContract = c \<rparr> t"

(* Extra functions *)

type_synonym TransactionOutcomes = "(Party \<times> Money) list"

definition "emptyOutcome = (MList.empty :: TransactionOutcomes)"

lemma emptyOutcomeValid : "valid_map emptyOutcome"
  using MList.valid_empty emptyOutcome_def by auto

fun isEmptyOutcome :: "TransactionOutcomes \<Rightarrow> bool" where
"isEmptyOutcome trOut = all (\<lambda> (x, y) \<Rightarrow> y = 0) trOut"

fun addOutcome :: "Party \<Rightarrow> Money \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"addOutcome party diffValue trOut =
   (let newValue = case MList.lookup party trOut of
                     Some value \<Rightarrow> value + diffValue
                   | None \<Rightarrow> diffValue in
    MList.insert party newValue trOut)"

fun combineOutcomes :: "TransactionOutcomes \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"combineOutcomes x y = MList.unionWith plus x y"

fun getPartiesFromReduceEffect :: "ReduceEffect list \<Rightarrow> (Party \<times> Token \<times> Money) list" where
"getPartiesFromReduceEffect (Cons (ReduceWithPayment (Payment src (Party p) tok m)) t) =
   Cons (p, tok, -m) (getPartiesFromReduceEffect t)" |
"getPartiesFromReduceEffect (Cons x t) = getPartiesFromReduceEffect t" |
"getPartiesFromReduceEffect Nil = Nil"

fun getPartiesFromInput :: "Input list \<Rightarrow> (Party \<times> Token \<times> Money) list" where
"getPartiesFromInput (Cons (IDeposit _ p tok m) t) =
   Cons (p, tok, m) (getPartiesFromInput t)" |
"getPartiesFromInput (Cons x t) = getPartiesFromInput t" |
"getPartiesFromInput Nil = Nil"

fun getOutcomes :: "ReduceEffect list \<Rightarrow> Input list \<Rightarrow> TransactionOutcomes" where
"getOutcomes eff inp =
   foldl (\<lambda> acc (p, t, m) . addOutcome p m acc) emptyOutcome
         ((getPartiesFromReduceEffect eff) @ (getPartiesFromInput inp))"

fun addSig :: "Party list \<Rightarrow> Input \<Rightarrow> Party list" where
"addSig acc (IDeposit _ p _ _) = SList.insert p acc" |
"addSig acc (IChoice (ChoiceId _ p) _) = SList.insert p acc" |
"addSig acc INotify = acc"

fun getSignatures :: "Input list \<Rightarrow> TransactionSignatures" where
"getSignatures l = foldl addSig SList.empty l"

fun isQuiescent :: "Contract \<Rightarrow> State \<Rightarrow> bool" where
"isQuiescent Close state = (accounts state = [])" |
"isQuiescent (When _ _ _) _ = True" |
"isQuiescent _ _ = False"

fun maxTimeContract :: "Contract \<Rightarrow> int"
and maxTimeCase :: "Case \<Rightarrow> int" where
"maxTimeContract Close = 0" |
"maxTimeContract (Pay _ _ _ _ contract) = maxTimeContract contract" |
"maxTimeContract (If _ contractTrue contractFalse) = max (maxTimeContract contractTrue) (maxTimeContract contractFalse)" |
"maxTimeContract (When Nil timeout contract) = max timeout (maxTimeContract contract)" |
"maxTimeContract (When (Cons head tail) timeout contract) = max (maxTimeCase head) (maxTimeContract (When tail timeout contract))" |
"maxTimeContract (Let _ _ contract) = maxTimeContract contract" |
"maxTimeContract (Assert _ contract) = maxTimeContract contract" |
"maxTimeCase (Case _ contract) = maxTimeContract contract"

end
