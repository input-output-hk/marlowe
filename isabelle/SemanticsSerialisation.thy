theory SemanticsSerialisation
imports Main SemanticsTypes
begin


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

fun tokenToByteString :: "Token \<Rightarrow> ByteString" where
"tokenToByteString (Token cs tn) = (packByteString cs) @ (packByteString tn)"

fun byteStringToToken :: "ByteString \<Rightarrow> (Token \<times> ByteString) option" where
"byteStringToToken x =
  (case getByteString x of
      None \<Rightarrow> None
    | Some (cs, t1) \<Rightarrow> (case getByteString t1 of
                          None \<Rightarrow> None
                        | Some (tn, t2) \<Rightarrow> Some (Token cs tn, t2)))"

lemma tokenToByteStringToToken : "byteStringToToken ((tokenToByteString x) @ y) = Some (x, y)"
  apply (cases x)
  subgoal for tn cs
    apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  using addAndGetByteString by auto
  done

lemma byteStringToToken_inverseRoundtrip : "byteStringToToken x = Some (a, b) \<Longrightarrow> tokenToByteString a @ b = x"
  apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  using addAndGetByteString_inverseRoundtrip append_assoc by blast


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

end
