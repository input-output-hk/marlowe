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


lemma byteStringToToken_reduceslist : "byteStringToToken x = Some (a, b) \<Longrightarrow>
                                                    size b < size x"
  apply (auto simp only:tokenToByteString.simps byteStringToToken.simps split:option.splits prod.splits)
  by (meson dual_order.strict_trans getByteString_reduceslist)


lemma byteStringToChoiceId_reduceslist : "byteStringToChoiceId x = Some (a, b) \<Longrightarrow>
                                                       size b < size x"
  apply (simp only:byteStringToChoiceId.simps split:option.splits prod.splits)
   apply auto
  using byteStringToParty_reduceslist getByteString_reduceslist by fastforce



lemma byteStringToValueId_reduceslist : "byteStringToValueId x = Some (a, b) \<Longrightarrow>
                                                       size b < size x"
  apply (simp only:byteStringToValueId.simps split:option.splits prod.splits)
   apply auto
  using byteStringToParty_reduceslist getByteString_reduceslist by fastforce


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



fun boundToByteString :: "Bound \<Rightarrow> ByteString" where
"boundToByteString (l, u) = intToByteString l @ intToByteString u"

fun byteStringToBound :: "ByteString \<Rightarrow> (Bound \<times> ByteString) option" where
"byteStringToBound x =
  (case byteStringToInt x of
      None \<Rightarrow> None
    | Some (l, bs1) \<Rightarrow>(case byteStringToInt bs1 of
                      None \<Rightarrow> None
                    | Some (u, bs2) \<Rightarrow> Some ((l, u), bs2)))"


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


end