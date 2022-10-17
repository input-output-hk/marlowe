
(*<*)
theory SemanticsGuarantees
imports SemanticsTypes "HOL-Library.Product_Lexorder" Util.MList 
begin
(*>*)

(* BEGIN Proof of linorder for Party *)

fun less_eq_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where
"less_eq_Party (Address _) (Role _) = True" |
"less_eq_Party (Role _) (Address _) = False" |
"less_eq_Party (Address x) (Address y) =  (x \<le> y)" |
"less_eq_Party (Role x) (Role y) =  (x \<le> y)"

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
      by (metis SemanticsGuarantees.less_eq_Party.elims(3) SemanticsTypes.Party.distinct(1) SemanticsTypes.Party.inject(1) less_eq_ByteString_def less_eq_Party_def oneLessEqBS)
    subgoal for y
      by (simp add: less_eq_Party_def)
    done
  subgoal for x
    apply (cases y)
    subgoal for y
      by (simp add: less_eq_Party_def)
    subgoal for y
      by (meson SemanticsGuarantees.less_eq_Party.simps(4) less_eq_ByteString_def less_eq_Party_def oneLessEqBS)
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
    apply (meson SemanticsGuarantees.less_eq_Party.simps(3) less_eq_BS_trans less_eq_ByteString_def)
      apply simp_all
    
     apply (metis Party.exhaust less_eq_Party.simps(1) less_eq_Party.simps(2))
     apply (cases y)
      apply (cases z)
      apply simp_all
    by (metis (full_types) SemanticsGuarantees.less_eq_Party.elims(2) SemanticsGuarantees.less_eq_Party.simps(4) SemanticsTypes.Party.simps(4) less_eq_BS_trans less_eq_ByteString_def)
  
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Party)"
    by (smt (verit) SemanticsGuarantees.less_eq_Party.elims(2) SemanticsGuarantees.less_eq_Party.simps(3) SemanticsTypes.Party.inject(2) SemanticsTypes.Party.simps(4) byteStringLessEqTwiceEq less_eq_ByteString_def less_eq_Party_def)
 
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: Party)" by simp
next
  fix x y
  from linearParty have "x \<le> y \<or> y \<le> (x :: Party)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end

(* END Proof of linorder for Party *)


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
  by (smt (verit, best) SemanticsGuarantees.less_eq_Tok.elims(3) SemanticsTypes.Token.inject less_eq_Token_def oneLessEqBS)

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
    by (smt less_eq_BS_trans less_BS.simps less_eq_Tok.elims(2) less_eq_Tok.simps less_eq_Token_def oneLessEqBS)
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
    by (smt less_eq_BS_trans less_BS.simps less_eq_ChoId.simps oneLessEqBS order.trans)
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
    by (smt ValueId.simps(1) less_eq_BS_trans less_eq_ValId.elims(2) less_eq_ValId.elims(3) less_eq_ValueId_def)
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

fun valid_state :: "State \<Rightarrow> bool" where
"valid_state state = (valid_map (accounts state)
                     \<and> valid_map (choices state)
                     \<and> valid_map (boundValues state))"

(*<*)
end
(*>*)

