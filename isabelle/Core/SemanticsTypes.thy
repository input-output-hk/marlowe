theory SemanticsTypes
imports Main Util.MList Util.SList ListTools "HOL-Library.Product_Lexorder" Util.Serialisation
begin


type_synonym POSIXTime = int

type_synonym Ada = int
type_synonym CurrencySymbol = ByteString
type_synonym TokenName = ByteString

type_synonym ChoiceName = ByteString
type_synonym NumAccount = int
type_synonym Timeout = POSIXTime
type_synonym Money = Ada
type_synonym ChosenNum = int

datatype Party = Address ByteString
               | Role TokenName

type_synonym AccountId = Party

(* BEGIN Proof of linorder for Party *)
fun less_eq_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where
"less_eq_Party (Address _) (Role _) = True" |
"less_eq_Party (Role _) (Address _) = False" |
"less_eq_Party (Address x) (Address y) = less_eq_BS x y" |
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

datatype Value = AvailableMoney AccountId Token
               | Constant int
               | NegValue Value
               | AddValue Value Value
               | SubValue Value Value
               | MulValue Value Value
               | DivValue Value Value
               | ChoiceValue ChoiceId
               | TimeIntervalStart
               | TimeIntervalEnd
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

type_synonym TimeInterval = "POSIXTime \<times> POSIXTime"
type_synonym Bound = "int \<times> int"

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = any (\<lambda> (l, u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

datatype Action = Deposit AccountId Party Token Value
                | Choice ChoiceId "Bound list"
                | Notify Observation

datatype Payee = Account AccountId
               | Party Party

datatype Case = Case Action Contract
and Contract = Close
             | Pay AccountId Payee Token Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract
             | Assert Observation Contract

type_synonym Accounts = "((AccountId \<times> Token) \<times> Money) list"

record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minTime :: POSIXTime

fun valid_state :: "State \<Rightarrow> bool" where
"valid_state state = (valid_map (accounts state)
                     \<and> valid_map (choices state)
                     \<and> valid_map (boundValues state))"

record Environment = timeInterval :: TimeInterval

datatype Input = IDeposit AccountId Party Token Money
               | IChoice ChoiceId ChosenNum
               | INotify

(* Processing of time interval *)
datatype IntervalError = InvalidInterval TimeInterval
                       | IntervalInPastError POSIXTime TimeInterval

datatype IntervalResult = IntervalTrimmed Environment State
                        | IntervalError IntervalError

end
