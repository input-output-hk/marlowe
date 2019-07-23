theory Semantics
imports Main MList SList ListTools
begin

type_synonym SlotNumber = int
type_synonym SlotInterval = "SlotNumber \<times> SlotNumber"
type_synonym PubKey = int
type_synonym Party = PubKey
type_synonym NumChoice = int
type_synonym NumAccount = int
type_synonym Timeout = SlotNumber
type_synonym Money = int
type_synonym ChosenNum = int

datatype AccountId = AccountId NumAccount Party

fun less_eq :: "AccountId \<Rightarrow> AccountId \<Rightarrow> bool" where
"less_eq (AccountId a b) (AccountId c d) =
   (if a < c then True
    else (if (a > c) then False else b \<le> d))"

fun less :: "AccountId \<Rightarrow> AccountId \<Rightarrow> bool" where
  "less a b = (\<not> (less_eq b a))"

(* BEGIN Proof of linorder for AccountId *)
instantiation "AccountId" :: "ord"
begin
definition "a < b = less a b"
definition "a \<le> b = less_eq a b"
instance
proof
qed
end

lemma linearAccountId_aux :
  "(AccountId x1 x2) \<le> (AccountId y1 y2) \<or>
   (AccountId y1 y2) \<le> (AccountId x1 x2)"
  apply (cases "x1 \<le> y1")
  apply (cases "y1 \<le> y2")
  by (auto simp: less_eq_AccountId_def linear)

lemma linearAccountId : "x \<le> y \<or> y \<le> (x::AccountId)"
  by (metis AccountId.exhaust linearAccountId_aux)

instantiation "AccountId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: AccountId))"
    by (meson less.elims(2) less.elims(3) less_AccountId_def
              less_eq_AccountId_def linearAccountId)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: AccountId)" by (meson linearAccountId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: AccountId)"
    by (smt less_eq.elims(2) less_eq.simps less_eq_AccountId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: AccountId)"
    by (smt AccountId.inject less_eq.elims(2) less_eq_AccountId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: AccountId)" by simp
next
  fix x y
  from linearAccountId have "x \<le> y \<or> y \<le> (x :: AccountId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for AccountId *)

fun accountOwner :: "AccountId \<Rightarrow> Party" where
"accountOwner (AccountId _ party) = party"

datatype ChoiceId = ChoiceId NumChoice Party
datatype OracleId = OracleId PubKey
datatype ValueId = ValueId int

datatype Value = AvailableMoney AccountId
               | Constant int
               | NegValue Value
               | AddValue Value Value
               | SubValue Value Value
               | ChoiceValue ChoiceId Value
               | SlotIntervalStart
               | SlotIntervalEnd
               | UseValue ValueId

datatype Observation = AndObs Observation Observation
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

type_synonym Bound = "int \<times> int"

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = any (\<lambda> (l, u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

datatype Action = Deposit AccountId Party Value
                | Choice ChoiceId "Bound list"
                | Notify Observation

datatype Payee = Account AccountId
               | Party Party

codatatype Case = Case Action Contract
and Contract = Refund
             | Pay AccountId Payee Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract

record State = account :: "(AccountId \<times> Money) list"
               choice :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minSlot :: SlotNumber

record Environment = slotInterval :: SlotInterval

datatype Input = IDeposit AccountId Party Money
               | IChoice ChoiceId ChosenNum
               | INotify

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

end
