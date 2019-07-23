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

(* BEGIN Proof of linorder for AccountId *)
fun less_eq_AccId :: "AccountId \<Rightarrow> AccountId \<Rightarrow> bool" where
"less_eq_AccId (AccountId a b) (AccountId c d) =
   (if a < c then True
    else (if (a > c) then False else b \<le> d))"

fun less_AccId :: "AccountId \<Rightarrow> AccountId \<Rightarrow> bool" where
"less_AccId a b = (\<not> (less_eq_AccId b a))"

instantiation "AccountId" :: "ord"
begin
definition "a \<le> b = less_eq_AccId a b"
definition "a < b = less_AccId a b"
instance
proof
qed
end

lemma linearAccountId : "x \<le> y \<or> y \<le> (x::AccountId)"
  by (smt less_eq_AccId.elims(3) less_eq_AccId.simps less_eq_AccountId_def)
 
instantiation "AccountId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: AccountId))"
    by (meson less_AccId.elims(2) less_AccId.elims(3) less_AccountId_def less_eq_AccountId_def linearAccountId)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: AccountId)" by (meson linearAccountId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: AccountId)"
    by (smt less_eq_AccId.elims(2) less_eq_AccId.simps less_eq_AccountId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: AccountId)"
    by (smt less_eq_AccId.elims(2) less_eq_AccId.simps less_eq_AccountId_def)
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

(* BEGIN Proof of linorder for ChoiceId *)
fun less_eq_ChoId :: "ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> bool" where
"less_eq_ChoId (ChoiceId a b) (ChoiceId c d) =
   (if a < c then True
    else (if (a > c) then False else b \<le> d))"

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
  by (smt less_eq_ChoId.elims(3) less_eq_ChoId.simps less_eq_ChoiceId_def)
 
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
    by (smt less_eq_ChoId.elims(2) less_eq_ChoId.simps less_eq_ChoiceId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ChoiceId)"
    by (smt less_eq_ChoId.elims(2) less_eq_ChoId.simps less_eq_ChoiceId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ChoiceId)" by simp
next
  fix x y
  from linearChoiceId have "x \<le> y \<or> y \<le> (x :: ChoiceId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for ChoiceId *)

datatype OracleId = OracleId PubKey

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

datatype ValueId = ValueId int

(* BEGIN Proof of linorder for ValueId *)
fun less_eq_ValId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where
"less_eq_ValId (ValueId a) (ValueId b) = (a \<le> b)"

fun less_ValId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where
"less_ValId (ValueId a) (ValueId b) = (a < b)"

instantiation "ValueId" :: "ord"
begin
definition "a \<le> b = less_eq_ValId a b"
definition "a < b = less_ValId a b"
instance
proof
qed
end

lemma linearValueId : "x \<le> y \<or> y \<le> (x::ValueId)"
  by (smt ValueId.inject less_eq_ValId.elims(3) less_eq_ValueId_def)

instantiation "ValueId" :: linorder
begin
instance
proof
  fix x y
  have "(x < y) = (x \<le> y \<and> \<not> y \<le> (x :: ValueId))"
    by (metis ValueId.exhaust dual_order.order_iff_strict less_ValId.simps less_ValueId_def less_eq_ValId.simps less_eq_ValueId_def not_le)
  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by simp
next
  fix x
  have "x \<le> (x :: ValueId)" by (meson linearValueId)
  thus "x \<le> x" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> (z :: ValueId)"
    by (smt ValueId.inject less_eq_ValId.elims(2) less_eq_ValId.elims(3) less_eq_ValueId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
next
  fix x y z
  have "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ValueId)"
    by (smt less_eq_ValId.elims(2) less_eq_ValId.simps less_eq_ValueId_def)
  thus "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = (y :: ValueId)" by simp
next
  fix x y
  from linearValueId have "x \<le> y \<or> y \<le> (x :: ValueId)" by simp
  thus "x \<le> y \<or> y \<le> x" by simp
qed
end
(* END Proof of linorder for ValueId *)

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

datatype IntervalError = InvalidInterval SlotInterval
                       | IntervalInPastError SlotNumber SlotInterval

datatype IntervalResult = IntervalTrimmed Environment State
                        | IntervalError IntervalError

fun fixInterval :: "SlotInterval \<Rightarrow> State \<Rightarrow> IntervalResult" where
"fixInterval (l, h) st =
   (let minSlot = minSlot st in
    let nl = max l minSlot in
    let tInt = (nl, h) in
    let env = \<lparr> slotInterval = tInt \<rparr> in
    let nst = st \<lparr> minSlot := nl \<rparr> in
    (if (h < l)
     then IntervalError (InvalidInterval (l, h))
     else (if (h < minSlot)
           then IntervalError (IntervalInPastError minSlot (l, h))
           else IntervalTrimmed env nst)))"

fun evalValue :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> int" where
"evalValue env state (AvailableMoney accId) =
    findWithDefault 0 accId (account state)" |
"evalValue env state (Constant integer) = integer" |
"evalValue env state (NegValue val) = evalValue env state val" |
"evalValue env state (AddValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs" |
"evalValue env state (SubValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs" |
"evalValue env state (ChoiceValue choId defVal) =
    findWithDefault (evalValue env state defVal) choId (choice state)" |
"evalValue env state (SlotIntervalStart) = fst (slotInterval env)" |
"evalValue env state (SlotIntervalEnd) = snd (slotInterval env)" |
"evalValue env state (UseValue valId) =
    findWithDefault 0 valId (boundValues state)"

fun evalObservation :: "Environment \<Rightarrow> State \<Rightarrow> Observation \<Rightarrow> bool" where
"evalObservation env state (AndObs lhs rhs) =
    (evalObservation env state lhs \<and> evalObservation env state rhs)" |
"evalObservation env state (OrObs lhs rhs) =
    (evalObservation env state lhs \<or> evalObservation env state rhs)" |
"evalObservation env state (NotObs subObs) =
    (\<not> evalObservation env state subObs)" |
"evalObservation env state (ChoseSomething choId) =
    (member choId (choice state))" |
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

end
