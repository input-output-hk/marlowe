theory Semantics
imports Main MList SList ListTools
begin

type_synonym Slot = int

type_synonym PubKey = int

type_synonym Ada = int

type_synonym Party = PubKey
type_synonym ChoiceName = int
type_synonym NumAccount = int
type_synonym Timeout = Slot
type_synonym Money = Ada
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

datatype ChoiceId = ChoiceId ChoiceName Party

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

type_synonym SlotInterval = "Slot \<times> Slot"
type_synonym Bound = "int \<times> int"

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = any (\<lambda> (l, u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

datatype Action = Deposit AccountId Party Value
                | Choice ChoiceId "Bound list"
                | Notify Observation

datatype Payee = Account AccountId
               | Party Party

datatype Case = Case Action Contract
and Contract = Refund
             | Pay AccountId Payee Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract

record State = accounts :: "(AccountId \<times> Money) list"
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minSlot :: Slot

record Environment = slotInterval :: SlotInterval

datatype Input = IDeposit AccountId Party Money
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

fun evalValue :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> int" where
"evalValue env state (AvailableMoney accId) =
    findWithDefault 0 accId (accounts state)" |
"evalValue env state (Constant integer) = integer" |
"evalValue env state (NegValue val) = uminus (evalValue env state val)" |
"evalValue env state (AddValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs" |
"evalValue env state (SubValue lhs rhs) =
    evalValue env state lhs - evalValue env state rhs" |
"evalValue env state (ChoiceValue choId defVal) =
    findWithDefault (evalValue env state defVal) choId (choices state)" |
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

fun refundOne :: "(AccountId \<times> Money) list \<Rightarrow>
                  ((Party \<times> Money) \<times> ((AccountId \<times> Money) list)) option" where
"refundOne ((accId, money)#rest) =
   (if money > 0 then Some ((accountOwner accId, money), rest) else refundOne rest)" |
"refundOne [] = None"

lemma refundOneShortens : "refundOne acc = Some (c, nacc) \<Longrightarrow>
                           length nacc < length acc"
  apply (induction acc)
  apply simp
  by (metis Pair_inject length_Cons less_Suc_eq list.distinct(1)
            list.inject option.inject refundOne.elims)

datatype Payment = Payment Party Money

datatype ReduceEffect = ReduceNoPayment
                      | ReduceWithPayment Payment

fun moneyInAccount :: "AccountId \<Rightarrow> ((AccountId \<times> Money) list) \<Rightarrow> Money" where
"moneyInAccount accId accountsV = findWithDefault 0 accId accountsV"

fun updateMoneyInAccount :: "AccountId \<Rightarrow> Money \<Rightarrow>
                             ((AccountId \<times> Money) list) \<Rightarrow>
                             ((AccountId \<times> Money) list)" where
"updateMoneyInAccount accId money accountsV =
  (if money \<le> 0
   then MList.delete accId accountsV
   else MList.insert accId money accountsV)"

fun addMoneyToAccount :: "AccountId \<Rightarrow> Money \<Rightarrow>
                          ((AccountId \<times> Money) list) \<Rightarrow>
                          ((AccountId \<times> Money) list)" where
"addMoneyToAccount accId money accountsV =
  (let balance = moneyInAccount accId accountsV in
   let newBalance = balance + money in
   if money \<le> 0
   then accountsV
   else updateMoneyInAccount accId newBalance accountsV)"

fun giveMoney :: "Payee \<Rightarrow> Money \<Rightarrow>
                  ((AccountId \<times> Money) list) \<Rightarrow>
                  (ReduceEffect \<times> ((AccountId \<times> Money) list))" where
"giveMoney (Party party) money accountsV =
  (ReduceWithPayment (Payment party money), accountsV)" |
"giveMoney (Account accId) money accountsV =
  (let newAccs = addMoneyToAccount accId money accountsV in
    (ReduceNoPayment, newAccs))"

lemma giveMoneyIncOne : "giveMoney p m a = (e, na) \<Longrightarrow> length na \<le> length a + 1"
  apply (cases p)
  apply (cases "m \<le> 0")
  apply auto
  by (smt Suc_eq_plus1 delete_length insert_length le_Suc_eq)

(* REDUCE *)

datatype ReduceWarning = ReduceNoWarning
                       | ReduceNonPositivePay AccountId Payee Money
                       | ReducePartialPay AccountId Payee Money Money
                       | ReduceShadowing ValueId int int

datatype ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                          | NotReduced
                          | AmbiguousSlotIntervalReductionError

fun reduceContractStep :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceStepResult" where
"reduceContractStep _ state Refund =
  (case refundOne (accounts state) of
     Some ((party, money), newAccount) \<Rightarrow>
       let newState = state \<lparr> accounts := newAccount \<rparr> in
       Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) newState Refund
   | None \<Rightarrow> NotReduced)" |
"reduceContractStep env state (Pay accId payee val cont) =
  (let moneyToPay = evalValue env state val in
   if moneyToPay \<le> 0
   then Reduced (ReduceNonPositivePay accId payee moneyToPay) ReduceNoPayment state cont
   else (let balance = moneyInAccount accId (accounts state) in
        (let paidMoney = min balance moneyToPay in
         let newBalance = balance - paidMoney in
         let newAccs = updateMoneyInAccount accId newBalance (accounts state) in
         let warning = (if paidMoney < moneyToPay
                        then ReducePartialPay accId payee paidMoney moneyToPay
                        else ReduceNoWarning) in
         let (payment, finalAccs) = giveMoney payee paidMoney newAccs in
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
   Reduced warn ReduceNoPayment newState cont)"

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
  "Reduced ReduceNoWarning (ReduceWithPayment (Payment party money))
          (sta\<lparr>accounts := newAccount\<rparr>) Refund =
   Reduced twa tef nsta nc \<Longrightarrow>
   c = Refund \<Longrightarrow>
   refundOne (accounts sta) = Some ((party, money), newAccount) \<Longrightarrow>
   length (accounts nsta) + 2 * size nc < length (accounts sta)"
  apply simp
  using reduceContractStepReducesSize_Refund_aux by blast

lemma reduceContractStepReducesSize_Refund :
  "(case a of
          ((party, money), newAccount) \<Rightarrow>
            Reduced ReduceNoWarning (ReduceWithPayment (Payment party money))
             (sta\<lparr>accounts := newAccount\<rparr>) Refund) =
         Reduced twa tef nsta nc \<Longrightarrow>
         c = Refund \<Longrightarrow>
         refundOne (accounts sta) = Some a \<Longrightarrow>
         length (accounts nsta) + 2 * size nc < length (accounts sta)"
  apply (cases a)
  apply simp
  using reduceContractStepReducesSize_Refund_aux2 by fastforce

lemma zeroMinIfGT : "x > 0 \<Longrightarrow> min 0 x = (0 :: int)"
  by simp

lemma reduceContractStepReducesSize_Pay_aux :
  "length z \<le> length x \<Longrightarrow>
   giveMoney x22 a z = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  using giveMoneyIncOne by fastforce

lemma reduceContractStepReducesSize_Pay_aux2 :
  "giveMoney dst a (MList.delete src x)  = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  using delete_length reduceContractStepReducesSize_Pay_aux by blast

lemma reduceContractStepReducesSize_Pay_aux3 :
  "sta\<lparr>accounts := b\<rparr> = nsta \<Longrightarrow>
   giveMoney dst a (MList.delete src (accounts sta)) = (tef, b) \<Longrightarrow>
   length (accounts nsta) < Suc (Suc (length (accounts sta)))"
  using reduceContractStepReducesSize_Pay_aux2 by auto

lemma reduceContractStepReducesSize_Pay_aux4 :
  "lookup k x = Some w \<Longrightarrow>
   giveMoney dst a (MList.insert k v x) = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  by (metis insert_existing_length le_refl reduceContractStepReducesSize_Pay_aux)

lemma reduceContractStepReducesSize_Pay_aux5 :
"sta\<lparr>accounts := ba\<rparr> = nsta \<Longrightarrow>
 lookup src (accounts sta) = Some a \<Longrightarrow>
 giveMoney dst (evalValue env sta am) (MList.insert src (a - evalValue env sta am) (accounts sta)) = (tef, ba) \<Longrightarrow>
 length (accounts nsta) < Suc (Suc (length (accounts sta)))"
  using reduceContractStepReducesSize_Pay_aux4 by auto

lemma reduceContractStepReducesSize_Pay_aux6 :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst am y \<Longrightarrow>
   evalValue env sta am > 0 \<Longrightarrow>
   lookup src (accounts sta) = Some a \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  apply (cases "a < evalValue env sta am")
  apply (simp add:min_absorb1)
  apply (cases "giveMoney dst a (MList.delete src (accounts sta))")
  using reduceContractStepReducesSize_Pay_aux3 apply fastforce
  apply (cases "a = evalValue env sta am")
  apply (cases "giveMoney dst (evalValue env sta am) (MList.delete src (accounts sta))")
  apply (simp add:min_absorb2)
  using reduceContractStepReducesSize_Pay_aux3 apply blast
  apply (cases "giveMoney dst (evalValue env sta am) (MList.insert src (a - evalValue env sta am) (accounts sta))")
  apply (simp add:min_absorb2)
  using reduceContractStepReducesSize_Pay_aux5 by blast

lemma reduceContractStepReducesSize_Pay :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst am y \<Longrightarrow> evalBound nsta nc < evalBound sta c"
  apply (cases "evalValue env sta am \<le> 0")
  apply auto[1]
  apply (cases "lookup src (accounts sta)")
  apply (cases "evalValue env sta am > 0")
  apply (cases "giveMoney dst 0 (MList.delete src (accounts sta))")
  apply (simp add:zeroMinIfGT)
  using reduceContractStepReducesSize_Pay_aux3 apply blast
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
  apply (simp add:reduceContractStepReducesSize_Refund)
  using reduceContractStepReducesSize_Pay apply blast
  apply auto[1]
  apply (meson eq_fst_iff reduceContractStepReducesSize_When)
  using reduceContractStepReducesSize_Let by blast

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
                      | ApplyNonPositiveDeposit Party AccountId int

datatype ApplyResult = Applied ApplyWarning State Contract
                     | ApplyNoMatchError

fun applyCases :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Case list \<Rightarrow> ApplyResult" where
"applyCases env state (IDeposit accId1 party1 money)
            (Cons (Case (Deposit accId2 party2 val) cont) rest) =
  (let amount = evalValue env state val in
   let warning = if amount > 0
                 then ApplyNoWarning
                 else ApplyNonPositiveDeposit party1 accId2 amount in
   let newState = state \<lparr> accounts := addMoneyToAccount accId1 money (accounts state) \<rparr> in
   if (accId1 = accId2 \<and> party1 = party2 \<and> money = amount)
   then Applied warning newState cont
   else applyCases env state (IDeposit accId1 party1 money) rest)" |
"applyCases env state (IChoice choId1 choice)
            (Cons (Case (Choice choId2 bounds) cont) rest) =
  (let newState = state \<lparr> choices := MList.insert choId1 choice (choices state) \<rparr> in
   if (choId1 = choId2 \<and> inBounds choice bounds)
   then Applied ApplyNoWarning newState cont
   else applyCases env state (IChoice choId1 choice) rest)" |
"applyCases env state INotify (Cons (Case (Notify obs) cont) rest) =
  (if evalObservation env state obs
   then Applied ApplyNoWarning state cont
   else applyCases env state INotify rest)" |
"applyCases env state (IDeposit accId1 party1 money) (Cons _ rest) =
  applyCases env state (IDeposit accId1 party1 money) rest" |
"applyCases env state (IChoice choId1 choice) (Cons _ rest) =
  applyCases env state (IChoice choId1 choice) rest" |
"applyCases env state INotify (Cons _ rest) =
  applyCases env state INotify rest" |
"applyCases env state acc Nil = ApplyNoMatchError"

fun applyInput :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Contract \<Rightarrow> ApplyResult" where
"applyInput env state input (When cases t cont) = applyCases env state input cases" |
"applyInput env state input c = ApplyNoMatchError"

datatype TransactionWarning = TransactionNonPositiveDeposit Party AccountId int
                            | TransactionNonPositivePay AccountId Payee int
                            | TransactionPartialPay AccountId Payee Money Money
                            | TransactionShadowing ValueId int int

fun convertReduceWarnings :: "ReduceWarning list \<Rightarrow> TransactionWarning list" where
"convertReduceWarnings Nil = Nil" |
"convertReduceWarnings (Cons ReduceNoWarning rest) =
   convertReduceWarnings rest" |
"convertReduceWarnings (Cons (ReduceNonPositivePay accId payee amount) rest) =
   Cons (TransactionNonPositivePay accId payee amount)
        (convertReduceWarnings rest)" |
"convertReduceWarnings (Cons (ReducePartialPay accId payee paid expected) rest) =
   Cons (TransactionPartialPay accId payee paid expected)
        (convertReduceWarnings rest)" |
"convertReduceWarnings (Cons (ReduceShadowing valId oldVal newVal) rest) =
   Cons (TransactionShadowing valId oldVal newVal)
        (convertReduceWarnings rest)"

fun convertApplyWarning :: "ApplyWarning \<Rightarrow> TransactionWarning list" where
"convertApplyWarning ApplyNoWarning = Nil" |
"convertApplyWarning (ApplyNonPositiveDeposit party accId amount) =
   Cons (TransactionNonPositiveDeposit party accId amount) Nil"

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
            if contract = cont
            then TransactionError TEUselessTransaction
            else TransactionOutput \<lparr> txOutWarnings = warnings
                                   , txOutPayments = payments
                                   , txOutState = newState
                                   , txOutContract = cont \<rparr>
        | ApplyAllNoMatchError \<Rightarrow> TransactionError TEApplyNoMatchError
        | ApplyAllAmbiguousSlotIntervalError \<Rightarrow> TransactionError TEAmbiguousSlotIntervalError)
     | IntervalError error \<Rightarrow> TransactionError (TEIntervalError error))"

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

fun getPartiesFromReduceEffect :: "ReduceEffect list \<Rightarrow> (Party \<times> Money) list" where
"getPartiesFromReduceEffect (Cons (ReduceWithPayment (Payment p m)) t) =
   Cons (p, -m) (getPartiesFromReduceEffect t)" |
"getPartiesFromReduceEffect (Cons x t) = getPartiesFromReduceEffect t" |
"getPartiesFromReduceEffect Nil = Nil"

fun getPartiesFromInput :: "Input list \<Rightarrow> (Party \<times> Money) list" where
"getPartiesFromInput (Cons (IDeposit _ p m) t) =
   Cons (p, m) (getPartiesFromInput t)" |
"getPartiesFromInput (Cons x t) = getPartiesFromInput t" |
"getPartiesFromInput Nil = Nil"

fun getOutcomes :: "ReduceEffect list \<Rightarrow> Input list \<Rightarrow> TransactionOutcomes" where
"getOutcomes eff inp =
   foldl (\<lambda> acc (p, m) . addOutcome p m acc) emptyOutcome
         ((getPartiesFromReduceEffect eff) @ (getPartiesFromInput inp))"

fun addSig :: "Party list \<Rightarrow> Input \<Rightarrow> Party list" where
"addSig acc (IDeposit _ p _) = SList.insert p acc" |
"addSig acc (IChoice (ChoiceId _ p) _) = SList.insert p acc" |
"addSig acc INotify = acc"

fun getSignatures :: "Input list \<Rightarrow> TransactionSignatures" where
"getSignatures l = foldl addSig SList.empty l"

fun isQuiescent :: "Contract \<Rightarrow> bool" where
"isQuiescent Refund = True" |
"isQuiescent (When _ _ _) = True" |
"isQuiescent _ = False"

lemma reduceContractStepPayIsQuiescent :
      "(let moneyToPay = evalValue env sta x23
        in if moneyToPay \<le> 0 then Reduced (ReduceNonPositivePay x21 x22 moneyToPay) ReduceNoPayment sta x24
           else let balance = moneyInAccount x21 (accounts sta); paidMoney = min balance moneyToPay; newBalance = balance - paidMoney;
                    newAccs = updateMoneyInAccount x21 newBalance (accounts sta);
                    warning = if paidMoney < moneyToPay then ReducePartialPay x21 x22 paidMoney moneyToPay else ReduceNoWarning;
                    (payment, finalAccs) = giveMoney x22 paidMoney newAccs
                in Reduced warning payment (sta\<lparr>accounts := finalAccs\<rparr>) x24) =
       NotReduced \<Longrightarrow>
       cont = Pay x21 x22 x23 x24 \<Longrightarrow> False"
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 (accounts sta)) (evalValue env sta x23) < (evalValue env sta x23)")
  apply (cases "lookup x21 (accounts sta)")
  apply simp
  apply (metis (mono_tags, lifting) ReduceStepResult.distinct(1) case_prod_unfold)
  apply (cases "evalValue env sta x23 \<le> 0")
  apply simp
  apply (cases "min (moneyInAccount x21 (accounts sta)) (evalValue env sta x23) < evalValue env sta x23")
  apply simp
  apply (metis (no_types, lifting) ReduceStepResult.distinct(1) case_prod_unfold)
  apply simp
  by (smt ReduceStepResult.distinct(1) case_prod_unfold)

lemma reduceContractStepIsQuiescent : "reduceContractStep env sta cont = NotReduced \<Longrightarrow> isQuiescent cont"
  apply (cases cont)
  apply auto[1]
  using reduceContractStepPayIsQuiescent apply fastforce
  apply simp
  using isQuiescent.simps(2) apply blast
  by (metis ReduceStepResult.distinct(1) reduceContractStep.simps(5))

lemma reductionLoopIsQuiescent_aux : "
       (\<And>x11 x12 x13 x14 x xa.
           reduceContractStep env state contract = Reduced x11 x12 x13 x14 \<Longrightarrow>
           x = (if x11 = ReduceNoWarning then warnings else x11 # warnings) \<Longrightarrow>
           xa = (case x12 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) \<Longrightarrow>
           reductionLoop env x13 x14 x xa = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon) \<Longrightarrow>
       reductionLoop env state contract warnings payments = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (cases "reduceContractStep env state contract")
  apply simp
  apply metis
  by (simp_all add: reduceContractStepIsQuiescent)

lemma reductionLoopIsQuiescent : "reductionLoop env sta c wa ef = ContractQuiescent nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (induction env sta c wa ef rule:reductionLoop.induct)
  using reductionLoopIsQuiescent_aux by blast

theorem reduceContractUntilQuiecentIsQuiescent : "reduceContractUntilQuiescent env sta c = ContractQuiescent wa ef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (simp only: reduceContractUntilQuiescent.simps)
  by (simp add: reductionLoopIsQuiescent)

lemma applyAllInputsLoopIsQuiescent_base : "applyAllLoop env fixSta cont [] wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  apply (simp del:reduceContractUntilQuiescent.simps)
  using reduceContractUntilQuiecentIsQuiescent apply blast
  by simp

lemma applyAllInputsLoopIsQuiescent_loop : "(\<And>env fixSta cont wa ef. applyAllLoop env fixSta cont inps wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon) \<Longrightarrow>
       applyAllLoop env fixSta cont (a # inps) wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (cases "reduceContractUntilQuiescent env fixSta cont")
  apply (unfold applyAllLoop.simps [of "env" "fixSta"])
  apply (simp del:applyAllLoop.simps reduceContractUntilQuiescent.simps)
  apply (metis (no_types, lifting) ApplyAllResult.distinct(1) ApplyResult.exhaust ApplyResult.simps(4) ApplyResult.simps(5))
  by simp

lemma applyAllInputsLoopIsQuiescent : "applyAllLoop env fixSta cont inps wa ef = ApplyAllSuccess nwa nef nsta ncon \<Longrightarrow> isQuiescent ncon"
  apply (induction inps arbitrary:env fixSta cont wa ef)
  apply (simp add: applyAllInputsLoopIsQuiescent_base)
  using applyAllInputsLoopIsQuiescent_loop by blast

lemma applyAllInputsIsQuiescent : "applyAllInputs env fixSta cont inps = ApplyAllSuccess warnings payments newState newCont \<Longrightarrow> isQuiescent newCont"
  by (simp add: applyAllInputsLoopIsQuiescent)

lemma computeTransactionIsQuiescent_aux : "computeTransaction (Transaction \<lparr>interval = interva, inputs = inps\<rparr>) sta cont
                                            = TransactionOutput \<lparr> txOutWarnings = nwa,
                                                                  txOutPayments = nef,
                                                                  txOutState = nsta,
                                                                  txOutContract = ncont\<rparr> \<Longrightarrow>
       fixInterval (interval (Transaction \<lparr>interval = interva, inputs = inps\<rparr>)) sta = IntervalTrimmed x11 x12
       \<Longrightarrow> isQuiescent ncont"
  by (smt ApplyAllResult.exhaust ApplyAllResult.simps(10) ApplyAllResult.simps(8) ApplyAllResult.simps(9) IntervalResult.simps(5) TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.select_convs(4) applyAllInputsIsQuiescent computeTransaction.simps)

theorem computeTransactionIsQuiescent : "computeTransaction traIn sta cont = TransactionOutput traOut \<Longrightarrow> isQuiescent (txOutContract traOut)"
  apply (cases "traIn")
  apply (cases "traOut")
  by (smt IntervalResult.exhaust IntervalResult.simps(6) Transaction.update_convs(3) TransactionOutput.distinct(1) TransactionOutputRecord.select_convs(4) computeTransaction.elims computeTransactionIsQuiescent_aux old.unit.exhaust)

end
