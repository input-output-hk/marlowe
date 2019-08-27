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

record State = account :: "(AccountId \<times> Money) list"
               choice :: "(ChoiceId \<times> ChosenNum) list"
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
"moneyInAccount accId accounts = findWithDefault 0 accId accounts"

fun updateMoneyInAccount :: "AccountId \<Rightarrow> Money \<Rightarrow>
                             ((AccountId \<times> Money) list) \<Rightarrow>
                             ((AccountId \<times> Money) list)" where
"updateMoneyInAccount accId money accounts =
  (if money \<le> 0
   then MList.delete accId accounts
   else MList.insert accId money accounts)"

fun addMoneyToAccount :: "AccountId \<Rightarrow> Money \<Rightarrow>
                          ((AccountId \<times> Money) list) \<Rightarrow>
                          ((AccountId \<times> Money) list)" where
"addMoneyToAccount accId money accounts =
  (let balance = moneyInAccount accId accounts in
   let newBalance = balance + money in
   if money \<le> 0
   then accounts
   else updateMoneyInAccount accId newBalance accounts)"

fun giveMoney :: "Payee \<Rightarrow> Money \<Rightarrow>
                  ((AccountId \<times> Money) list) \<Rightarrow>
                  (ReduceEffect \<times> ((AccountId \<times> Money) list))" where
"giveMoney (Party party) money accounts =
  (ReduceWithPayment (Payment party money), accounts)" |
"giveMoney (Account accId) money accounts =
  (let newAccs = addMoneyToAccount accId money accounts in
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

datatype ReduceResult = Reduced ReduceWarning ReduceEffect State Contract
                      | NotReduced
                      | AmbiguousSlotIntervalReductionError

fun reduceContractStep :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceResult" where
"reduceContractStep _ state Refund =
  (case refundOne (account state) of
     Some ((party, money), newAccount) \<Rightarrow>
       let newState = state \<lparr> account := newAccount \<rparr> in
       Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) newState Refund
   | None \<Rightarrow> NotReduced)" |
"reduceContractStep env state (Pay accId payee val nc) =
  (case evalValue env state val of money \<Rightarrow>
   let balance = moneyInAccount accId (account state) in
  (case min balance money of withdrawnMoney \<Rightarrow>
   let newBalance = balance - withdrawnMoney in
   let newAccs = updateMoneyInAccount accId newBalance (account state) in
   let noMonWarn = (if withdrawnMoney < money
                    then ReducePartialPay accId payee withdrawnMoney money
                    else ReduceNoWarning) in
   let (payEffect, finalAccs) = giveMoney payee withdrawnMoney newAccs in
   if money \<le> 0
   then Reduced (ReduceNonPositivePay accId payee money) ReduceNoPayment state nc
   else Reduced noMonWarn payEffect (state \<lparr> account := finalAccs \<rparr>) nc))" |
"reduceContractStep env state (If obs cont1 cont2) =
  (let nc = (if evalObservation env state obs
             then cont1
             else cont2) in
   Reduced ReduceNoWarning ReduceNoPayment state nc)" |
"reduceContractStep env state (When _ timeout c) =
  (let (startSlot, endSlot) = slotInterval env in
   if endSlot < timeout
   then NotReduced
   else (if startSlot \<ge> timeout
         then Reduced ReduceNoWarning ReduceNoPayment state c
         else AmbiguousSlotIntervalReductionError))" |
"reduceContractStep env state (Let valId val cont) =
  (let sv = boundValues state in
   case evalValue env state val of evVal \<Rightarrow>
   let nsv = MList.insert valId evVal sv in
   let ns = state \<lparr> boundValues := nsv \<rparr> in
   let warn = case lookup valId sv of
                Some oldVal \<Rightarrow> ReduceShadowing valId oldVal evVal
              | None \<Rightarrow> ReduceNoWarning in
   Reduced warn ReduceNoPayment ns cont)"


datatype ReduceAllResult = ReducedAll "ReduceWarning list" "ReduceEffect list"
                                      State Contract
                         | RRAmbiguousSlotIntervalError

fun evalBound :: "State \<Rightarrow> Contract \<Rightarrow> nat" where
"evalBound sta cont = length (account sta) + 2 * (size cont)"

lemma reduceContractStepReducesSize_Refund_aux :
  "refundOne (account sta) = Some ((party, money), newAccount) \<Longrightarrow>
   length (account (sta\<lparr>account := newAccount\<rparr>)) < length (account sta)"
  by (simp add: refundOneShortens)

lemma reduceContractStepReducesSize_Refund_aux2 :
  "Reduced ReduceNoWarning (ReduceWithPayment (Payment party money))
          (sta\<lparr>account := newAccount\<rparr>) Refund =
   Reduced twa tef nsta nc \<Longrightarrow>
   c = Refund \<Longrightarrow>
   refundOne (account sta) = Some ((party, money), newAccount) \<Longrightarrow>
   length (account nsta) + 2 * size nc < length (account sta)"
  apply simp
  using reduceContractStepReducesSize_Refund_aux by blast

lemma reduceContractStepReducesSize_Refund_aux3 :
  "(case a of
          ((party, money), newAccount) \<Rightarrow>
            Reduced ReduceNoWarning (ReduceWithPayment (Payment party money))
             (sta\<lparr>account := newAccount\<rparr>) Refund) =
         Reduced twa tef nsta nc \<Longrightarrow>
         c = Refund \<Longrightarrow>
         refundOne (account sta) = Some a \<Longrightarrow>
         length (account nsta) + 2 * size nc < length (account sta)"
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
  "sta\<lparr>account := b\<rparr> = nsta \<Longrightarrow>
   giveMoney dst a (MList.delete src (account sta)) = (tef, b) \<Longrightarrow>
   length (account nsta) < Suc (Suc (length (account sta)))"
  using reduceContractStepReducesSize_Pay_aux2 by auto

lemma reduceContractStepReducesSize_Pay_aux4 :
  "lookup k x = Some w \<Longrightarrow>
   giveMoney dst a (MList.insert k v x) = (tef, y) \<Longrightarrow>
   length y < Suc (Suc (length x))"
  by (metis insert_existing_length le_refl reduceContractStepReducesSize_Pay_aux)

lemma reduceContractStepReducesSize_Pay_aux5 :
"sta\<lparr>account := ba\<rparr> = nsta \<Longrightarrow>
 lookup src (account sta) = Some a \<Longrightarrow>
 giveMoney dst (evalValue env sta am) (MList.insert src (a - evalValue env sta am) (account sta)) = (tef, ba) \<Longrightarrow>
 length (account nsta) < Suc (Suc (length (account sta)))"
  using reduceContractStepReducesSize_Pay_aux4 by auto

lemma not_leq_min : "(\<not> (a \<le> x)) \<Longrightarrow> \<not> (min a (x::int) < x)"
  by simp

lemma not_leq_min2 : "(\<not> (a \<le> x)) \<Longrightarrow> (min a (x::int) = x)"
  by auto

lemma reduceContractStepReducesSize_Pay_aux6 :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst am y \<Longrightarrow>
   lookup src (account sta) = Some a \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  apply (cases "giveMoney dst 0 (MList.delete src (account sta))")
  apply (cases "a \<le> evalValue env sta am")
  apply (cases "a = evalValue env sta am")
  apply (cases "giveMoney dst (evalValue env sta am)
                          (MList.delete src (account sta))")
  apply (simp add:zeroMinIfGT)
  apply (cases "evalValue env sta am \<le> 0")
  apply simp
  apply simp
  using reduceContractStepReducesSize_Pay_aux3 apply blast
  apply (simp add:min_absorb1)
  apply (cases "giveMoney dst a (MList.delete src (account sta))")
  apply (cases "evalValue env sta am \<le> 0")
  apply simp
  apply simp
  using reduceContractStepReducesSize_Pay_aux3 apply blast
  apply (cases "evalValue env sta am \<le> 0")
  apply (cases "giveMoney dst (evalValue env sta am)
                          (MList.insert src (a - evalValue env sta am) (account sta))")
  apply (simp add:not_leq_min not_leq_min2)
  apply (cases "giveMoney dst (evalValue env sta am)
                          (MList.insert src (a - evalValue env sta am) (account sta))")
  apply (simp add:not_leq_min not_leq_min2)
  using reduceContractStepReducesSize_Pay_aux5 by blast

lemma reduceContractStepReducesSize_Pay_aux7 :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Pay src dst am y \<Longrightarrow> evalBound nsta nc < evalBound sta c"
  apply (cases "lookup src (account sta)")
  apply (cases "evalValue env sta am > 0")
  apply (cases "giveMoney dst 0 (MList.delete src (account sta))")
  apply (simp add:zeroMinIfGT)
  using reduceContractStepReducesSize_Pay_aux3 apply blast
  apply (cases "evalValue env sta am > 0")
  apply blast
  apply auto[1]
  by (metis reduceContractStepReducesSize_Pay_aux6)

lemma reduceContractStepReducesSize_When_aux :
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
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
   c = Contract.Let vId val cont \<Longrightarrow> evalBound nsta nc < evalBound sta c"
  apply (cases "lookup vId (boundValues sta)")
  by auto

lemma reduceContractStepReducesSize :
  "reduceContractStep env sta c = Reduced twa tef nsta nc \<Longrightarrow>
     (evalBound nsta nc) < (evalBound sta c)"
  apply (cases c)
  apply (cases "refundOne (account sta)")
  apply simp
  apply simp
  apply (simp add:reduceContractStepReducesSize_Refund_aux3)
  using reduceContractStepReducesSize_Pay_aux7 apply blast
  apply auto[1]
  apply (meson eq_fst_iff reduceContractStepReducesSize_When_aux)
  using reduceContractStepReducesSize_Let_aux by blast

function (sequential) reduceAllAux :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceWarning list \<Rightarrow>
                                       ReduceEffect list \<Rightarrow> ReduceAllResult" where
"reduceAllAux env sta c wa ef =
  (case reduceContractStep env sta c of
     Reduced twa tef nsta nc \<Rightarrow>
       let nwa = (if twa = ReduceNoWarning
                  then wa
                  else twa # wa) in
       let nef = (if tef = ReduceNoPayment
                  then ef
                  else tef # ef) in
       reduceAllAux env nsta nc nwa nef
   | AmbiguousSlotIntervalReductionError \<Rightarrow> RRAmbiguousSlotIntervalError
   | NotReduced \<Rightarrow> ReducedAll (rev wa) (rev ef) sta c)"
  by pat_completeness auto
termination reduceAllAux
  apply (relation "measure (\<lambda>(_, (st, (c, _))) . evalBound st c)")
  apply blast
  using reduceContractStepReducesSize by auto

fun reduceAll :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceAllResult" where
"reduceAll env sta c = reduceAllAux env sta c [] []"

datatype ApplyResult = Applied State Contract
                     | ApplyNoMatchError

fun applyCases :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Case list \<Rightarrow> ApplyResult" where
"applyCases env state (IDeposit accId1 party1 money1)
            (Cons (Case (Deposit accId2 party2 val2) nc) t) =
  (case evalValue env state val2 of money2 \<Rightarrow>
   let accounts = account state in
   let newAccs = addMoneyToAccount accId1 money1 accounts in
   let newState = state \<lparr> account := newAccs \<rparr> in
   if (accId1 = accId2 \<and> party1 = party2 \<and> money1 = money2)
   then Applied newState nc
   else applyCases env state (IDeposit accId1 party1 money1) t)" |
"applyCases env state (IChoice choId1 cho1)
            (Cons (Case (Choice choId2 bounds2) nc) t) =
  (let newState = state \<lparr> choice := MList.insert choId1 cho1 (choice state) \<rparr> in
   if (choId1 = choId2 \<and> inBounds cho1 bounds2)
   then Applied newState nc
   else applyCases env state (IChoice choId1 cho1) t)" |
"applyCases env state INotify (Cons (Case (Notify obs) nc) t) =
  (if evalObservation env state obs
   then Applied state nc
   else applyCases env state INotify t)" |
"applyCases env state (IDeposit accId1 party1 money1) (Cons h t) =
  applyCases env state (IDeposit accId1 party1 money1) t" |
"applyCases env state (IChoice choId1 cho1) (Cons h t) =
  applyCases env state (IChoice choId1 cho1) t" |
"applyCases env state INotify (Cons h t) =
  applyCases env state INotify t" |
"applyCases env state acc Nil = ApplyNoMatchError"

fun applyM :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Contract \<Rightarrow> ApplyResult" where
"applyM env state act (When cases t cont) = applyCases env state act cases" |
"applyM env state act c = ApplyNoMatchError"

datatype ApplyAllResult = AppliedAll "ReduceWarning list" "ReduceEffect list"
                                     State Contract
                        | ApplyAllNoMatchError
                        | ApplyAllAmbiguousSlotIntervalError

fun applyAllAux :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                    ReduceWarning list \<Rightarrow> ReduceEffect list \<Rightarrow>
                    ApplyAllResult" where
"applyAllAux env state c l wa ef =
   (case reduceAll env state c of
      RRAmbiguousSlotIntervalError \<Rightarrow> ApplyAllAmbiguousSlotIntervalError
    | ReducedAll twa tef tstate tc \<Rightarrow>
       (case l of
          Nil \<Rightarrow> AppliedAll (wa @ twa) (ef @ tef) tstate tc
        | Cons h t \<Rightarrow>
           (case applyM env tstate h tc of
              Applied nst nc \<Rightarrow> applyAllAux env nst nc t (wa @ twa) (ef @ tef)
            |  ApplyNoMatchError \<Rightarrow> ApplyAllNoMatchError)))"

fun applyAll :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                 ApplyAllResult" where
"applyAll env state c l = applyAllAux env state c l Nil Nil"

type_synonym TransactionSignatures = "Party list"

datatype ProcessError = TEAmbiguousSlotIntervalError
                      | TEApplyNoMatchError
                      | TEIntervalError IntervalError
                      | TEUselessTransaction

type_synonym ProcessWarning = ReduceWarning
type_synonym ProcessEffect = ReduceEffect

datatype ProcessResult = Processed "ProcessWarning list"
                                   "ProcessEffect list"
                                   State
                                   Contract
                       | ProcessError ProcessError

record Transaction = interval :: SlotInterval
                     inputs :: "Input list"

fun addSig :: "Party list \<Rightarrow> Input \<Rightarrow> Party list" where
"addSig acc (IDeposit _ p _) = SList.insert p acc" |
"addSig acc (IChoice (ChoiceId _ p) _) = SList.insert p acc" |
"addSig acc INotify = acc"

fun getSignatures :: "Input list \<Rightarrow> TransactionSignatures" where
"getSignatures l = foldl addSig SList.empty l"

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

fun process :: "Transaction \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ProcessResult" where
"process tra sta c =
  (let inps = inputs tra in
   case fixInterval (interval tra) sta of
     IntervalTrimmed env fixSta \<Rightarrow>
       (case applyAll env fixSta c inps of
          AppliedAll wa ef nsta ncon \<Rightarrow>
            if c = ncon
            then ProcessError TEUselessTransaction
            else Processed wa ef nsta ncon
        | ApplyAllNoMatchError \<Rightarrow> ProcessError TEApplyNoMatchError
        | ApplyAllAmbiguousSlotIntervalError \<Rightarrow> ProcessError TEAmbiguousSlotIntervalError)
     | IntervalError intErr \<Rightarrow> ProcessError (TEIntervalError intErr))"

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

fun getOutcomes :: "ReduceEffect list \<Rightarrow> Input list \<Rightarrow> TransactionOutcomes" where
"getOutcomes eff inp =
   foldl (\<lambda> acc (p, m) . addOutcome p m acc) emptyOutcome
         ((getPartiesFromReduceEffect eff) @ (getPartiesFromInput inp))"

end
