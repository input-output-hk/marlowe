theory Semantics
imports Main Util.MList Util.SList ListTools "HOL-Library.Product_Lexorder" SemanticsTypes SemanticsGuarantees OptBoundTimeInterval
begin

(* EVALUATION *)

fun fixInterval :: "TimeInterval \<Rightarrow> State \<Rightarrow> IntervalResult" where
"fixInterval (low, high) state =
   (let curMinTime = minTime state in
    let newLow = max low curMinTime in
    let curInterval = (newLow, high) in
    let env = \<lparr> timeInterval = curInterval \<rparr> in
    let newState = state \<lparr> minTime := newLow \<rparr> in
    (if (high < low)
     then IntervalError (InvalidInterval (low, high))
     else (if (high < curMinTime)
           then IntervalError (IntervalInPastError curMinTime (low, high))
           else IntervalTrimmed env newState)))"


fun signum :: "int \<Rightarrow> int" where
"signum x = (if x > 0 then 1 else if x = 0 then 0 else -1)"

fun quot :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "quot" 70) where
"x quot y = (if ((x < 0) = (y < 0)) then x div y else -(abs x div abs y))"

fun rem :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "rem" 70) where
"x rem y = x - (x quot y) * y"

fun quotRem :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" (infixl "quotRem" 70) where
"x quotRem y = (x quot y, x rem y)"

fun evalValue :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> int" and evalObservation :: "Environment \<Rightarrow> State \<Rightarrow> Observation \<Rightarrow> bool" where
evalValue_AvailableMoney: "evalValue env state (AvailableMoney accId token) =
    findWithDefault 0 (accId, token) (accounts state)" |
evalValue_Constant: "evalValue env state (Constant integer) = integer" |
evalValue_NegValue: "evalValue env state (NegValue val) = uminus (evalValue env state val)" |
evalValue_AddValue: "evalValue env state (AddValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs" |
evalValue_SubValue: "evalValue env state (SubValue lhs rhs) =
    evalValue env state lhs - evalValue env state rhs" |
evalValue_MulValue: "evalValue env state (MulValue lhs rhs) =
    evalValue env state lhs * evalValue env state rhs" |
evalValue_DivValue: "evalValue env state (DivValue lhs rhs) =
   (let n = evalValue env state lhs;
        d = evalValue env state rhs
    in if d = 0 then 0
       else n quot d)" |
evalValue_ChoiceValue: "evalValue env state (ChoiceValue choId) =
    findWithDefault 0 choId (choices state)" |
evalValue_TimeIntervalStart: "evalValue env state (TimeIntervalStart) = fst (timeInterval env)" |
evalValue_TimeIntervalEnd: "evalValue env state (TimeIntervalEnd) = snd (timeInterval env)" |
evalValue_UseValue: "evalValue env state (UseValue valId) =
    findWithDefault 0 valId (boundValues state)" |
evalValue_Cond: "evalValue env state (Cond cond thn els) =
    (if evalObservation env state cond then evalValue env state thn else evalValue env state els)" |
evalObservation_AndObs: "evalObservation env state (AndObs lhs rhs) =
    (evalObservation env state lhs \<and> evalObservation env state rhs)" |
evalObservation_OrObs: "evalObservation env state (OrObs lhs rhs) =
    (evalObservation env state lhs \<or> evalObservation env state rhs)" |
evalObservation_NotObs: "evalObservation env state (NotObs subObs) =
    (\<not> evalObservation env state subObs)" |
evalObservation_ChoseSomething: "evalObservation env state (ChoseSomething choId) =
    (member choId (choices state))" |
evalObservation_ValueGE: "evalObservation env state (ValueGE lhs rhs) =
    (evalValue env state lhs \<ge> evalValue env state rhs)" |
evalObservation_ValueGT: "evalObservation env state (ValueGT lhs rhs) =
    (evalValue env state lhs > evalValue env state rhs)" |
evalObservation_ValueLT: "evalObservation env state (ValueLT lhs rhs) =
    (evalValue env state lhs < evalValue env state rhs)" |
evalObservation_ValueLE: "evalObservation env state (ValueLE lhs rhs) =
    (evalValue env state lhs \<le> evalValue env state rhs)" |
evalObservation_ValueEQ: "evalObservation env state (ValueEQ lhs rhs) =
    (evalValue env state lhs = evalValue env state rhs)" |
evalObservation_TrueObs: "evalObservation env state TrueObs = True" |
evalObservation_FalseObs: "evalObservation env state FalseObs = False"

lemma evalDoubleNegValue :
  "evalValue env sta (NegValue (NegValue x)) = evalValue env sta x"
  by auto

lemma evalNegValue :
  "evalValue env sta (AddValue x (NegValue x)) = 0"
  by auto

lemma evalAddCommutative :
  "evalValue env sta (AddValue x y) = evalValue env sta (AddValue y x)"
  by auto

lemma evalAddAssoc :
  "evalValue env sta (AddValue x (AddValue y z)) = evalValue env sta (AddValue (AddValue x y) z)"
  by auto

lemma evalMulValue :
  "evalValue env sta (MulValue x (Constant 0)) = 0"
  by auto

lemma evalSubValue :
  "evalValue env sta (SubValue (AddValue x y) y) = evalValue env sta x"
  by auto

lemma evalDivByZeroIsZero :
  "evalValue env sta y = 0 \<Longrightarrow> evalValue env sta (DivValue x y) = 0"
  by simp

lemma evalDivByItSelf : "a \<noteq> 0 \<Longrightarrow> evalValue env sta x = a \<Longrightarrow> evalValue env sta y = a \<Longrightarrow> evalValue env sta (DivValue x y) = 1"
  by simp

lemma evalDivByOneIsX : "evalValue env sta y = 1 \<Longrightarrow> evalValue env sta (DivValue x y) = evalValue env sta x"
  by (simp add:Let_def)

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
  by (metis (no_types, opaque_lifting) diff_minus_eq_add mult_minus_left remMultiplySmalle_aux2)

lemma evalDivMultiplyFractByConstant :
  "evalValue env sta c \<noteq> 0 \<Longrightarrow> evalValue env sta (DivValue (MulValue c a) (MulValue c b)) = evalValue env sta (DivValue a b)"
  using quotMultiplyEquivalence by force

fun absValue :: "Value \<Rightarrow> Value" where
  "absValue x = Cond (ValueGT (Constant 0) x) (NegValue x) x"

lemma absValueMatchesAbs : "evalValue env sta x = y \<Longrightarrow> evalValue env sta (absValue x) = \<bar>y\<bar>"
  apply (cases "0 > y")
  by simp_all

lemma evalDivAbsMultiplyFractByConstant :
  "evalValue env sta c \<noteq> 0 \<Longrightarrow> evalValue env sta (DivValue (absValue (MulValue c a)) (absValue (MulValue c b))) = evalValue env sta (DivValue (absValue a) (absValue b))"
  apply simp
  by (smt (verit, best) div_minus_right div_mult_mult1_if minus_mult_right mult_neg_neg mult_pos_neg)

lemma evalDivCancelsMul :
  "evalValue env sta c \<noteq> 0 \<Longrightarrow> evalValue env sta (DivValue (MulValue a c) c) = evalValue env sta a"
  apply simp
  by (smt (verit, best) minus_mult_minus mult_minus_left nonzero_mult_div_cancel_right)

lemma evalDivCancelsMulPlusRem :
  "evalValue env sta b \<noteq> 0 \<Longrightarrow> evalValue env sta (MulValue (DivValue a b) b) = evalValue env sta a - (evalValue env sta a rem evalValue env sta b)"
  by simp

lemma evalDivCommutesWithNeg1 :
  "evalValue env sta (NegValue (DivValue a b)) = evalValue env sta (DivValue (NegValue a) b)"
  apply (simp add:Let_def)
  using div_minus_right by fastforce

lemma evalDivCommutesWithNeg2 :
  "evalValue env sta (NegValue (DivValue a b)) = evalValue env sta (DivValue a (NegValue b))"
  apply (simp add:Let_def)
  by (smt (verit) div_minus_right)

fun refundOne :: "Accounts \<Rightarrow>
                  ((Party \<times> Token \<times> int) \<times> Accounts) option" where
"refundOne (((accId, tok), money)#rest) =
   (if money > 0 then Some ((accId, tok, money), rest) else refundOne rest)" |
"refundOne [] = None"

lemma refundOneShortens : "refundOne acc = Some (c, nacc) \<Longrightarrow>
                           length nacc < length acc"
  apply (induction acc)
  apply simp
  by (metis Pair_inject length_Cons less_Suc_eq list.distinct(1)
            list.inject option.inject refundOne.elims)

datatype Payment = Payment AccountId Payee Token int

datatype ReduceEffect = ReduceNoPayment
                      | ReduceWithPayment Payment

fun moneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Accounts \<Rightarrow> int" where
"moneyInAccount accId token accountsV = findWithDefault 0 (accId, token) accountsV"

fun updateMoneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> int \<Rightarrow>
                             Accounts \<Rightarrow>
                             Accounts" where
"updateMoneyInAccount accId token money accountsV =
  (if money \<le> 0
   then MList.delete (accId, token) accountsV
   else MList.insert (accId, token) money accountsV)"

fun addMoneyToAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> int \<Rightarrow>
                          Accounts \<Rightarrow>
                          Accounts" where
"addMoneyToAccount accId token money accountsV =
  (let balance = moneyInAccount accId token accountsV in
   let newBalance = balance + money in
   if money \<le> 0
   then accountsV
   else updateMoneyInAccount accId token newBalance accountsV)"

fun giveMoney :: "AccountId \<Rightarrow> Payee \<Rightarrow> Token \<Rightarrow> int \<Rightarrow> Accounts \<Rightarrow>
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
                       | ReduceNonPositivePay AccountId Payee Token int
                       | ReducePartialPay AccountId Payee Token int int
                       | ReduceShadowing ValueId int int
                       | ReduceAssertionFailed

datatype ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                          | NotReduced
                          | AmbiguousTimeIntervalReductionError

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
  (let (startTime, endTime) = timeInterval env in
   if endTime < timeout
   then NotReduced
   else (if timeout \<le> startTime
         then Reduced ReduceNoWarning ReduceNoPayment state cont
         else AmbiguousTimeIntervalReductionError))" |
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

datatype ReduceResult = ContractQuiescent bool "ReduceWarning list" "Payment list"
                                          State Contract
                      | RRAmbiguousTimeIntervalError

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
   timeInterval env = (startTime, endTime) \<Longrightarrow>
   evalBound nsta nc < evalBound sta c"
  apply simp
  apply (cases "endTime < timeout")
  apply simp
  apply (cases "timeout \<le> startTime")
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

function (sequential) reductionLoop :: "bool \<Rightarrow> Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceWarning list \<Rightarrow>
                                        Payment list \<Rightarrow> ReduceResult" where
"reductionLoop reduced env state contract warnings payments =
  (case reduceContractStep env state contract of
     Reduced warning effect newState ncontract \<Rightarrow>
       let newWarnings = (if warning = ReduceNoWarning
                          then warnings
                          else warning # warnings) in
       let newPayments = (case effect of
                            ReduceWithPayment payment \<Rightarrow> payment # payments
                          | ReduceNoPayment \<Rightarrow> payments) in
       reductionLoop True env newState ncontract newWarnings newPayments
   | AmbiguousTimeIntervalReductionError \<Rightarrow> RRAmbiguousTimeIntervalError
   | NotReduced \<Rightarrow> ContractQuiescent reduced (rev warnings) (rev payments) state contract)"
  by pat_completeness auto
termination reductionLoop
  apply (relation "measure (\<lambda>(_, (_, (state, (contract, _)))) . evalBound state contract)")
  apply blast
  using reduceContractStepReducesSize by auto

fun reduceContractUntilQuiescent :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceResult" where
"reduceContractUntilQuiescent env state contract = reductionLoop False env state contract [] []"

datatype ApplyWarning = ApplyNoWarning
                      | ApplyNonPositiveDeposit Party AccountId Token int

datatype ApplyResult = Applied ApplyWarning State Contract
                     | ApplyNoMatchError

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = any (\<lambda> (Bound l u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

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
                            | TransactionPartialPay AccountId Payee Token int int
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

datatype ApplyAllResult = ApplyAllSuccess bool "TransactionWarning list" "Payment list"
                                     State Contract
                        | ApplyAllNoMatchError
                        | ApplyAllAmbiguousTimeIntervalError

fun applyAllLoop :: "bool \<Rightarrow> Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                    TransactionWarning list \<Rightarrow> Payment list \<Rightarrow>
                    ApplyAllResult" where
"applyAllLoop contractChanged env state contract inputs warnings payments =
   (case reduceContractUntilQuiescent env state contract of
      RRAmbiguousTimeIntervalError \<Rightarrow> ApplyAllAmbiguousTimeIntervalError
    | ContractQuiescent reduced reduceWarns pays curState cont \<Rightarrow>
       (case inputs of
          Nil \<Rightarrow> ApplyAllSuccess (contractChanged \<or> reduced) (warnings @ (convertReduceWarnings reduceWarns))
                                 (payments @ pays) curState cont
        | Cons input rest \<Rightarrow>
           (case applyInput env curState input cont of
              Applied applyWarn newState cont \<Rightarrow>
                  applyAllLoop True env newState cont rest
                               (warnings @ (convertReduceWarnings reduceWarns)
                                         @ (convertApplyWarning applyWarn))
                               (payments @ pays)
            | ApplyNoMatchError \<Rightarrow> ApplyAllNoMatchError)))"

fun applyAllInputs :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                 ApplyAllResult" where
"applyAllInputs env state contract inputs = applyAllLoop False env state contract inputs Nil Nil"

type_synonym TransactionSignatures = "Party list"

datatype TransactionError = TEAmbiguousTimeIntervalError
                          | TEApplyNoMatchError
                          | TEIntervalError IntervalError
                          | TEUselessTransaction

record TransactionOutputRecord = txOutWarnings :: "TransactionWarning list"
                                 txOutPayments :: "Payment list"
                                 txOutState :: State
                                 txOutContract :: Contract


datatype TransactionOutput = TransactionOutput TransactionOutputRecord
                           | TransactionError TransactionError

record Transaction = interval :: TimeInterval
                     inputs :: "Input list"

fun computeTransaction :: "Transaction \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> TransactionOutput" where
"computeTransaction tx state contract =
  (let inps = inputs tx in
   case fixInterval (interval tx) state of
     IntervalTrimmed env fixSta \<Rightarrow>
       (case applyAllInputs env fixSta contract inps of
          ApplyAllSuccess reduced warnings payments newState cont \<Rightarrow>
            if ((\<not> reduced) \<and> ((contract \<noteq> Close) \<or> (accounts state = [])))
            then TransactionError TEUselessTransaction
            else TransactionOutput \<lparr> txOutWarnings = warnings
                                   , txOutPayments = payments
                                   , txOutState = newState
                                   , txOutContract = cont \<rparr>
        | ApplyAllNoMatchError \<Rightarrow> TransactionError TEApplyNoMatchError
        | ApplyAllAmbiguousTimeIntervalError \<Rightarrow> TransactionError TEAmbiguousTimeIntervalError)
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

fun emptyState :: "POSIXTime \<Rightarrow> State" where
"emptyState sl = \<lparr> accounts = MList.empty
                 , choices = MList.empty
                 , boundValues = MList.empty
                 , minTime = sl \<rparr>"

fun playTrace :: "POSIXTime \<Rightarrow> Contract \<Rightarrow> Transaction list \<Rightarrow> TransactionOutput" where
"playTrace sl c t = playTraceAux \<lparr> txOutWarnings = Nil
                                 , txOutPayments = Nil
                                 , txOutState = emptyState sl
                                 , txOutContract = c \<rparr> t"

(* Extra functions *)

type_synonym TransactionOutcomes = "(Party \<times> int) list"

definition "emptyOutcome = (MList.empty :: TransactionOutcomes)"

lemma emptyOutcomeValid : "valid_map emptyOutcome"
  using MList.valid_empty emptyOutcome_def by auto

fun isEmptyOutcome :: "TransactionOutcomes \<Rightarrow> bool" where
"isEmptyOutcome trOut = all (\<lambda> (x, y) \<Rightarrow> y = 0) trOut"

fun addOutcome :: "Party \<Rightarrow> int \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"addOutcome party diffValue trOut =
   (let newValue = case MList.lookup party trOut of
                     Some value \<Rightarrow> value + diffValue
                   | None \<Rightarrow> diffValue in
    MList.insert party newValue trOut)"

fun combineOutcomes :: "TransactionOutcomes \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"combineOutcomes x y = MList.unionWith plus x y"

fun getPartiesFromReduceEffect :: "ReduceEffect list \<Rightarrow> (Party \<times> Token \<times> int) list" where
"getPartiesFromReduceEffect (Cons (ReduceWithPayment (Payment src (Party p) tok m)) t) =
   Cons (p, tok, -m) (getPartiesFromReduceEffect t)" |
"getPartiesFromReduceEffect (Cons x t) = getPartiesFromReduceEffect t" |
"getPartiesFromReduceEffect Nil = Nil"

fun getPartiesFromInput :: "Input list \<Rightarrow> (Party \<times> Token \<times> int) list" where
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


subsection "calculateNonAmbiguousInterval" 

fun gtIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"gtIfNone None _ = True" |
"gtIfNone (Some x) y = (x > y)"

fun geIfNone :: "int option \<Rightarrow> int \<Rightarrow> bool" where
"geIfNone None _ = True" |
"geIfNone (Some x) y = (x \<ge> y)"

fun subIfSome :: "int option \<Rightarrow> int \<Rightarrow> int option" where
"subIfSome None _ = None" |
"subIfSome (Some x) y = Some (x - y)"


fun calculateNonAmbiguousInterval :: "int option \<Rightarrow> POSIXTime \<Rightarrow> Contract \<Rightarrow> OptBoundTimeInterval"
where
"calculateNonAmbiguousInterval _ _ Close = (Unbounded, Unbounded)" |
"calculateNonAmbiguousInterval n t (Pay _ _ _ _ c) = calculateNonAmbiguousInterval n t c" |
"calculateNonAmbiguousInterval n t (If _ ct cf) = intersectInterval (calculateNonAmbiguousInterval n t ct)
                                                           (calculateNonAmbiguousInterval n t cf)" |
"calculateNonAmbiguousInterval n t (When Nil timeout tcont) =
  (if t < timeout
   then (Unbounded, Bounded (timeout - 1))
   else intersectInterval (Bounded timeout, Unbounded) (calculateNonAmbiguousInterval n t tcont))" |
"calculateNonAmbiguousInterval n t (When (Cons (Case _ cont ) tail) timeout tcont) =
  (if gtIfNone n 0
   then intersectInterval (calculateNonAmbiguousInterval (subIfSome n 1) t cont)
                         (calculateNonAmbiguousInterval n t (When tail timeout tcont))
   else calculateNonAmbiguousInterval n t (When tail timeout tcont))" |
"calculateNonAmbiguousInterval n t (Let _ _ c) = calculateNonAmbiguousInterval n t c" |
"calculateNonAmbiguousInterval n t (Assert _ c) = calculateNonAmbiguousInterval n t c"



section "Interpreter helpers" 
(*TODO: these are placed here for rapid prototyping between the 
        BigStep and small step semantics, once we figure how we 
        want to represent the basic types these should be refactored
        accordingly.
*)

subsection "Transaction"

(*
type_synonym ExecutionPath = "Transaction list" 
  
fun superHelper ::"Contract \<Rightarrow> ExecutionPath set" 
*)

fun fixedTransaction :: "Transaction \<Rightarrow> State \<Rightarrow> bool" where 
"fixedTransaction tx s = 
  (let curMinTime = minTime s; 
      (low, high) = interval tx 
   in 
     low \<le> high \<and> curMinTime \<le> high
   )
"

lemma fixedTransaction_implies_IntervalTrimmed :
  assumes "fixedTransaction tx s"
  shows "\<exists> env newState. fixInterval (interval tx) s = IntervalTrimmed env newState" 
proof -
  note assms
  moreover obtain low high where "interval tx = (low, high)" 
    by fastforce

  moreover obtain curMinTime where "minTime s = curMinTime" 
    by simp

  ultimately show ?thesis
    by auto metis
qed


(*
type_synonym ValidTransaction = Transaction
*)
typedef ValidTransaction = "{(tx, st). fixedTransaction tx st}"
 apply (rule_tac x = "(\<lparr> interval = (0, 0), inputs = Nil\<rparr> ,emptyState 0)" in exI)
 by simp

subsection "Accounts and payments"

fun accountsAsPayment :: "((AccountId \<times> Token) \<times> int) \<Rightarrow> Payment" where
  "accountsAsPayment ((accId, tok), val) = Payment accId (Party accId) tok val"

fun accountsAsPayments :: "Accounts \<Rightarrow> Payment set" where
 "accountsAsPayments accs = set (map accountsAsPayment accs)" 


subsection "State"

(*typedef ValidState = "{ st :: State. validAndPositive_state st }"*)

end
