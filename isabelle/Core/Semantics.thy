theory Semantics
imports Main Util.MList Util.SList ListTools "HOL-Library.Product_Lexorder" Util.Serialisation SemanticsTypes
begin

(* EVALUATION *)

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
"evalValue env state (DivValue lhs rhs) = 
   (let n = evalValue env state lhs in 
    if n = 0 then 0 
    else let d = evalValue env state rhs in 
      if d = 0 then 0 else 
        let (q, r) = n quotRem d in 
        let ar = abs r * 2 in
        let ad = abs d in 
        if ar < ad then q
        else if ar > ad then q + signum n * signum d
        else let qIsEven = q rem 2 = 0 in 
          if qIsEven then q else q + signum n * signum d)" |
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
  by (metis (no_types, opaque_lifting) diff_minus_eq_add mult_minus_left remMultiplySmalle_aux2)

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

datatype ReduceResult = ContractQuiescent bool "ReduceWarning list" "Payment list"
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
   | AmbiguousSlotIntervalReductionError \<Rightarrow> RRAmbiguousSlotIntervalError
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

datatype ApplyAllResult = ApplyAllSuccess bool "TransactionWarning list" "Payment list"
                                     State Contract
                        | ApplyAllNoMatchError
                        | ApplyAllAmbiguousSlotIntervalError

fun applyAllLoop :: "bool \<Rightarrow> Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Input list \<Rightarrow>
                    TransactionWarning list \<Rightarrow> Payment list \<Rightarrow>
                    ApplyAllResult" where
"applyAllLoop contractChanged env state contract inputs warnings payments =
   (case reduceContractUntilQuiescent env state contract of
      RRAmbiguousSlotIntervalError \<Rightarrow> ApplyAllAmbiguousSlotIntervalError
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
          ApplyAllSuccess reduced warnings payments newState cont \<Rightarrow>
            if ((\<not> reduced) \<and> ((contract \<noteq> Close) \<or> (accounts state = [])))
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
