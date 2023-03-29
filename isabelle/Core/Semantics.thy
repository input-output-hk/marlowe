(*<*)
theory Semantics
  imports SemanticsTypes
          SemanticsGuarantees
          OptBoundTimeInterval
          "HOL-Library.Product_Lexorder"
          Util.MList
          Util.SList
          Util.Division
begin
(*>*)

section \<open>Interpreter\<close>

text \<open>

This section defines the semantics of the Marlowe language using an interpreter. The functions and
 datatypes that make up the interpreter are designed with respect to Isabelle's characteristics.
 For example, mutually recursive functions need to be defined together, and any definition can only
use what is defined before.

An implementation of Marlowe can use this section as reference. However, it is not necessary to use
the exact same inner types and functions. The essential requirements are to model the types defined in
section \secref{sec:core-types} and ensure that calling \<^emph>\<open>computeTransaction\<close> \secref{sec:computeTransaction}
produces the same results as specified in this document. The Marlowe repository includes a tool called
 \<^emph>\<open>spec-test\<close> which is used to verify compliance of an implementation with the
specification.
\<close>

subsection \<open>Account operations\<close>

text \<open>In this section we present some helper functions to query and modify the assets
present in the internal accounts of a contract\<close>

text \<open>The function \<^emph>\<open>moneyInAccount\<close> returns the number of \<^emph>\<open>token\<close> a particular \<^emph>\<open>AccountId\<close> has in
their account.\<close>

fun moneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> Accounts \<Rightarrow> int"
  where
  "moneyInAccount accId token accountsV =
    findWithDefault 0 (accId, token) accountsV"

text \<open>The function \<^emph>\<open>updateMoneyInAccount\<close> sets the amount of \<^emph>\<open>token\<close> a particular \<^emph>\<open>AccountId\<close>
has in their account, overriding any previous value. Marlowe requires all accounts to have positive
balances, so if the function is called with a negative value or zero the entry is removed
from the accounts.\<close>

fun updateMoneyInAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> int \<Rightarrow> Accounts \<Rightarrow> Accounts"
where
  "updateMoneyInAccount accId token money accountsV =
    (if money \<le> 0
     then MList.delete (accId, token) accountsV
     else MList.insert (accId, token) money accountsV)"

text \<open>The function \<^emph>\<open>addMoneyToAccount\<close> increases the amount of token a particular \<^emph>\<open>AccountId\<close> has
in their account. To ensure that the value always increases we check that \<^term>\<open>money > 0\<close>. \<close>
fun addMoneyToAccount :: "AccountId \<Rightarrow> Token \<Rightarrow> int \<Rightarrow> Accounts \<Rightarrow> Accounts"
where
  "addMoneyToAccount accId token money accts =
    (let balance = moneyInAccount accId token accts ;
         newBalance = balance + money
     in
         if money \<le> 0
         then accts
         else updateMoneyInAccount accId token newBalance accts)"

subsection \<open>Eval value and observation\label{sec:evalValueObservation}\<close>

text \<open>The functions \<^emph>\<open>evalValue\<close> and \<^emph>\<open>evalObservation\<close> are defined in a mutually
recursive manner. They operate by taking a term, as described in section \secref{sec:values-and-observations},
 and evaluating it with a specific \<^emph>\<open>State\<close> and \<^emph>\<open>Environment\<close>.\<close>
fun evalValue :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> int"
and evalObservation :: "Environment \<Rightarrow> State \<Rightarrow> Observation \<Rightarrow> bool"
where
  \<comment> \<open>===Eval Value===\<close>
  \<comment> \<open>For AvailableMoney, ChoiceValue and UseValue we check the state\<close>
  \<comment> \<open>for a value and if its not found we default to zero\<close>
  "evalValue env state (AvailableMoney accId token) =
    moneyInAccount accId token (accounts state)"
| "evalValue env state (ChoiceValue choId) =
    findWithDefault 0 choId (choices state)"
| "evalValue env state (UseValue valId) =
    findWithDefault 0 valId (boundValues state)"
  \<comment> \<open>Arithmetic operations\<close>
| "evalValue env state (Constant c) = c"
| "evalValue env state (NegValue val) =
    - evalValue env state val"
| "evalValue env state (AddValue lhs rhs) =
    evalValue env state lhs + evalValue env state rhs"
| "evalValue env state (SubValue lhs rhs) =
    evalValue env state lhs - evalValue env state rhs"
| "evalValue env state (MulValue lhs rhs) =
    evalValue env state lhs * evalValue env state rhs"
| "evalValue env state (DivValue lhs rhs) =
    \<comment> \<open>Division is a special case because we only evaluate to integers. We use\<close>
    \<comment> \<open>Partial quotients with rounding towards zero. If the denominator is zero we\<close>
    \<comment> \<open>return zero (some languages use NaN for this case)\<close>
   (let n = evalValue env state lhs;
        d = evalValue env state rhs
    in if d = 0 then 0
       else n quot d)"
  \<comment> \<open>Eval value from Environment\<close>
| "evalValue env state TimeIntervalStart = fst (timeInterval env)"
| "evalValue env state TimeIntervalEnd = snd (timeInterval env)"
  \<comment> \<open>Conditional/Ternary operator\<close>
| "evalValue env state (Cond cond thn els) =
    (if evalObservation env state cond
     then evalValue env state thn
     else evalValue env state els)"

  \<comment> \<open>===Eval Observation===\<close>
  \<comment> \<open>Constants\<close>
| "evalObservation env state TrueObs = True"
| "evalObservation env state FalseObs = False"
  \<comment> \<open>Logical operators\<close>
| "evalObservation env state (NotObs subObs) =
    (\<not> evalObservation env state subObs)"
| "evalObservation env state (AndObs lhs rhs) =
    (evalObservation env state lhs \<and> evalObservation env state rhs)"
| "evalObservation env state (OrObs lhs rhs) =
    (evalObservation env state lhs \<or> evalObservation env state rhs)"
  \<comment> \<open>See if a choice was made\<close>
| "evalObservation env state (ChoseSomething choId) =
    (member choId (choices state))"
  \<comment> \<open>Value comparisons\<close>
| "evalObservation env state (ValueGE lhs rhs) =
    (evalValue env state lhs \<ge> evalValue env state rhs)"
| "evalObservation env state (ValueGT lhs rhs) =
    (evalValue env state lhs > evalValue env state rhs)"
| "evalObservation env state (ValueLT lhs rhs) =
    (evalValue env state lhs < evalValue env state rhs)"
| "evalObservation env state (ValueLE lhs rhs) =
    (evalValue env state lhs \<le> evalValue env state rhs)"
| "evalObservation env state (ValueEQ lhs rhs) =
    (evalValue env state lhs = evalValue env state rhs)"

text \<open>Different languages can behave differently regarding rounding with partial
division. To follow the specification, it is important for implementers to respect
the following properties.\<close>

text \<open>Dividing by zero results in zero\<close>
lemma eval_DivValue_by_zero_is_zero :
  assumes "evalValue env sta d = 0"
    shows "evalValue env sta (DivValue n d) = 0"
(*<*)
  using assms by simp
(*>*)

text \<open>Dividing by itself results in one\<close>
lemma eval_DivValue_by_itself :
  assumes "evalValue env sta n = a"
      and "evalValue env sta d = a"
      and "a \<noteq> 0"
    shows "evalValue env sta (DivValue n d) = 1"
(*<*)
  using assms  by simp
(*>*)

text \<open>Dividing by one results in the numerator\<close>
lemma eval_DivValue_by_one :
  assumes "evalValue env sta d = 1"
    shows "evalValue env sta (DivValue n d) = evalValue env sta n"
(*<*)
  using assms by (simp add:Let_def)
(*>*)

text \<open>If we multiply the numerator and denominator by the same constant, we can
simplify it.\<close>
lemma eval_DivValue_simp_MulByConstant :
  assumes "evalValue env sta c \<noteq> 0"
    shows "evalValue env sta (DivValue (MulValue c a) (MulValue c b))
           = evalValue env sta (DivValue a b)"
(*<*)
  using quotMultiplyEquivalence assms by force
(*>*)


text \<open>If the denomintor is bigger than the numerator in absolute values, the result is zero.\<close>
lemma eval_DivValue_rounds_to_zero :
  assumes "\<bar>(evalValue env sta n)\<bar> < \<bar>(evalValue env sta d)\<bar>"
  shows "evalValue env sta (DivValue n d) = 0"
(*<*)
  using assms
  by (auto simp add: Let_def)
(*>*)


subsection \<open>Reduce contract step\label{sec:reduceContractStep}\<close>

text \<open>In section \secref{sec:Quiescent}, we defined a quiescent contract as one that has either completed its execution or is
 waiting for external input. The function \<^emph>\<open>reduceContractStep\<close> makes a single reduction toward that state.
It is later recursively called by the \<^emph>\<open>reduceContractUntilQuiescent\<close> function until the contract can no longer
 be reduced any further.\<close>

text \<open>The following datatypes are auxiliary to define the result of the \<^emph>\<open>reduceContractStep\<close> function.\<close>

text \<open>The \<^emph>\<open>ReduceEffect\<close> type represents whether a payment should be made as a
consequence of reducing the contract.\<close>
datatype ReduceEffect
  = ReduceNoPayment
  | ReduceWithPayment Payment

text \<open>The \<^emph>\<open>ReduceWarning\<close> type denotes results that may not necessarily be an
error, but should be taken into account.\<close>
datatype ReduceWarning
  = ReduceNoWarning
  \<comment> \<open>If a Pay contract tries to pay a value lower or equal than zero, no payment is\<close>
  \<comment> \<open> made and this warning is raised\<close>
  | ReduceNonPositivePay AccountId Payee Token int
  \<comment> \<open>If a Pay contract tries to pay more tokens than the available in the account,\<close>
  \<comment> \<open>the available tokens are paid and this warning is raised\<close>
  | ReducePartialPay AccountId Payee Token int int
  \<comment> \<open>If a Let contract uses a value that was already bound, the value is overwritten\<close>
  \<comment> \<open>and this warning is raised\<close>
  | ReduceShadowing ValueId int int
  \<comment> \<open>If the observation of an Assert evaluates to false this warning is raised\<close>
  | ReduceAssertionFailed

text \<open>When calling reduceContractStep, there are three potential outcomes. If the
contract is quiescent, the function returns \<^emph>\<open>NotReduced\<close>. If the contract has been
successfully reduced, the function returns an optional warning, an optional payment,
the updated state, and the new continuation. However, if the contract is a \<^emph>\<open>When\<close>
statement with an ambiguous timeout for the given Environment, the function will
return an \<^emph>\<open>AmbiguousTimeIntervalReductionError\<close>\<close>

text \<open>A TimeInterval expressed as the tuple \<^term>\<open>(startTime \<times> endTime)\<close> can be
ambiguous w.r.t. a \<^term>\<open>When\<close>'s timeout iff \<^emph>\<open>startTime\<close> < \<^emph>\<open>timeout\<close> \le \<^emph>\<open>endTime\<close>
\<close>
datatype ReduceStepResult
  = Reduced ReduceWarning ReduceEffect State Contract
  | NotReduced
  | AmbiguousTimeIntervalReductionError

text \<open>
The auxiliary function \<^emph>\<open>refundOne\<close> assists in the reduction of a Close contract.
Its purpose is to remove any non-positive values from the account and return the
first positive value as well as the remaining accounts.\<close>

fun refundOne :: "Accounts \<Rightarrow> ((Party \<times> Token \<times> int) \<times> Accounts) option"
where
  "refundOne (((accId, tok), money) # rest) =
   (if money > 0
    then Some ((accId, tok, money), rest)
    else refundOne rest
   )"
| "refundOne [] = None"


text \<open>The auxiliary function \<^emph>\<open>giveMoney\<close> assists in the reduction of a Pay contract.\<close>

\<comment> \<open>TODO: this function should probably be inlined or renamed as the name is missleading\<close>
fun giveMoney ::
  "AccountId
  \<Rightarrow> Payee
  \<Rightarrow> Token
  \<Rightarrow> int
  \<Rightarrow> Accounts
  \<Rightarrow> (ReduceEffect \<times> Accounts)"
where
"giveMoney accountId payee token money accts =
  (let newAccounts = case payee of
                        Party _ \<Rightarrow> accts
                      | Account accId \<Rightarrow> addMoneyToAccount accId token money accts
   in (ReduceWithPayment (Payment accountId payee token money)
      , newAccounts)
  )"



text \<open>The function reduceContractStep makes a single reduction of the contract\<close>
fun reduceContractStep :: "Environment \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> ReduceStepResult"
where
  \<comment> \<open>A Close contract can only be reduced if there are assets left in the accounts\<close>
  "reduceContractStep _ state Close =
    (case refundOne (accounts state) of
       Some ((party, token, money), newAccounts) \<Rightarrow>
         let newState = state \<lparr> accounts := newAccounts \<rparr>
         in
          Reduced
            ReduceNoWarning
            (ReduceWithPayment (Payment party (Party party) token money))
            newState
            Close
     | None \<Rightarrow> NotReduced)"
  \<comment> \<open>A Pay contract is always reduced\<close>
| "reduceContractStep env state (Pay accId payee token val cont) =
    (let amountToPay = evalValue env state val in
     if amountToPay \<le> 0
     then let warning = ReduceNonPositivePay accId payee token amountToPay
          in Reduced warning ReduceNoPayment state cont
     else let balance = moneyInAccount accId token (accounts state);
              paidAmount = min balance amountToPay;
              newBalance = balance - paidAmount;
              newAccs =
                updateMoneyInAccount accId token newBalance (accounts state);
              warning =
                if paidAmount < amountToPay
                then ReducePartialPay accId payee token paidAmount amountToPay
                else ReduceNoWarning;
              (payment, finalAccs) =
                giveMoney accId payee token paidAmount newAccs;
              newState = (state \<lparr> accounts := finalAccs \<rparr>)
           in Reduced warning payment newState cont

    )"
  \<comment> \<open>An If contract is reduced to the corresponding continuation\<close>
| "reduceContractStep env state (If obs cont1 cont2) =
    (let cont = if evalObservation env state obs
                then cont1
                else cont2
     in Reduced ReduceNoWarning ReduceNoPayment state cont
    )"
  \<comment> \<open>A When contract is reduced to the contingeny continuation if the timeout is\<close>
  \<comment> \<open>in the past. If the timeout has not happened yet the contract is Quiescent\<close>
| "reduceContractStep env state (When _ timeout cont) =
    (let (startTime, endTime) = timeInterval env in
     if endTime < timeout
     then NotReduced
     else (if timeout \<le> startTime
           then Reduced ReduceNoWarning ReduceNoPayment state cont
           else AmbiguousTimeIntervalReductionError))"
  \<comment> \<open>A Let contract is always reduced to the continuation, with an optional Shadow\<close>
  \<comment> \<open>warning.\<close>
| "reduceContractStep env state (Let valId val cont) =
    (let evaluatedValue = evalValue env state val;
         boundVals = boundValues state;
         newState =
           state \<lparr> boundValues := MList.insert valId evaluatedValue boundVals \<rparr>;
         warn = case lookup valId boundVals of
                  Some oldVal \<Rightarrow> ReduceShadowing valId oldVal evaluatedValue
                | None \<Rightarrow> ReduceNoWarning
     in Reduced warn ReduceNoPayment newState cont
    )"
| "reduceContractStep env state (Assert obs cont) =
    (let warning = if evalObservation env state obs
                   then ReduceNoWarning
                   else ReduceAssertionFailed
     in Reduced warning ReduceNoPayment state cont)"


subsection \<open>Reduce contract until quiescent\label{sec:reduceContractUntilQuiescent}\<close>

text \<open>The datatype \<^emph>\<open>ReduceResult\<close> describes the result of calling
 \<^emph>\<open>reduceContractUntilQuiescent\<close>.
The function may produce an Ambiguous error if a call to \<^emph>\<open>reduceContractStep\<close> is ambiguous,
or it may result in a successful outcome with the following details:
\<^item> A flag that indicates whether the contract has been reduced (True) or not
\<^item> A list of warnings, excluding the ReduceNoWarning constructor
\<^item> A list of payments
\<^item> The new state after reducing the contract
\<^item> A quiescent contract that cannot be further reduced (because it has been completed or requires external input)\<close>

datatype ReduceResult
  = ContractQuiescent bool "ReduceWarning list" "Payment list" State Contract
  | RRAmbiguousTimeIntervalError

(*<*)
(* The following functions and lemmas are auxiliary to prove that reductionLoop
  terminates. They are hidden from the specification.
TODO: refactor the aux lemmas into a single Isar proof.
*)

lemma refundOneShortens : "refundOne acc = Some (c, nacc) \<Longrightarrow>
                           length nacc < length acc"
  apply (induction acc)
  apply simp
  by (metis Pair_inject length_Cons less_Suc_eq list.distinct(1)
            list.inject option.inject refundOne.elims)

fun evalBound :: "State \<Rightarrow> Contract \<Rightarrow> nat" where
"evalBound sta cont = length (accounts sta) + 2 * (size cont)"


lemma giveMoneyIncOne : "giveMoney sa p t m a = (e, na) \<Longrightarrow> length na \<le> length a + 1"
  apply (cases p)
  apply (cases "m \<le> 0")
  apply auto
  by (smt Suc_eq_plus1 delete_length insert_length le_Suc_eq)

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
  apply simp
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
(*>*)

text \<open>
The function \<^emph>\<open>reductionLoop\<close> recursively reduces the contract until it becomes
quiescent. In other programming languages, it could be defined as an inner function
of \<^emph>\<open>reduceContractUntilQuiescent\<close>, however, Isabelle does not support inner functions.
\<close>

text \<open>
The parameters of \<^emph>\<open>reductionLoop\<close> have the same meaning as the components of a
successful \<^emph>\<open>ReduceResult\<close>.
\<close>
function (sequential) reductionLoop ::
  "bool
  \<Rightarrow> Environment
  \<Rightarrow> State
  \<Rightarrow> Contract
  \<Rightarrow> ReduceWarning list
  \<Rightarrow> Payment list
  \<Rightarrow> ReduceResult"
where
"reductionLoop reduced env state contract warnings payments =
  (case reduceContractStep env state contract of
      Reduced warning effect newState cont \<Rightarrow>
        let
          newWarnings = if warning = ReduceNoWarning
                          then warnings
                          else warning # warnings;
          newPayments = case effect of
                          ReduceWithPayment payment \<Rightarrow> payment # payments
                        | ReduceNoPayment \<Rightarrow> payments
        in
          reductionLoop True env newState cont newWarnings newPayments
    | AmbiguousTimeIntervalReductionError \<Rightarrow>
       RRAmbiguousTimeIntervalError
    | NotReduced \<Rightarrow>
        \<comment> \<open>During the loop, we prepend the warnings and payments to their respective\<close>
        \<comment> \<open>lists, resulting in the last warning/payment appearing first.\<close>
        \<comment> \<open>After the recursion ends, we reverse the lists to restore the intended order.\<close>
        \<comment> \<open>This approach reduces the number of O(1) operations and requires only\<close>
        \<comment> \<open>one O(N) operation\<close>
        ContractQuiescent reduced (rev warnings) (rev payments) state contract)"
(*<*)
  by pat_completeness auto
termination reductionLoop
  apply (relation "measure (\<lambda>(_, (_, (state, (contract, _)))) . evalBound state contract)")
  apply blast
  using reduceContractStepReducesSize by auto

(* This lemma allows to work with the reductionLoop.induct theorem with a new name for the induction
   case.*)
lemmas reductionLoop_induct = reductionLoop.induct[case_names "reductionLoopInduction"]
(*>*)

text \<open>Then, the function \<^emph>\<open>reduceContractUntilQuiescent\<close> just calls the reduction loop with the initial values.\<close>

fun reduceContractUntilQuiescent ::
  "Environment
  \<Rightarrow> State
  \<Rightarrow> Contract
  \<Rightarrow> ReduceResult"
where
"reduceContractUntilQuiescent env state contract =
  reductionLoop False env state contract [] []"

subsection \<open>Apply inputs \label{sec:applyInputs}\<close>

text \<open>This section focuses on introducing the \<^emph>\<open>applyAllInputs\<close> function, which
 is responsible for applying a list of external inputs to a contract. To define
 this function, we need to first establish how to apply a single input to a
contract using \<^emph>\<open>applyInput\<close>. This, in turn, requires us to define
 how to apply an input to a Case statement with \<^emph>\<open>applyCases\<close>.\<close>

subsubsection \<open>Apply cases\<close>
text \<open>The following datatypes describes the result of calling \<^emph>\<open>applyCases\<close>\<close>

datatype ApplyWarning
  \<comment> \<open>No warning was produced by applying a case\<close>
  = ApplyNoWarning
  \<comment> \<open>A Deposit of zero or less token was asked\<close>
  | ApplyNonPositiveDeposit Party AccountId Token int

datatype ApplyResult
  \<comment> \<open>The input was applied succesfully to a case list, producing a new\<close>
  \<comment> \<open>state, continuation and optional warning\<close>
  = Applied ApplyWarning State Contract
  \<comment> \<open>No case in the list matched the input\<close>
  | ApplyNoMatchError

text \<open>
The \<^emph>\<open>applyCases\<close> function attempts to match an \<^emph>\<open>Input\<close> with an \<^emph>\<open>Action\<close>, applying
changes to the state on the first match, or returning \<^emph>\<open>ApplyNoMatchError\<close>
if there isn't a compatible Case. When an input matches a Deposit, funds are
 added to the corresponding account. When the input matches a Choice, the
selected value is stored. When the input matches a Notify, the state is not
modified.\<close>

fun applyCases :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Case list \<Rightarrow> ApplyResult"
where
"applyCases env state (IDeposit accId1 party1 tok1 amount)
            ((Case (Deposit accId2 party2 tok2 val) cont) # rest) =
  (if (accId1 = accId2 \<and> party1 = party2
       \<and> tok1 = tok2 \<and> amount = evalValue env state val)
   then
     let
       warning =
         if amount > 0
         then ApplyNoWarning
         else ApplyNonPositiveDeposit party2 accId2 tok2 amount;
       newState =
         state
           \<lparr> accounts := addMoneyToAccount accId1 tok1 amount (accounts state)
           \<rparr>
     in Applied warning newState cont
   else applyCases env state (IDeposit accId1 party1 tok1 amount) rest)"
|"applyCases env state (IChoice choId1 choice)
             ((Case (Choice choId2 bounds) cont) # rest) =
   (if (choId1 = choId2 \<and> inBounds choice bounds)
    then
      let
        newState =
          state
            \<lparr> choices := MList.insert choId1 choice (choices state)
            \<rparr>
      in
        Applied ApplyNoWarning newState cont
    else applyCases env state (IChoice choId1 choice) rest)"
|"applyCases env state INotify ((Case (Notify obs) cont) # rest) =
   (if evalObservation env state obs
    then Applied ApplyNoWarning state cont
    else applyCases env state INotify rest)"
\<comment> \<open>The following cases are explicit to avoid Isabelle from giving\<close>
\<comment> \<open>a "Ignoring duplicate rewrite rule" warning. In other languages\<close>
\<comment> \<open>(like Haskell) this could be simplified by a single match.\<close>
|"applyCases env state (IDeposit accId1 party1 tok1 amount) (_ # rest) =
   applyCases env state (IDeposit accId1 party1 tok1 amount) rest"
|"applyCases env state (IChoice choId1 choice) (_ # rest) =
   applyCases env state (IChoice choId1 choice) rest"
|"applyCases env state INotify (_ # rest) =
   applyCases env state INotify rest"
|"applyCases env state input [] = ApplyNoMatchError"

subsubsection \<open>Apply single input\<close>

text \<open>We can only apply an input to a list of cases, so if the contract is not
a When statement we return \<^emph>\<open>ApplyNoMatchError\<close>\<close>
fun applyInput :: "Environment \<Rightarrow> State \<Rightarrow> Input \<Rightarrow> Contract \<Rightarrow> ApplyResult"
where
 "applyInput env state input (When cases t cont) =
    applyCases env state input cases"
|"applyInput env state input c = ApplyNoMatchError"

subsubsection \<open>Apply multiple inputs\<close>
text \<open>The following functions are used to convert the intermediate warning representation
defined in the apply cases section and \<^emph>\<open>reduceContractStep\<close> \secref{sec:reduceContractStep}, to the
 final \<^emph>\<open>TransactionWarning\<close> representation defined in section \secref{sec:transaction}\<close>

fun convertReduceWarnings :: "ReduceWarning list \<Rightarrow> TransactionWarning list"
where
 "convertReduceWarnings [] = []"
|"convertReduceWarnings (ReduceNoWarning # rest) =
      convertReduceWarnings rest"
|"convertReduceWarnings ((ReduceNonPositivePay accId payee tok amount) # rest) =
    TransactionNonPositivePay accId payee tok amount # convertReduceWarnings rest"
|"convertReduceWarnings ((ReducePartialPay accId payee tok paid expected) # rest) =
    TransactionPartialPay accId payee tok paid expected # convertReduceWarnings rest"
|"convertReduceWarnings ((ReduceShadowing valId oldVal newVal) # rest) =
    TransactionShadowing valId oldVal newVal # convertReduceWarnings rest"
|"convertReduceWarnings (ReduceAssertionFailed # rest) =
    TransactionAssertionFailed # convertReduceWarnings rest"

fun convertApplyWarning :: "ApplyWarning \<Rightarrow> TransactionWarning list"
where
 "convertApplyWarning ApplyNoWarning = []"
|"convertApplyWarning (ApplyNonPositiveDeposit party accId tok amount) =
   [TransactionNonPositiveDeposit party accId tok amount]"

text \<open>
The following datatype describes the result of calling \<^emph>\<open>applyAllInputs\<close>. The
function may produce an \<^emph>\<open>ApplyAllAmbiguousTimeIntervalError\<close> if a \<^emph>\<open>When\<close> \<^emph>\<open>timeout\<close> is
ambiguous in the \<^emph>\<open>Environment\<close>, an \<^emph>\<open>ApplyAllNoMatchError\<close> if no action is matched by
the input or a successful outcome with the following details:

\<^item> A flag that indicates if the contract has changed as a result of applying the inputs
\<^item> A list of Transaction warnings
\<^item> A list of payments
\<^item> The new state
\<^item> The new contract
\<close>
datatype ApplyAllResult
  = ApplyAllSuccess bool "TransactionWarning list" "Payment list" State Contract
  | ApplyAllNoMatchError
  | ApplyAllAmbiguousTimeIntervalError


text \<open>
The function \<^emph>\<open>applyAllLoop\<close> recursively apply inputs to a contract. In other
programming languages, it could be defined as an inner function
of \<^emph>\<open>applyAllInputs\<close>, however, Isabelle does not support inner functions.
\<close>

text \<open>
The parameters of \<^emph>\<open>applyAllLoop\<close> have the same meaning as the components of a
successful \<^emph>\<open>ApplyAllResult\<close>.
\<close>
fun applyAllLoop ::
  "bool
  \<Rightarrow> Environment
  \<Rightarrow> State
  \<Rightarrow> Contract
  \<Rightarrow> Input list
  \<Rightarrow> TransactionWarning list
  \<Rightarrow> Payment list
  \<Rightarrow> ApplyAllResult"
where
"applyAllLoop contractChanged env state contract inps warnings payments =
   \<comment> \<open>Before calling applyInput we make sure that the contract is in a\<close>
   \<comment> \<open>quiescent state, meaning it has finished executing or is waiting\<close>
   \<comment> \<open>for an external input. During the first iteration of the loop, a\<close>
   \<comment> \<open>contract may not be in a quiescent state if it was constructed with\<close>
   \<comment> \<open>a statement other than a When or Close or if the When statement has\<close>
   \<comment> \<open>timed out with respect to the environment. For subsequent iterations\<close>
   \<comment> \<open>of the loop, this code reduces the continuation of the previous\<close>
   \<comment> \<open>applyInput, ensuring that the final continuation is quiescent.\<close>
   (case reduceContractUntilQuiescent env state contract of
      RRAmbiguousTimeIntervalError \<Rightarrow> ApplyAllAmbiguousTimeIntervalError
    | ContractQuiescent reduced reduceWarns pays curState cont \<Rightarrow>
       \<comment> \<open>Once the contract is quiescent we recursively apply all the inputs\<close>
       (case inps of
          [] \<Rightarrow> ApplyAllSuccess
                  (contractChanged \<or> reduced)
                  (warnings @ (convertReduceWarnings reduceWarns))
                  (payments @ pays)
                  curState cont
        | input # rest \<Rightarrow>
           (case applyInput env curState input cont of
              Applied applyWarn newState appliedCont \<Rightarrow>
                  applyAllLoop True env newState appliedCont rest
                               (warnings @ (convertReduceWarnings reduceWarns)
                                         @ (convertApplyWarning applyWarn))
                               (payments @ pays)
            | ApplyNoMatchError \<Rightarrow> ApplyAllNoMatchError)))"

(*<*)
(* This lemma allows to work with the applyAllLoop.induct theorem with a new name for the induction
   case.*)
lemmas applyAllLoop_induct = applyAllLoop.induct[case_names applyAllLoopInduction]
(*>*)


text \<open>Then, the function \<^emph>\<open>applyAllInputs\<close> just calls the \<^emph>\<open>applyAllLoop\<close> with the initial values.\<close>

fun applyAllInputs ::
  "Environment
  \<Rightarrow> State
  \<Rightarrow> Contract
  \<Rightarrow> Input list
  \<Rightarrow> ApplyAllResult"
where
"applyAllInputs env state contract inps =
  applyAllLoop False env state contract inps [] []"


subsection \<open>Compute transaction\label{sec:computeTransaction}\<close>

text \<open>
This section defines the function \<^emph>\<open>computeTransaction\<close> which is the entry point of
 the interpreter and plays a central role in executing Marlowe contracts on the
 blockchain. Given a Contract/State pair and a transaction, \<^emph>\<open>computeTransaction\<close>
 moves the contract forward and returns the new state and continuation, along with
any warnings and payments that may be generated. This function should be called on
the blockchain as part of the transaction validation.
\<close>

text \<open>
The \<^emph>\<open>IntervalResult\<close> datatype represents the result of calling \<^emph>\<open>fixInterval\<close>, an
 auxiliary function used in \<^emph>\<open>computeTransaction\<close>. The function makes sure that the 
provided interval is valid (it ends after it starts and is not in the past) and it 
may adjust the \<^emph>\<open>minState\<close> property of the contract state. If the transaction is 
computed successfully, the new \<^emph>\<open>minState\<close> becomes a lower bound on the observed time. 
It is important to note that the interpreter is composed of pure functions, so it can't 
query the current time. For the semantics to work as intended, it is expected that the 
blockchain that executes \<^emph>\<open>computeTransaction\<close> checks that \<^emph>\<open>startTime\<close> \le \<^emph>\<open>now\<close> \le \<^emph>\<open>endTime\<close>.

\<close>

datatype IntervalResult  
  = IntervalTrimmed Environment State
  | IntervalError IntervalError

fun fixInterval :: "TimeInterval \<Rightarrow> State \<Rightarrow> IntervalResult" where
"fixInterval (startTime, endTime) state = (
  let
    curMinTime = minTime state;
    newMinTime = max startTime curMinTime;
    env = \<lparr> timeInterval = (newMinTime, endTime) \<rparr>;
    newState = state \<lparr> minTime := newMinTime \<rparr>
  in
    if endTime < startTime then
      IntervalError (InvalidInterval (startTime, endTime))
    else if endTime < curMinTime then
      IntervalError (IntervalInPastError curMinTime (startTime, endTime))
    else
      IntervalTrimmed env newState
)"

fun computeTransaction ::
  "Transaction
  \<Rightarrow> State
  \<Rightarrow> Contract
  \<Rightarrow> TransactionOutput"
where
"computeTransaction tx state contract =
  (let
     inps = inputs tx
   in case fixInterval (interval tx) state of
     IntervalTrimmed env fixSta \<Rightarrow>
       (case applyAllInputs env fixSta contract inps of
          ApplyAllSuccess reduced warnings payments newState cont \<Rightarrow>
            if (\<not> reduced \<and> (contract \<noteq> Close \<or> accounts state = []))
            then TransactionError TEUselessTransaction
            else TransactionOutput \<lparr> txOutWarnings = warnings
                                   , txOutPayments = payments
                                   , txOutState = newState
                                   , txOutContract = cont \<rparr>
        | ApplyAllNoMatchError \<Rightarrow>
            TransactionError TEApplyNoMatchError
        | ApplyAllAmbiguousTimeIntervalError \<Rightarrow>
            TransactionError TEAmbiguousTimeIntervalError
       )
     | IntervalError error \<Rightarrow> TransactionError (TEIntervalError error))"

subsection \<open>Play trace\label{sec:playTrace}\<close>

text 
\<open>
The \<^emph>\<open>computeTransaction\<close> function is capable of processing currently running 
contracts, allowing them to move forward. However, there are instances where it is 
beneficial to replay the entire sequence of transactions from the beginning. This is 
where the \<^emph>\<open>playTrace\<close> function comes into play, which makes use of \<^emph>\<open>emptyState\<close> and 
\<^emph>\<open>playTraceAux\<close>. This function accepts an initial time, a contract, and a list of 
transactions as input, and it accumulates the outcome by invoking \<^emph>\<open>computeTransaction\<close> 
recursively.
\<close>

fun emptyState :: "POSIXTime \<Rightarrow> State" where
"emptyState initialTime = 
  \<lparr> accounts = MList.empty
  , choices = MList.empty
  , boundValues = MList.empty
  , minTime = initialTime 
  \<rparr>"

(* TODO: rename to playTraceLoop to keep consistency with reductionLoop and applyAllLoop  *)

fun playTraceAux ::
  "TransactionOutputRecord 
  \<Rightarrow> Transaction list 
  \<Rightarrow> TransactionOutput" 
where
 "playTraceAux res Nil = TransactionOutput res" 
|"playTraceAux \<lparr> txOutWarnings = warnings
              , txOutPayments = payments
              , txOutState = state
              , txOutContract = cont \<rparr> (h # t) =
   (let 
      transRes = computeTransaction h state cont 
    in 
      case transRes of
        TransactionOutput transResRec \<Rightarrow> 
          playTraceAux 
            (transResRec 
              \<lparr> txOutPayments := payments @ (txOutPayments transResRec)
              , txOutWarnings := warnings @ (txOutWarnings transResRec) 
              \<rparr>
            )
            t
      | TransactionError _ \<Rightarrow> transRes)"


fun playTrace :: 
  "POSIXTime 
  \<Rightarrow> Contract 
  \<Rightarrow> Transaction list 
  \<Rightarrow> TransactionOutput" 
where
"playTrace initialTime contract transactions = 
  playTraceAux 
    \<lparr> txOutWarnings = Nil
    , txOutPayments = Nil
    , txOutState = emptyState initialTime
    , txOutContract = contract 
    \<rparr> 
    transactions"


(*TODO: Move into its own module refactor and document, for now it is removed 
from the PDF*)
(*<*)
section \<open>Contract insights\<close>
subsection \<open>Transaction outcome\<close>
type_synonym TransactionOutcomes = "(Party \<times> int) list"

definition "emptyOutcome = (MList.empty :: TransactionOutcomes)"

lemma emptyOutcomeValid : "valid_map emptyOutcome"
  using MList.valid_empty emptyOutcome_def by auto

fun isEmptyOutcome :: "TransactionOutcomes \<Rightarrow> bool" where
"isEmptyOutcome trOut = list_all (\<lambda> (x, y) \<Rightarrow> y = 0) trOut"

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

subsection \<open>Contract participant\<close>
(* TODO: rename sig *)
fun addSig :: "Party list \<Rightarrow> Input \<Rightarrow> Party list" where
"addSig acc (IDeposit _ p _ _) = SList.insert p acc" |
"addSig acc (IChoice (ChoiceId _ p) _) = SList.insert p acc" |
"addSig acc INotify = acc"

type_synonym TransactionSignatures = "Party list"

fun getSignatures :: "Input list \<Rightarrow> TransactionSignatures" where
"getSignatures l = foldl addSig SList.empty l"

subsection \<open>Is quiescent\<close>
fun isQuiescent :: "Contract \<Rightarrow> State \<Rightarrow> bool" where
"isQuiescent Close state = (accounts state = [])" |
"isQuiescent (When _ _ _) _ = True" |
"isQuiescent _ _ = False"

subsection \<open>Maximum time\<close>
fun maxTimeContract :: "Contract \<Rightarrow> int"
and maxTimeCase :: "Case \<Rightarrow> int" where
"maxTimeContract Close = 0" |
"maxTimeContract (Pay _ _ _ _ contract) = maxTimeContract contract" |
"maxTimeContract (If _ contractTrue contractFalse) = max (maxTimeContract contractTrue) (maxTimeContract contractFalse)" |
"maxTimeContract (When [] timeout contract) = max timeout (maxTimeContract contract)" |
"maxTimeContract (When (head # tail) timeout contract) = max (maxTimeCase head) (maxTimeContract (When tail timeout contract))" |
"maxTimeContract (Let _ _ contract) = maxTimeContract contract" |
"maxTimeContract (Assert _ contract) = maxTimeContract contract" |
"maxTimeCase (Case _ contract) = maxTimeContract contract"


end
(*>*)
