(*<*)
theory Core
  imports
      Core.Semantics
      Core.SemanticsTypes
      "Util.SpecificationLatexSugar"

begin
(*>*)

section \<open>Semantics\<close>

text \<open>Marlowe's behavior is defined via the \<^emph>\<open>operational semantics\<close> (or \<^emph>\<open>executable
semantics\<close>) of the Isabelle implementation of its @{const computeTransaction} function. That
function calls several auxiliary functions to apply inputs and find a quiescent state of the
contract. These, in turn, call evaluators for @{term Value} and @{term Observation}.\<close>

subsection \<open>Compute Transaction\label{sec:computeTransaction}\<close>

text \<open>The entry point into Marlowe semantics is the function @{const computeTransaction} that
applies input to a prior state to transition to a posterior state, perhaps reporting warnings or
throwing an error, all in the context of an @{term environment} \secref{sec:state-and-env} for the transaction.\<close>

text \<open>@{const computeTransaction} :: @{typeof computeTransaction}\<close>

(* FIXME: remove duplicate definition *)
record TransactionOutputRecord = txOutWarnings :: "TransactionWarning list"
                                 txOutPayments :: "Payment list"
                                 txOutState :: State
                                 txOutContract :: Contract


text \<open>
@{datatype [display,names_short, margin=40]TransactionOutput}
\<close> 

(* FIXME: remove duplicate definition *)
record Transaction = interval :: TimeInterval
                     inputs :: "Input list"


text \<open>This function adjusts the time interval for the transaction using @{const fixInterval} and
then applies all of the transaction inputs to the contract using @{const applyAllInputs}. It
reports relevant warnings and throws relevant errors.\<close>
text \<open>@{code_stmts computeTransaction constant: computeTransaction (Haskell)}\<close>

subsection \<open>Fix Interval\<close>

text \<open>The @{const fixInterval} functions combines the minimum-time constraint of @{term State}
with the time interval of @{term Environment} \secref{sec:state-and-env} to yield a ``trimmed'' validity interval and a minimum
time for the new state that will result from applying the transaction. It throws an error if the
interval is nonsensical or in the past.\<close>

(* FIXME: synonim are expanding *)
text \<open>@{code_stmts fixInterval constant: fixInterval (Haskell)}\<close>

subsection \<open>Apply All Inputs\label{sec:applyAllInputs}\<close>

text \<open>The @{const applyAllInputs} function iteratively progresses the contract and applies the
transaction inputs to the state, checking for errors along the way and continuing until all the inputs
are consumed and the contract reaches a quiescent state.\<close>
text \<open>@{code_stmts applyAllInputs constant: applyAllInputs (Haskell)}\<close>
text \<open>@{code_stmts applyAllLoop constant: applyAllLoop (Haskell)}\<close>

subsection \<open>Reduce Contract Until Quiescent\label{sec:reduceContractUntilQuiescent}\<close>

text \<open>The @{const reduceContractUntilQuiescent} executes as many non-input steps of the contract as
is possible. Marlowe semantics do not allow partial execution of a series of non-input steps.\<close>
text \<open>@{code_stmts reduceContractUntilQuiescent constant: reduceContractUntilQuiescent (Haskell)}\<close>

subsection \<open>Reduction Loop\label{sec:reductionloop}\<close>

text \<open>The @{const reductionLoop} function attempts to apply the next, non-input step to the
contract. It emits warnings along the way and it will through an error if it encounters an
ambiguous time interval.\<close>
text \<open>@{code_stmts reductionLoop constant: reductionLoop (Haskell)}\<close>

subsection \<open>Reduce Contract Step\label{sec:reducecontractstep}\<close>

text \<open>The @{const reduceContractStep} function handles the progression of the @{type Contract} in
the absence of inputs: it performs the relevant action (payments, state-change, etc.), reports warnings,
 and throws errors if needed. It stops reducing the contract at the point when the contract requires
external input.

Note that this function should report an implicit payment of zero (due to lack of funds) as a partial
payment of zero, not as a non-positive payment. An explicit payment of zero (due to the contract actually
specifying a zero payment) should be reported as a non-positive payment.\<close>
text \<open>@{code_stmts reduceContractStep constant: reduceContractStep (Haskell)}\<close>

subsection \<open>Apply Input\label{sec:applyinput}\<close>

text \<open>The @{const applyInput} function attempts to apply the next input to each @{term Case} in the
@{term When}, in sequence.\<close>
text \<open>@{code_stmts applyInput constant: applyInput (Haskell)}\<close>

subsection \<open>Apply Cases\label{sec:applycases}\<close>

text \<open>The @{const applyCases} function attempts to match an @{term Input} to an @{term Action},
compute the new contract state, emit warnings, throw errors if needed, and determine the appropriate
continuation of the contract.\<close>
text \<open>@{code_stmts applyCases constant: applyCases (Haskell)}\<close>

subsection \<open>Utilities\label{sec:accountutilities}\<close>

text \<open>The @{const moneyInAccount}, @{const updateMoneyInAccount}, and @{const addMoneyToAccount}
functions read, write, and increment the funds in a particular account of the @{term State},
respectively.\<close>
text \<open>@{code_stmts moneyInAccount constant: moneyInAccount (Haskell)}\<close>
text \<open>@{code_stmts updateMoneyInAccount constant: updateMoneyInAccount (Haskell)}\<close>
text \<open>@{code_stmts addMoneyToAccount constant: addMoneyToAccount (Haskell)}\<close>

(* TODO: This will become clearer after refactoring the semantics as literal programming PLT-3761 *)
text \<open>The @{const giveMoney} function is used in @{const reduceContractStep} to execute a Payment.
It takes as arguments the Party to remove funds from, the Payee to pay to, the amount and token to pay 
and the state accounts. It returns the Payment as a Reduce effect and the new state accounts.

\<close>
text \<open>@{code_stmts giveMoney constant: giveMoney (Haskell)}\<close>

text \<open>The @{const refundOne} function is also used inside @{const reduceContractStep}. It receives
the state accounts, and returns the first account with funds and the rest of the accounts.\<close>
text \<open>@{code_stmts refundOne constant: refundOne (Haskell)}\<close>

subsection \<open>Evaluate Value\label{sec:evalvalue}\<close>

text \<open>Given the \hyperref[sec:environment]{@{typ Environment}} and the current
 \hyperref[sec:state]{@{typ State}}, the @{const evalValue} function
evaluates a \hyperref[sec:value]{@{typ Value}} into a number\<close>

text \<open>@{const evalValue} :: @{typeof evalValue}\<close>

subsubsection \<open>Available Money\<close>

text \<open>For the \<^emph>\<open>AvailableMoney\<close> case, @{const evalValue} will give us the amount of @{typ Token}s
that a @{typ Party} has in their internal account.\<close>

text \<open>@{thm evalValue_AvailableMoney}\<close>

subsubsection \<open>Constant\<close>

text \<open>For the \<^emph>\<open>Constant\<close> case, @{const evalValue} will always evaluate to the same value\<close>

text \<open>@{thm evalValue_Constant}\<close>

subsubsection \<open>Addition\<close>

text \<open>For the \<^emph>\<open>AddValue\<close> case, @{const evalValue} will evaluate both sides and add them together.\<close>

text \<open>@{thm evalValue_AddValue}\<close>


subsubsection \<open>Subtraction\<close>

text \<open>For the \<^emph>\<open>SubValue\<close> case, @{const evalValue} will evaluate both sides and subtract
the second value from the first.\<close>

text \<open>@{thm evalValue_SubValue}\<close>

subsubsection \<open>Negation\<close>

text \<open>For every value \<^emph>\<open>x\<close> there is the complement \<^emph>\<open>NegValue x\<close> so that\<close>

text \<open>@{thm evalNegValue}\<close>

subsubsection \<open>Multiplication\<close>

text \<open>For the \<^emph>\<open>MulValue\<close> case, @{const evalValue} will evaluate both sides and multiply them.\<close>

text \<open>@{thm evalValue_MulValue}\<close>

subsubsection \<open>Division\<close>

text \<open>Division is a special case because we only evaluate to integers:
\<^item> If the denominator is 0, the result is also 0. Other languages uses NaN or Infinity to represent this case
\<^item> The result will be rounded towards zero.\<close>

text \<open>@{thm [display,names_short, margin=40] evalValue_DivValue}\<close>

text \<open>@{thm evalDivRoundToZero}\<close>

subsubsection \<open>Choice Value\<close>

text \<open>For the \<^emph>\<open>ChoiceValue\<close> case, @{const evalValue} will look in its state if a @{typ Party} has
made a choice for the @{typ ChoiceName}. It will default to zero if it doesn't find it.\<close>
text \<open>@{thm evalValue_ChoiceValue}\<close>

subsubsection \<open>Time Interval Start\<close>

text \<open>All transactions are executed in the context of a valid time interval. For the \<^emph>\<open>TimeIntervalStart\<close> case,
@{const evalValue} will return the beginning of that interval.\<close>
text \<open>@{thm evalValue_TimeIntervalStart}\<close>

subsubsection \<open>Time Interval End\<close>

text \<open>All transactions are executed in the context of a valid time interval. For the \<^emph>\<open>TimeIntervalEnd\<close> case,
@{const evalValue} will return the end of that interval.\<close>
text \<open>@{thm evalValue_TimeIntervalEnd}\<close>

subsubsection \<open>Use Value\<close>

text \<open>For the \<^emph>\<open>TimeIntervalEnd\<close> case, @{const evalValue} will look in its state for a bound @{typ ValueId}.
It will default to zero if it doesn't find it.\<close>

text \<open>@{thm evalValue_UseValue}\<close>

subsubsection \<open>Conditional Value\<close>

text \<open>For the \<^emph>\<open>Cond\<close> case, @{const evalValue} will first call \hyperref[sec:evalobservation]{@{const evalObservation}}
on the condition, and it will evaluate the the true or false value depending on the result.\<close>

text \<open>@{thm evalValue_Cond}\<close>

subsection \<open>Evaluate Observation\label{sec:evalobservation}\<close>

text \<open>Given the \hyperref[sec:environment]{@{typ Environment}} and the current
 \hyperref[sec:state]{@{typ State}}, the @{const evalObservation} function
evaluates an \hyperref[sec:observation]{@{typ Observation}} into a number\<close>

text \<open>@{const evalObservation} :: @{typeof evalObservation}\<close>

subsubsection \<open>True and False\<close>

text \<open>The logical constants @{value true} and @{value false} are trivially evaluated.\<close>

text \<open>@{thm evalObservation_TrueObs}\<close>

text \<open>@{thm evalObservation_FalseObs}\<close>

subsubsection \<open>Not, And, Or\<close>

text \<open>The standard logical operators \<open>\<not>\<close>, \<open>\<and>\<close>, and \<open>\<or>\<close> are evaluated in a
straightforward manner.\<close>

text \<open>@{thm evalObservation_NotObs}\<close>

text \<open>@{thm evalObservation_AndObs}\<close>

text \<open>@{thm evalObservation_OrObs}\<close>

subsubsection \<open>Comparison of Values\<close>

text \<open>Five functions are provided for the comparison (equality and ordering of integer values) have
traditional evaluations: \<open>=\<close>,\<open><\<close>, \<open>\<le>\<close>, \<open>>\<close>, and \<open>\<ge>\<close>.\<close>

text \<open>@{thm evalObservation_ValueEQ}\<close>

text \<open>@{thm evalObservation_ValueLT}\<close>

text \<open>@{thm evalObservation_ValueLE}\<close>

text \<open>@{thm evalObservation_ValueGT}\<close>

text \<open>@{thm evalObservation_ValueGE}\<close>

subsubsection \<open>Chose Something\<close>

text \<open>The @{term "ChoseSometing i"} term evaluates to true if the a choice @{term i} was previously
made in the history of the contract.\<close>

text \<open>@{thm evalObservation_ChoseSomething}\<close>

(*

subsection \<open>Play Trace\label{sec:playTrace}\<close>

text \<open>TODO: explain\<close>
text \<open>@{code_stmts playTrace constant: playTrace (Haskell)}\<close>

subsection \<open>Max Time\<close>

text \<open>TODO: explain\<close>
text \<open>@{code_stmts maxTimeContract constant: maxTimeContract (Haskell)}\<close>

section \<open>Transaction times\label{sec:transaction-times}\<close>

text \<open>TODO: explain how minTime relates to the transaction interval, and how to
reach errors: ApplyAllAmbiguousTimeIntervalError, IntervalInPastError, etc\<close>


section \<open>Serialization\<close>
text \<open>TODO: Json and Cbor serialization\<close>

*)

(*<*)
end
(*>*)
