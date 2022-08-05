(*<*)
theory Core
  imports 
      SpecificationLatexSugar
      Core.Semantics
      Core.SemanticsTypes

begin 
(*>*)
chapter \<open>Marlowe Core\<close>

section \<open>Types\<close>

subsection \<open>Contract\<close>
text \<open>@{datatype [display,names_short, margin=40]Contract}\<close>

subsection \<open>Value\label{sec:value}\<close>
text \<open>@{datatype [display,names_short, margin=40]Value}\<close>

subsection \<open>Input\<close>
text \<open>@{datatype [display,names_short, margin=40]Input}\<close>

subsection \<open>State\label{sec:state}\<close>
(* Sadly there is no antiquote to print a record, and I wasn't able to 
make the snipet import work (described in chapter 7 of the Sugar Latex PDF).
So to show records we need to duplicate the definition
 *)
record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minTime :: POSIXTime

subsection \<open>Environment\label{sec:environment}\<close>


record Environment = timeInterval :: TimeInterval

section \<open>Semantics\<close>

text \<open>TODO: Add the different functions and explanation \<close>



subsection \<open>Eval value\<close>
text \<open>Given the \hyperref[sec:environment]{@{typ Environment}} and the current 
 \hyperref[sec:state]{@{typ State}}, the @{const evalValue} function 
evaluates a \hyperref[sec:value]{@{typ Value}} into a number\<close>

text \<open>\<^emph>\<open>evalValue\<close> :: @{typeof evalValue}\<close>

subsubsection \<open>Available money\<close>
text \<open>For the \<^emph>\<open>AvailableMoney\<close> case, @{const evalValue} will give us the amount of @{typ Token}s
that a @{typ Party} has in their internal account.\<close>

text \<open>@{thm evalValue_AvailableMoney}\<close>

subsubsection \<open>Constant\<close>
text \<open>For the \<^emph>\<open>Constant\<close> case, @{const evalValue} will always evaluate to the same value\<close>

text \<open>@{thm evalValue_Constant}\<close>

subsubsection \<open>Add value\<close>

text \<open>For the \<^emph>\<open>AddValue\<close> case, @{const evalValue} will evaluate both sides and add them together.\<close>

text \<open>@{thm evalValue_AddValue}\<close>

text \<open>addition is associative\<close>

text \<open>@{thm evalAddAssoc}\<close>

text \<open>and commutative \<close>

text \<open>@{thm evalAddCommutative}\<close>

subsubsection \<open>Substract value\<close>
text \<open>For the \<^emph>\<open>SubValue\<close> case, @{const evalValue} will evaluate both sides and substract
the second value to the first.\<close>

text \<open>@{thm evalValue_SubValue}\<close>

subsubsection \<open>Negative\<close>
text \<open>For every value \<^emph>\<open>val\<close> there is the complement \<^emph>\<open>NegValue val\<close> so that\<close>

text \<open>@{thm evalNegValue}\<close>

subsubsection \<open>Multiplication\<close>

text \<open>For the \<^emph>\<open>MulValue\<close> case, @{const evalValue} will evaluate both sides and multiply them.\<close>
text \<open>@{thm evalValue_MulValue}\<close>

subsubsection \<open>Division\<close>
text \<open>Division is a special case because we only evaluate to natural numbers:
\<^item> If the numerator is 0, the denominator is not evaluated and the result is 0
\<^item> If the denominator is 0, the result is also 0. Other languages uses NaN or Infinity to represent this case
\<^item> The result will be rounded down if the remainder is lower than 1/2
\<^item> The result will be rounded up if the remainder is bigger than 1/2
\<^item> If the remainder is exactly 1/2, the result will be rounded down if the quotient is even or up if it is odd\<close>

text \<open>@{thm [display,names_short, margin=40] evalValue_DivValue}\<close>
text \<open>TODO: lemmas around division? maybe extend the following to proof evalValue and not just div\<close>
text \<open>@{thm divMultiply}\<close>
text \<open>@{thm divAbsMultiply}\<close>

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

subsection \<open>Eval Observation\label{sec:evalobservation}\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts evalObservation constant: evalObservation (Haskell)}\<close>

subsection \<open>Reduction Loop\label{sec:reductionloop}\<close>

text \<open>TODO: explain\<close>
text \<open>@{code_stmts reductionLoop constant: reductionLoop (Haskell)}\<close>

subsection \<open>Reduce Contract Until Quiescent\label{sec:reduceContractUntilQuiescent}\<close>

text \<open>TODO: explain\<close>
text \<open>@{code_stmts reduceContractUntilQuiescent constant: reduceContractUntilQuiescent (Haskell)}\<close>

subsection \<open>Apply All Inputs\label{sec:applyAllInputs}\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts applyAllInputs constant: applyAllInputs (Haskell)}\<close>

subsection \<open>Compute Transaction\label{sec:computeTransaction}\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts computeTransaction constant: computeTransaction (Haskell)}\<close>

subsection \<open>Play Trace\label{sec:playTrace}\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts playTrace constant: playTrace (Haskell)}\<close>

subsection \<open>Max Time\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts maxTimeContract constant: maxTimeContract (Haskell)}\<close>

subsection \<open>Fix Interval\<close>
text \<open>TODO: explain\<close>
text \<open>@{code_stmts fixInterval constant: fixInterval (Haskell)}\<close>

section \<open>Serialization\<close>
text \<open>TODO: Json and Cbor serialization\<close>

(*<*)
end
(*>*)