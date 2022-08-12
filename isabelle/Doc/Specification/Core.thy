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

text \<open>The Marlowe core types define the Marlowe DSL: @{type Contract} defines Marlowe contracts,
@{type State} tracks the state variables of such contracts, and @{type Environment} specifies the
execution environment for contracts.\<close>

text \<open>FIXME: Figure out how to prevent erasure of type synonyms in the antiquotations in this
section.\<close>

subsection \<open>Contract\<close>

text \<open>The simplest contract, @{term Close}, has completed its execution; other contracts include
one or more continuations for subsequent contract(s). The @{term When} and
@{term If} contracts branch on conditions. The @{term Pay} contract makes a payment to a
@{type Payee}. A @{term Let} contract assigns a value to a variable and an @{term Assert} contract
make an assertion about the contract's state that a particular condition should hold at that point
in the contract.
@{datatype [display,names_short, margin=40]Contract}
\<close>

text \<open>A contract @{term Close} provides for the contract to be closed (or terminated). The only
action that it performs is to provide refunds to the owners of accounts that contain a positive
balance. This is performed one account per step, but all accounts will be refunded in a single
transaction.\<close>

text \<open>A payment contract @{term "Pay a p t v c"} will make a payment of
value @{term v} of token @{term t} from the account @{term a} to a payee
@{term p}, which will be one of the contract participants or another account in the contract.
Warnings will be generated if the value v is negative, or if there is not enough in the account to
make the payment in full (even if there are positive balances of other tokens in the account). In
the latter case, a partial payment (of all the money available) is made. The continuation contract
is the one given in the contract: @{term c}.\<close>

text \<open>The conditional @{term "If b c1 c2"} will continue as
@{term c1} or @{term c2}, depending on the Boolean value of the observation
@{term b} when this construct is executed.\<close>

text \<open>@{term When} is the most complex constructor for contracts, with the form
@{term "When cs t c"}. It is a contract that is triggered on actions, which may
or may not happen at any particular time: what happens when various actions happen is described by
the cases in the contract. The list @{term cs} contains a collection of cases providing input to
the contract: the first case that is satisfied by external input is the one that is executed. In
order to make sure that the contract makes progress eventually, the contract will continue as
@{term c} when the @{term t}, a POSIX time, is reached.\<close>

text \<open>A @{term Let} contract @{term "Let i v c"} allows a contract to name a
value using an identifier @{term i}. In this case, the expression @{term v} is
evaluated, and stored with the name @{term i}. The contract then continues as
@{term c}. As well as allowing us to use abbreviations, this mechanism also means that we
can capture and save volatile values that might be changing with time, e.g. the current price of
oil, or the current time, at a particular point in the execution of the contract, to be used later
on in contract execution.
@{datatype [display,names_short, margin=40]ValueId}
\<close>

text \<open>An assertion contract @{term "Assert b c"} does not have any effect on
the state of the contract, it immediately continues as @{term c}, but it issues a warning
when the observation @{term b} is false. It can be used to ensure that a property holds
in any given point of the contract, since static analysis will fail if any execution causes a
warning.\<close>

subsection \<open>Case and Action\label{sec:case}\<close>

text \<open>The @{term Case} is used in @{term When} clauses to branch on input conditions or timeouts.
External inputs take the form of @{term Action}.
@{datatype [display,names_short, margin=40]Case}
\<close>

text \<open>Each case has the form @{term "Case a c"} where @{term a} is the external
input (an action) and @{term c} a continuation to another contract. When a particular action, e.g.
@{term a}, happens, the state is updated accordingly and the contract will continue as the
corresponding continuation @{term c}.\<close>

text \<open>Three kinds of action are possible: deposits, choices, and notifications.
@{datatype [display,names_short, margin=40]Action}
\<close>

text \<open>A @{term "Deposit a p t v"} makes a deposit of value @{term v} of token @{term t} from party
@{term p} into account @{term a}.\<close>

text \<open>A choice @{term "Choice i bs"} is made for a particular choice identified by @{term i}  with a
list of inclusive bounds @{term bs} on the values that are acceptable. For example,
@{text "[Bound 0 0, Bound 3 5]"} offers the choice of one of 0, 3, 4 and 5.
@{term [display,names_short, margin=40]Bound}
@{datatype [display,names_short, margin=40]ChoiceId}
@{term [display,names_short, margin=40]ChoiceName}
Choices of integers, @{term "ChoiceId c p"} are identified by the name @{term n} for the choice
and the party @{term p} who had made the choice.\<close>

text \<open>The contract is notified that a particular observation @{term b} is made via
@{term "Notify b"}; the contract only proceeds if the observation evaluates to true. Typically
notification would be done by one of the parties, or one of their wallets acting automatically.
Notifications also have the effect of pausing contract execution until the @{term Notify} is
received.\<close>

subsection \<open>Party and Payee\label{sec:party}\<close>

text \<open>A payment can be made to one of the parties to the contract, or to one of the accounts of the
contract. A party may be identified by a public-key hash or by a role.
@{datatype [display,names_short, margin=40]Payee}
@{datatype [display,names_short, margin=40]Party}
\<close>

text \<open>@{term "Account p"} identifies the internal account for party @{term p}, whereas
@{term "Party p"} identifies the internal account for that party.\<close>

text \<open>@{term "PubKey h"} identifies a party by the hash @{term h} of a public key, whereas
@{term "Role n"} identifies the party by the name @{term n} of their role.\<close>

text \<open>\<close>


subsection \<open>Value\label{sec:value}\<close>
text \<open>@{datatype [display,names_short, margin=40]Value}\<close>

subsection \<open>Observation\label{sec:observation}\<close>
text \<open>@{datatype [display,names_short, margin=40]Observation}\<close>

subsection \<open>Input\<close>
text \<open>@{datatype [display,names_short, margin=40]Input}\<close>

subsection \<open>State\label{sec:state}\<close>
text \<open>FIXME: Figure out how to display records via antiquotation.\<close>
(* Sadly there is no antiquote to print a record, and I wasn't able to 
make the snipet import work (described in chapter 7 of the Sugar Latex PDF).
So to show records we need to duplicate the definition
 *)
record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minTime :: POSIXTime

subsection \<open>Environment\label{sec:environment}\<close>

text \<open>FIXME: Figure out how to display records via antiquotation.\<close>
record Environment = timeInterval :: TimeInterval


subsection \<open>Token\label{sec:token}\<close>
text \<open>@{datatype [display,names_short, margin=40]Token}\<close>

subsection \<open>Type Synonyms\label{sec:synonyms}\<close>
text \<open>FIXME: Figure out how to display type synonyms here.\<close>


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