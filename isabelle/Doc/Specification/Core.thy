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
text \<open>FIXME: Figure out how to display type synonyms where they are displayed in this section.\<close>
text \<open>FIXME: Figure out how to emit Isabelle instead of Haskell in "code stmnts" construct.\<close>

subsection \<open>Contract\<close>

text \<open>The simplest contract, @{term Close}, has completed its execution; other contracts include
one or more continuations for subsequent contract(s). The @{term When} and
@{term If} contracts branch on conditions. The @{term Pay} contract makes a payment to a
@{type Payee}. A @{term Let} contract assigns a value to a variable and an @{term Assert} contract
make an assertion about the contract's state that a particular condition should hold at that point
in the contract.
@{datatype [display,names_short, margin=40]Contract}
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]Timeout}
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
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]Bound}
@{datatype [display,names_short, margin=40]ChoiceId}
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]ChoiceName}
\<close> text \<open>Choices of integers, @{term "ChoiceId c p"} are identified by the name @{term n} for the choice
and the party @{term p} who had made the choice.\<close>

text \<open>The contract is notified that a particular observation @{term b} is made via
@{term "Notify b"}; the contract only proceeds if the observation evaluates to true. Typically
notification would be done by one of the parties, or one of their wallets acting automatically.
Notifications also have the effect of pausing contract execution until the @{term Notify} is
received.\<close>

subsection \<open>Input\<close>

text \<open>External @{type Input} to a contract directly corresponds to the @{type Action} that handles
such input.
@{datatype [display,names_short, margin=40]Input}
\<close>

text \<open>A deposit input @{term "IDeposit a p t v"} exactly matches the action
@{term "Deposit a p t v"}. A choice input @{term "IChoice i x"} corresponds to the action
@{term "Choice i bs"} where the integer @{term x} falls within the bounds @{term bs}. The input
@{term INotify} triggers the contract to evaluate the condition @{term b} in the action
@{term "Notify b"}.\<close>

subsection \<open>Party and Payee\label{sec:party}\<close>

text \<open>A payment can be made to one of the parties to the contract, or to one of the accounts of the
contract. A party may be identified by a public-key hash or by a role.
@{datatype [display,names_short, margin=40]Payee}
@{datatype [display,names_short, margin=40]Party}
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]AccountId}
\<close>

text \<open>@{term "Account p"} identifies the internal account for party @{term p}, whereas
@{term "Party p"} identifies the internal account for that party.\<close>

text \<open>@{term "PubKey h"} identifies a party by the hash @{term h} of a public key, whereas
@{term "Role n"} identifies the party by the name @{term n} of their role.
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]PubKey}
  \<close>

subsection \<open>Value\label{sec:value}\<close>

text \<open>A @{type Value} is a term that evaluates to an integer, given the current state of the Marlowe
contract.
@{datatype [display,names_short, margin=40]Value}
\<close>

text \<open>Three of the @{type Value} terms look up information in the Marlowe state:
@{term "AvailableMoney p t"} reports the amount of token @{term t} in the internal account of party
@{term p}; @{term "ChoiceValue i"} reports the most recent value chosen for choice @{term i}, or
zero if no such choice has been made; and @{term "UseValue i"} reports the most recent value of the
variable @{term i}, or zero if that variable has not yet been set to a value.\<close>

text \<open>@{term "Constant v"} evaluates to the integer @{term x}, while @{term "NegValue x"},
@{term "AddValue x y"}, @{term "SubValue x y"}, @{term "MulValue x y"}, and @{term "DivValue x y"}
provide the common arithmetic operations @{term "- x"}, @{term "x + y"}, @{term "x - y"},
@{term "x * y"}, and @{term "x / y"}, where division always rounds (truncates) its result towards
zero.\<close>

text \<open>@{term "Cond b x y"} represents a condition expressions that evaluates to @{term x} if
@{term b} is true and to @{term y} if @{term b} is false.\<close>

text \<open>Finally, @{term TimeIntervalStart} and @{term TimeIntervalEnd} evaluate respectively to the
start or end of the validity interval for the Marlowe transaction.\<close>

subsection \<open>Observation\label{sec:observation}\<close>

text \<open>A @{type Observation} evaluates to a logical value (true or false), given the current statet
of the Marlowe contract.
@{datatype [display,names_short, margin=40]Observation}
\<close>

text \<open>The @{term "ChoseSomething i"} term reports whether a choice @{term i} has been made thus far in
the contract.\<close>

text \<open>The terms @{term TrueObs} and @{term FalseObs} provide the logical constants @{value true} and
@{value false}. The logical operators @{term "\<not> x"}, @{term "x \<and> y"},
and @{term "x \<or> y"}are represented by the terms @{term "NotObs x"}, @{term "AndObs x y"}, and
@{term "OrObs x y"}, respectively.\<close>

text \<open>Value comparisons @{term "x < y"}, @{term "x \<le> y"}, @{term "x > y"}, @{term "x \<ge> y"},
and @{term "x = y"} are represented by @{term "ValueLT x y"}, @{term "ValueLE x y"},
@{term "ValueGT x y"}, @{term "ValueGE x y"}, and @{term "ValueEQ x y"}.\<close>

subsection \<open>Token\label{sec:token}\<close>

text \<open>Each currency in the contract is represented by a @{type Token} that consists of a symbol
@{term CurrencySymbol} and a name @{term TokenName}, each represented by bytes.
@{datatype [display,names_short, margin=40]Token}
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]CurrencySymbol}
\<close> text \<open>FIXME: print type synonym: @{term [names_short, margin=40]TokenName}
\<close>

subsection \<open>State\label{sec:state}\<close>

text \<open>The internal state of a Marlowe contract consists of the current balances in each party's
account, a record of the most recent value of each type of choice, a record of the most recent
value of each variable, and the minimum time for which input can be applied to the contract. The
data for accounts, choices, and bound values are stored as association lists.\<close>
(* Sadly there is no antiquote to print a record, and I wasn't able to 
make the snipet import work (described in chapter 7 of the Sugar Latex PDF).
So to show records we need to duplicate the definition
 *)
text \<open>FIXME: Print record:\<close>
record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minTime :: POSIXTime
text \<open>FIXME: print type synonym: @{term [names_short, margin=40]Accounts}\<close>

subsection \<open>Environment\label{sec:environment}\<close>

text \<open>The execution environment of a Marlowe contract simply consists of the (inclusive) time
interval within which the transaction is occurring.\<close>
record Environment = timeInterval :: TimeInterval
text \<open>FIXME: Print record:
@{term [names_short, margin=40]TimeInterval}
\<close>

section \<open>Semantics\<close>

text \<open>Marlowe's behavior is defined via the \<^emph>\<open>operational semantics\<close> (or \<^emph>\<open>executable
semantics\<close>) of the Isabelle implementation of its @{const computeTransaction} function. That
function calls several auxiliary functions to apply inputs and find a quiescent state of the
contract. These, in turn, call evaluators for @{term Value} and @{term Observation}.\<close>

subsection \<open>Compute Transaction\label{sec:computeTransaction}\<close>

text \<open>The entry point into Marlowe semantics is the function @{const computeTransaction} that
applies input to a prior state to transition to a posterior state, perhaps reporting warnings or
throwing an error, all in the context of an environment for the transaction.\<close>
text \<open>@{const computeTransaction} :: @{typeof computeTransaction}\<close>
text \<open>FIXME: Print record: @{term [names_short, margin=40]Transaction}
@{datatype [display,names_short, margin=40]TransactionOutput}
\<close> text \<open>FIXME: Print record: @{term [names_short, margin=40]TransactionOutputRecord}
\<close>

text \<open>This function adjusts the time interval for the transaction using @{const fixInterval} and
then applies all of the transaction inputs to the contract using @{const applyAllInputs}. It
reports relevant warnings and throws relevant errors.\<close>
text \<open>@{code_stmts computeTransaction constant: computeTransaction (Haskell)}\<close>

subsection \<open>Fix Interval\<close>

text \<open>The @{const fixInterval} functions combines the minimum-time constraint of @{term State}
with the time interval of @{term Environment} to yield a "trimmed" validity interval and a minimum
time for the new state that will result from applying the transaction. It throws an error if the
interval is nonsensical or in the past.\<close>
text \<open>@{code_stmts fixInterval constant: fixInterval (Haskell)}\<close>

subsection \<open>Apply All Inputs\label{sec:applyAllInputs}\<close>

text \<open>The @{const applyAllInputs} function iteratively applies the transaction inputs to the state,
checking for errors along the way and continuing until the contract reaches a quiescent state.\<close>
text \<open>@{code_stmts applyAllInputs constant: applyAllInputs (Haskell)}\<close>
text \<open>@{code_stmts applyAllLoop constant: applyAllLoop (Haskell)}\<close>

subsection \<open>Reduce Contract Until Quiescent\label{sec:reduceContractUntilQuiescent}\<close>

text \<open>The @{const reduceContractUntilQuiescent} executes as many non-input steps of the contract as
is possible.\<close>
text \<open>@{code_stmts reduceContractUntilQuiescent constant: reduceContractUntilQuiescent (Haskell)}\<close>

subsection \<open>Reduction Loop\label{sec:reductionloop}\<close>

text \<open>The @{const reductionLoop} function attempts to apply the next, non-input step to the
contract. It emits warnings along the way and it will through an error if it encounters an
ambiguous time interval.\<close>
text \<open>@{code_stmts reductionLoop constant: reductionLoop (Haskell)}\<close>

subsection \<open>Reduce Contract Step\label{sec:reducecontractstep}\<close>

text \<open>The @{const reduceContractStep} function handles is @{type Contract} case, performing the
relevant action (payments, state-change, etc.), reporting warning and throwing errors if needed.\<close>
text \<open>@{code_stmts reduceContractStep constant: reduceContractStep (Haskell)}\<close>

subsection \<open>Apply Input\label{sec:applyinput}\<close>

text \<open>The @{const applyInput} function attempts to apply the next input each @{term Case} in the
@{term When}, in sequence.\<close>
text \<open>@{code_stmts applyInput constant: applyInput (Haskell)}\<close>

subsection \<open>Apply Cases\label{sec:applycases}\<close>

text \<open>The @{const applyCases} function attempts to match an @{term Input} to an @{term Action},
compute the new contract state, emit warnings, throw errors if needed, and determine the appropriate
continuation of the contract.\<close>
text \<open>@{code_stmts applyCases constant: applyCases (Haskell)}\<close>

subsection \<open>Account Utilitiesn\label{sec:accountutilities}\<close>

text \<open>The @{const moneyInAccount}, @{const updateMoneyInAccount}, and @{const addMoneyToAccount}
functions read, write, and increment the funds in a particular account of the @{term State},
respectively. The @{const giveMoney} function transfer funds internally between accounts. The
@{const refundOne} function finds the first account with funds in it.\<close>
text \<open>@{code_stmts moneyInAccount constant: moneyInAccount (Haskell)}\<close>
text \<open>@{code_stmts updateMoneyInAccount constant: updateMoneyInAccount (Haskell)}\<close>
text \<open>@{code_stmts addMoneyToAccount constant: addMoneyToAccount (Haskell)}\<close>
text \<open>@{code_stmts giveMoney constant: giveMoney (Haskell)}\<close>
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

text \<open>Addition is associative and commutative:\<close>

text \<open>@{thm evalAddAssoc}\<close>

text \<open>@{thm evalAddCommutative}\<close>

subsubsection \<open>Subtraction\<close>

text \<open>For the \<^emph>\<open>SubValue\<close> case, @{const evalValue} will evaluate both sides and subtract
the second value to the first.\<close>

text \<open>@{thm evalValue_SubValue}\<close>

subsubsection \<open>Negation\<close>

text \<open>For every value \<^emph>\<open>val\<close> there is the complement \<^emph>\<open>NegValue val\<close> so that\<close>

text \<open>@{thm evalNegValue}\<close>

subsubsection \<open>Multiplication\<close>

text \<open>For the \<^emph>\<open>MulValue\<close> case, @{const evalValue} will evaluate both sides and multiply them.\<close>

text \<open>@{thm evalValue_MulValue}\<close>

subsubsection \<open>Division\<close>

text \<open>Division is a special case because we only evaluate to natural numbers: 
\<^item> If the numerator is 0, the denominator is not evaluated and the result is 0
\<^item> If the denominator is 0, the result is also 0. Other languages uses NaN or Infinity to represent this case
\<^item> The result will be rounded towards zero.\<close>

text \<open>@{thm [display,names_short, margin=40] evalValue_DivValue}\<close>

text \<open>TODO: lemmas around division? maybe extend the following to proof evalValue and not just div\<close>
text \<open>@{thm divMultiply}\<close>
text \<open>@{thm divAbsMultiply}\<close>
text \<open>COMMENT(BWB): I suggest that the lemmas be (i) exact multiples divide with no remainder, (ii)
      the remainder equals the excess above an exact multiple, and (iii) negation commutues with
      division.\<close>

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

section \<open>Serialization\<close>
text \<open>TODO: Json and Cbor serialization\<close>

*)

(*<*)
end
(*>*)