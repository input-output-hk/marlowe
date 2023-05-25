
(*<*)
theory SemanticsTypes
  imports
    BlockchainTypes
    Util.ByteString
    "Util.SpecificationLatexSugar"
begin
(*>*)

section \<open>Types\label{sec:core-types}\<close>

text \<open>This section introduces the data types of \<^emph>\<open>Marlowe Core\<close>, which encompass both the Marlowe DSL
and the types needed to call \<^term>\<open>computeTransaction\<close>\secref{sec:computeTransaction} .\<close>

text \<open>
Marlowe uses a literate programming approach in which the types are defined from the bottom up,
as explained in \secref{sec:generation-nomenclature}.
However, readers who prefer a top-down approach can also start with the Contract definition in \secref{sec:contracts}.
\<close>

subsection \<open>Participants, roles and addresses \label{sec:participants-roles-and-addresses}\<close>

text \<open>
We should separate the notions of participant, role, and address in a Marlowe contract. A
participant (or \<^term>\<open>Party\<close>) in the contract can be represented by either a fixed \<^term>\<open>Address\<close> or
a \<^term>\<open>Role\<close>.
\<close>

type_synonym RoleName = ByteString

datatype Party =
    Address Address
  | Role RoleName

text \<open>
An address party is defined by a blockchain specific \<^term>\<open>Address\<close> \secref{sec:blockchain-agnostic} and it cannot be traded
(it is fixed for the lifetime of a contract).
\<close>

text \<open>
A \<^term>\<open>Role\<close>, on the other hand, allows the participation of the contract to be dynamic. Any user that can prove to have permission to act
as \<^term>\<open>RoleName\<close> is able to carry
out the actions assigned \secref{sec:actions-and-inputs}, and redeem the payments issued to that role. The roles could be implemented
as tokens\<^footnote>\<open>In the Cardano implementation roles are represented by native tokens and they are distributed to addresses at the time a contract is
deployed to the blockchain\<close> that can be traded. By minting multiple tokens for a particular role,
several people can be given permission to act on behalf of that role simultaneously, this allows for more complex use cases.
\<close>

subsection \<open>Multi-Asset token\<close>

text
\<open>Inspired by Cardano's Multi-Asset tokens \<^footnote>\<open>\<^url>\<open>https://docs.cardano.org/native-tokens/learn\<close>\<close>, Marlowe also
supports to transact with different assets. A \<^term>\<open>Token\<close> consists of a \<^term>\<open>CurrencySymbol\<close> that
represents the monetary policy of the \<^term>\<open>Token\<close> and a \<^term>\<open>TokenName\<close> which allows to have multiple
tokens with the same monetary policy.
\<close>

datatype Token = Token CurrencySymbol TokenName

text \<open>The Marlowe semantics treats both types as opaque \<^term>\<open>ByteString\<close>.\<close>

subsection \<open>Accounts \label{sec:internal-accounts}\<close>

text \<open>

The Marlowe model allows for a contract to store assets. All participants of the
contract implicitly own an account identified with an \<^term>\<open>AccountId\<close>.
\<close>

type_synonym AccountId = Party

text \<open>
All assets stored in the contract must be in an internal account for one of the parties; this way,
when the contract is closed, all remaining assets can be redeemed by their respective owners. These
accounts are local: they only exist (and are accessible) within the contract.
\<close>

\<comment> \<open>TODO: Should we change int for nat, we shouldn't be able to have negative accounts.\<close>
type_synonym Accounts = "((AccountId \<times> Token) \<times> int) list"

text \<open>
During its execution, the contract can invite parties to deposit assets into an internal account through the construct
 ``\<^term>\<open>When [Deposit accountId party token value ] timeout continuation\<close>" . The contract can transfer
  assets internally (between accounts) or externally (from an account to a party) by using
 the term "\<^term>\<open>Pay accountId payee token value continuation\<close>'', where \<^term>\<open>Payee\<close> is:
\<close>

datatype Payee
  = Account AccountId
  | Party Party

text \<open>
A \<^term>\<open>Pay\<close> always takes money from an internal \<^term>\<open>AccountId\<close>, and the \<^term>\<open>Payee\<close>
 defines if we transfer internally (\<^term>\<open>Account p\<close>) or externally (\<^term>\<open>Party p\<close>)
\<close>

subsection \<open>Choices\label{sec:choices}\<close>

text \<open>
Choices -- of integers -- are identified by \<^term>\<open>ChoiceId\<close> which is defined with a canonical
name and the \<^term>\<open>Party\<close> who had made the choice:
\<close>

type_synonym ChoiceName = ByteString
datatype ChoiceId = ChoiceId ChoiceName Party

text \<open>Choices are \<^term>\<open>Bound\<close>ed. As an argument for the \<^term>\<open>Choice\<close> action \secref{sec:actions-and-inputs}, we
pass a list of \<^term>\<open>Bound\<close>s that limit the integer that we can choose. The \<^term>\<open>Bound\<close>
data type is a tuple of integers that represents an \<^bold>\<open>inclusive\<close> lower and upper bound.\<close>

datatype Bound = Bound int int

text \<open>A \<^emph>\<open>Choice\<close> is an external action \secref{sec:actions-and-inputs}, so it can only be made as part
of a \<^emph>\<open>When\<close> contract \secref{sec:contracts}\<close>

subsection \<open>Values and Observations\label{sec:values-and-observations} \<close>

text \<open>

We can store a \<^term>\<open>Value\<close> in the Marlowe State \secref{sec:state} using the \<^term>\<open>Let\<close>
 construct \secref{sec:contracts}, and we use a \<^term>\<open>ValueId\<close> to referrence it\<close>

datatype ValueId = ValueId ByteString

text \<open>\<^term>\<open>Value\<close>s and \<^term>\<open>Observation\<close>s are language terms that interact with most of the other constructs.
\<^term>\<open>Value\<close> evaluates to an integer and @{term Observation} evaluates to a boolean using \<^term>\<open>evalValue\<close>
 and \<^term>\<open>evalObservation\<close> \secref{sec:evalValueObservation} respectively.
\<close>

text \<open>They are defined in a mutually recursive way as follows:\<close>


datatype Value = AvailableMoney AccountId Token
               | Constant int
               | NegValue Value
               | AddValue Value Value
               | SubValue Value Value
               | MulValue Value Value
               | DivValue Value Value
               | ChoiceValue ChoiceId
               | TimeIntervalStart
               | TimeIntervalEnd
               | UseValue ValueId
               | Cond Observation Value Value
and Observation = AndObs Observation Observation
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

text \<open>Three of the @{type Value} terms look up information in the Marlowe state:
@{term "AvailableMoney p t"} reports the amount of token @{term t} in the internal account of party
@{term p}; @{term "ChoiceValue i"} reports the most recent value chosen for choice @{term i}, or
zero if no such choice has been made; and @{term "UseValue i"} reports the most recent value of the
variable @{term i}, or zero if that variable has not yet been set to a value.\<close>

text \<open>@{term "Constant v"} evaluates to the integer @{term v}, while @{term "NegValue x"},
@{term "AddValue x y"}, @{term "SubValue x y"}, @{term "MulValue x y"}, and @{term "DivValue x y"}
provide the common arithmetic operations @{term "- x"}, @{term "x + y"}, @{term "x - y"},
@{term "x * y"}, and @{term "x / y"}, where division always rounds (truncates) its result towards
zero.\<close>

text \<open>@{term "Cond b x y"} represents a condition expression that evaluates to @{term x} if
@{term b} is true and to @{term y} otherwise.\<close>

text \<open>The last @{term Value}s, @{term TimeIntervalStart} and @{term TimeIntervalEnd}, evaluate respectively to the
start or end of the validity interval for the Marlowe transaction.\<close>

text \<open>For the observations, the @{term "ChoseSomething i"} term reports whether a choice @{term i} has been made thus far in
the contract.\<close>

text \<open>The terms @{term TrueObs} and @{term FalseObs} provide the logical constants @{value true} and
@{value false}. The logical operators @{term "\<not> x"}, @{term "x \<and> y"},
and @{term "x \<or> y"} are represented by the terms @{term "NotObs x"}, @{term "AndObs x y"}, and
@{term "OrObs x y"}, respectively.\<close>

text \<open>Value comparisons @{term "x < y"}, @{term "x \<le> y"}, @{text "x > y"}, @{text "x \<ge> y"},
and @{term "x = y"} are represented by @{term "ValueLT x y"}, @{term "ValueLE x y"},
@{term "ValueGT x y"}, @{term "ValueGE x y"}, and @{term "ValueEQ x y"}.\<close>


subsection \<open>Actions and inputs\label{sec:actions-and-inputs}\<close>

text \<open>
We use @{term "Action"}s while designing a contract, which have a counterpart called
 @{term "Input"}s during execution. An @{term "Action"} can only appear in a
 @{term "Case"} statement together with a continuation. In turn, a @{term "Case"}
 can only appear inside a  @{term "When"} statement, and is the only way to declare
that an external @{term "Input"} is expected. When an @{term "Input"} is applied to
the contract, it is matched against the list of expected @{term "Action"} and the
first match is applied \secref{sec:applyInputs}.\<close>

text \<open>
The different types of actions are:
\<close>

datatype Action = Deposit AccountId Party Token Value
                | Choice ChoiceId "Bound list"
                | Notify Observation


text \<open>A @{term "Deposit a p t v"} makes a deposit of \#@{term v} @{term Token}s @{term t} from @{term "Party p"}
 into account @{term a}.\<close>

text \<open>A @{term "Choice i bs"} can be made for a particular option identified by the @{term ChoiceId}
 @{term i} \secref{sec:choices} with a list of inclusive bounds @{term bs} that indicates acceptable values.
For example, @{term "Choice (ChoiceId name party) [Bound 0 0, Bound 3 5]"} allows @{term party} to
choose either 0, 3, 4 or 5 in the @{term name} option.
\<close>

text \<open>To give integers a semantic meaning in the context of Choices, we make use of
the type synonym @{term ChosenNum}. To determine if a @{term ChosenNum} is within the
inclusive bounds list, we use the "inBounds" function. Note that the Isabelle function
 \<^emph>\<open>list\_ex\<close> is the same as the \<^emph>\<open>any\<close> function in other functional
languages\<close>

type_synonym ChosenNum = int

fun inBounds :: "ChosenNum \<Rightarrow> Bound list \<Rightarrow> bool" where
"inBounds num = list_ex (\<lambda> (Bound l u) \<Rightarrow> num \<ge> l \<and> num \<le> u)"

text \<open>A notification can be triggered by anyone as long as the \<^term>\<open>Observation\<close> evaluates
to \<^term>\<open>true\<close>. If multiple @{term "Notify"} are present in the \<^term>\<open>Case\<close> list, the first one with a \<^term>\<open>true\<close>
observation is matched.\<close>

text \<open>For each @{term "Action"}, there is a corresponding @{term "Input"} that can be included inside
a @{term "Transaction"} \secref{sec:transaction}\<close>

datatype Input = IDeposit AccountId Party Token int
               | IChoice ChoiceId ChosenNum
               | INotify

text \<open>The differences between the @{term Actions} and @{term Inputs} are:
\<^item> \<^term>\<open>Deposit\<close> uses a \<^term>\<open>Value\<close> while \<^term>\<open>IDeposit\<close> has the \<^term>\<open>int\<close> it was evaluated to with \<^term>\<open>evalValue\<close> \secref{sec:evalValueObservation}.
\<^item> \<^term>\<open>Choice\<close> defines a list of valid \<^term>\<open>Bound\<close>s while \<^term>\<open>IChoice\<close> has the actual \<^term>\<open>ChosenNum\<close>.
\<^item> \<^term>\<open>Notify\<close> has an \<^term>\<open>Observation\<close> while \<^term>\<open>INotify\<close> does not have arguments, the
 \<^term>\<open>Observation\<close> must evaluate to true inside the \<^term>\<open>Transaction\<close> \secref{sec:transaction}
\<close>

subsection \<open>Contracts \label{sec:contracts}\<close>

text \<open>
Marlowe is a continuation-based language, this means that a \<^term>\<open>Contract\<close> can either be a \<^term>\<open>Close\<close>
or another construct that recursively has a \<^term>\<open>Contract\<close>. Eventually, \<^bold>\<open>all\<close> contracts end up
with a \<^term>\<open>Close\<close> construct.
\<close>

text \<open>\<^term>\<open>Case\<close> and \<^term>\<open>Contract\<close> are defined in a mutually recursive way as follows:\<close>

datatype Case = Case Action Contract
and Contract = Close
             | Pay AccountId Payee Token Value Contract
             | If Observation Contract Contract
             | When "Case list" Timeout Contract
             | Let ValueId Value Contract
             | Assert Observation Contract

text \<open>@{term Close} is the simplest contract, when we evaluate it, the execution is completed and we
generate \<^term>\<open>Payment\<close>s for the assets in the internal accounts to their default owners
\<^footnote>\<open>Even if the payments are generated one at a time (per account and per Token), the cardano implementation
generates a single transaction\<close>.
\<close>

text \<open>
The contract \<^term>\<open>Pay a p t v c\<close>, generates a \<^term>\<open>Payment\<close> from the internal account \<^term>\<open>a\<close> to
a payee \secref{sec:internal-accounts} \<^term>\<open>p\<close> of \#\<^term>\<open>v\<close> \<^term>\<open>Token\<close>s and then continues to contract \<^term>\<open>c\<close>.
Warnings will be generated if the value @{term v} is not positive, or if there is not enough in the account to
make the payment in full. In the latter case, a partial payment (of the available amount) is made
\<close>

text \<open>The contract \<^term>\<open>If obs x y\<close> allows branching. We continue to branch \<^term>\<open>x\<close> if the \<^term>\<open>Observation obs\<close>
evaluates to \<^term>\<open>true\<close>, or to branch \<^term>\<open>y\<close> otherwise.
\<close>

text \<open>@{term When} is the most complex constructor for contracts, with the form
@{term "When cs t c"}. The list \<^term>\<open>cs\<close> contains zero or more pairs of \<^term>\<open>Action\<close>s and
 \<^term>\<open>Contract\<close> continuations. When we do a \<^term>\<open>computeTransaction\<close> \secref{sec:computeTransaction},
 we follow the continuation associated to the first \<^term>\<open>Action\<close> that matches the \<^term>\<open>Input\<close>. If no
 action is matched it returns a \<^term>\<open>ApplyAllNoMatchError\<close>. If a valid \<^term>\<open>Transaction\<close> is computed
 with a \<^term>\<open>TimeInterval\<close> with a start time bigger or equal to the \<^term>\<open>Timeout t\<close>, the contingency
 continuation \<^term>\<open>c\<close> is evaluated. The explicit timeout mechanism is what allows Marlowe to avoid
waiting forever for external inputs.\<close>

text \<open>A @{term Let} contract @{term "Let i v c"} allows a contract to record a
value using an identifier @{term i}. In this case, the expression @{term v} is
evaluated, and the result is stored with the name @{term i}. The contract then continues as
@{term c}. As well as allowing us to use abbreviations, this mechanism also means that we
can capture and save volatile values that might be changing with time, e.g.~the current price of
oil, or the current time, at a particular point in the execution of the contract, to be used later
on in contract execution.
\<close>

text \<open>An assertion contract @{term "Assert b c"} does not have any effect on
the state of the contract, it immediately continues as @{term c}, but it issues a warning
if the observation @{term b} evaluates to false. It can be used to ensure that a property holds
in a given point of the contract, since static analysis will fail if any execution causes a
warning. The @{term Assert} term might be removed from future on-chain versions of Marlowe.\<close>


subsection \<open>State \label{sec:state}\<close>

text \<open>
While executing a Marlowe contract, we keep track of the following information:
\<close>

record State
    \<comment> \<open>How many tokens each participant has inside the contract\<close>
  = accounts :: Accounts
    \<comment> \<open>A record of choices made by participants through the Choice Action\<close>
    choices :: "(ChoiceId \<times> ChosenNum) list"
    \<comment> \<open>Values stored by Let bindings\<close>
    boundValues :: "(ValueId \<times> int) list"
    \<comment> \<open>A low boundary on known real time\<close>
    minTime :: POSIXTime

text \<open>
The accounts, choices and boundValues are actually Map's but they are represented
here as association lists. Each blockchain has different capabilities to represent
data structutres, the most suitable one should be used in each case.
\<close>

text \<open>
The accounts should only have positive values. If a transaction asks to pay more assets
than available to the account, a partial payment warning is raised and the entry is
removed from the Map.
\<close>

text \<open>
Transactions have a validity time interval @{term "(startTime, endTime)"} which
 gives us a proxy for real time. It is up to the blockchain implementation to make sure
 that @{term startTime} \le @{term now} \le @{term endTime}. The variable @{term minTime}
 is the biggest known @{term startTime}. That allow us to trim a time interval and
ensure that @{term startTime} does not decrease between transactions.
\<close>

subsection \<open>Payment \label{sec:payment}\<close>

text \<open>

The \<^emph>\<open>Payment\<close> type represents the intention to transfer funds from the internal
 \<^emph>\<open>AccountId\<close> to a \<^emph>\<open>Payee\<close> \secref{sec:internal-accounts}. This type is created as a
result of executing a \<^emph>\<open>Pay\<close> statement and is included as part of the output of computing a
transaction.
\<close>

text \<open>
The \<^emph>\<open>Payee\<close> indicates whether the recipient of the payment is an internal account or
external participant. When we call \<^emph>\<open>computeTransaction\<close>, if the payment is internal,
the funds are transferred between internal state accounts and no further action is
required. In this case, the \<^emph>\<open>Payment\<close> type serves as an information of what has
happened. However, if the payment is external, the funds are removed from the state
account, but the actual transfer is expected to occur outside of the semantics
defined in this document.
\<close>

datatype Payment = Payment AccountId Payee Token int

subsection \<open>Transaction \label{sec:transaction}\<close>

text \<open>We use transactions to move contracts forward. Transactions are comprised of a
list of inputs (possibly empty) to be applied within a TimeInterval\<close>
record Transaction
  = interval :: TimeInterval
    inputs :: "Input list"

text \<open>

From the transaction we can extract the validity interval as its own type, which is
useful for functions like evalValue and evalObservation, which only depends on the interval.
\<close>
(* TODO: See if it makes sense to just use TimeInterval and to upgrade to Environment
         once we know more data should be present here *)
record Environment = timeInterval :: TimeInterval

text \<open>The rest of this section introduces the types used to represent the output of
\<^emph>\<open>computeTransaction\<close>.\<close>

text \<open>The following warnings are issues that can happen while executing a transaction.
They don't prevent the transaction from being completed, but they may indicate a poorly
 designed contract. Marlowe contracts can be statically analyzed to ensure that no
execution path results in a warning.\<close>

datatype TransactionWarning
  \<comment> \<open>A Deposit of a value lower or equal to 0 was asked\<close>
  \<comment> \<open>The contract will need an empty Deposit to advance\<close>
  = TransactionNonPositiveDeposit Party AccountId Token int
  \<comment> \<open>A Pay of a value lower or equal to 0 was asked\<close>
  \<comment> \<open>The contract won't produce any payment and continue\<close>
  | TransactionNonPositivePay AccountId Payee Token int
  \<comment> \<open>A payment is partially fulfilled as more assets \<close>
  \<comment> \<open>than available were required\<close>
  | TransactionPartialPay AccountId Payee Token int int
  \<comment> \<open>A variable already bound in the state is being overwritten\<close>
  \<comment> \<open>This doesn't necessarily indicate a problem and is the only\<close>
  \<comment> \<open>way to model mutable variables\<close>
  | TransactionShadowing ValueId int int
  \<comment> \<open>A custom Assert observation evaluates to False\<close>
  | TransactionAssertionFailed

text \<open>
The \<^emph>\<open>IntervalError\<close> type describes possible errors associated with the
 \<^emph>\<open>TimeInterval\<close>.
\<close>

datatype IntervalError
  \<comment> \<open>A TimeInterval is invalid if it ends before it starts\<close>
  = InvalidInterval TimeInterval
  \<comment> \<open>The interval is in the past if the endTime is bigger than\<close>
  \<comment> \<open>the last observed minTime\<close>
  | IntervalInPastError POSIXTime TimeInterval


text \<open>The following errors are issues that can happen while executing a transaction.
Unlike the warnings, they do prevent a transaction from being executed.\<close>

datatype TransactionError
  \<comment> \<open>A When's timeout is ambiguous w.r.t. the transaction's time interval\<close>
  = TEAmbiguousTimeIntervalError
  \<comment> \<open>No Case matched the provided Input\<close>
  | TEApplyNoMatchError
  \<comment> \<open>The transaction's TimeInterval has one of the problems described before\<close>
  | TEIntervalError IntervalError
  \<comment> \<open>The transaction does not have any effect\<close>
  | TEUselessTransaction

text \<open>In a time interval @{term "(startTime, endTime)"}, a When's @{term timeout} is
ambiguous iff @{term startTime} < @{term timeout} \le @{term endTime}. \<close>

text \<open>If a transaction is computed correctly it will yield a new state and contract
continuation with optional warnings and payments.\<close>

record TransactionOutputRecord
  = txOutWarnings :: "TransactionWarning list"
    txOutPayments :: "Payment list"
    txOutState :: State
    txOutContract :: Contract

text
\<open>
Finally, the \<^emph>\<open>TransactionOutput\<close> type captures the results of calling computeTransaction
\<close>
datatype TransactionOutput
  \<comment> \<open>The transaction was computed successfully\<close>
  = TransactionOutput TransactionOutputRecord
  \<comment> \<open>There was a problem computing the transaction\<close>
  | TransactionError TransactionError

(*<*)
end
(*>*)
