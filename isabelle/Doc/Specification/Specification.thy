(*<*)
theory Specification
  imports Main CodeExports.CodeExports Core.BigStep Core.SmallStep

begin
(*>*)

chapter \<open>Marlowe \label{sec:marlowe-chaper}\<close>

section \<open>Introduction\<close>

text
\<open>
Marlowe is a special purpose or domain-specific language (DSL) that is designed to be usable by
someone who is expert in the field of financial contracts, somewhat lessening the need for
programming skills.
\<close>

text
\<open>
Marlowe is modelled on special-purpose financial contract languages popularised in the last decade
or so by academics and enterprises such as LexiFi \<^footnote>\<open>\<^url>\<open>https://www.lexifi.com/\<close>\<close>, which provides contract
software in the financial sector. In developing Marlowe, we have adapted these languages to work on any blockchain \secref{sec:blockchain-agnostic}.
\<close>

text
\<open>
Where we differ from non-blockchain approaches is in how we make sure that the contract is followed.
In the smart contracts world there is a saying ``Code is law'', which implies that the assets deposited
in a contract will follow its logic, without the ability of a human to change the rules. This applies
for both the intended and not intended behaviour (in the form of bugs or exploits).\<close>

text \<open>To reduce the probability of not intended behaviour, the Marlowe DSL is designed with simplicity
in mind. Without loops, recursion, or other features that general purposes smart-contract languages
(E.g: Plutus, Solidity) have, it is easier to make certain claims. Each Marlowe contract can be
reasoned with a static analyzer to avoid common pitfalls such as trying to Pay more money than the
available. And the \<^emph>\<open>executable semantics\<close> that dictates the logic of \<^bold>\<open>all\<close> Marlowe contracts is
formalized with the proof-assistant Isabelle.
\<close>

text \<open>

Chapter \secref{sec:marlowe-chaper} provides an overview of the Marlowe language. Chapter
\secref{sec:marlowe-core} defines the Core language and semantics in detail. Chapter \secref{sec:marlowe-guarantees} presents
proofs that guarantee that Marlowe contracts possess properties desirable for financial agreements.
\<close>


section \<open>The Marlowe Model\<close>

text \<open>
Marlowe \<^term>\<open>Contract\<close>s describe a series of steps, typically by describing the first step, together with
another (sub-)contract that describes what to do next. For example, the contract
@{term "Pay a p t v c"} says ``make a payment of @{term v} number of tokens @{term t} to the party
@{term p} from the account @{term a}, and then follow the contract @{term c}''. We call @{term c} the
continuation of the contract.  All paths of the contract are made
explicit this way, and each \<^term>\<open>Contract\<close> term is executed at most once.
\<close>

subsection \<open>Data types\<close>
text \<open>The \<^term>\<open>Value\<close>s and \<^term>\<open>Observation\<close>s \secref{sec:values-and-observations} only works with
integers and booleans respectively. There is no native representation of decimal numbers, so in order to
represent currencies it is recommended to work with fractional units (like cents). For example, amounts of
Ada are represented in Lovelaces, because a Lovelace represents a one-millionth of an Ada. Dates are only
used in the context of \<^term>\<open>Timeout\<close>s and they are absolute.
\<close>


subsection \<open>Quiescent \label{sec:Quiescent}\<close>

text \<open>When a transaction is computed, the contract is reduced as much as possible.
When it cannot be reduced anymore the contract is considered quiescent, which means that it is either
 awaiting external input or has been fully executed\<close>

subsection \<open>Timeouts and Contingencies\<close>
text \<open>
The blockchain can't force a participant to make a transaction. To avoid having a participant blocking
the execution of a contract, whenever an \<^term>\<open>Input\<close> is expected, there is a \<^term>\<open>Timeout\<close> with a contingency
continuation. For each step, we can know in advance how long it can last, and we can extend this to
know the maximum duration and the amount of transactions of a contract.
\<close>

subsection \<open>Participants, accounts and state\<close>

text \<open>
Once we define a contract, we can see how many participants it will have. The number of participants
is fixed for the duration of the contract, but there are mechanisms to trade participation
 \secref{sec:participants-roles-and-addresses}.\<close>

text \<open>Each participant has an internal account that allows the contract to define default owner for
 assets \secref{sec:internal-accounts}. Whenever a \<^term>\<open>Party\<close> deposits an asset in the contract,
they need to decide the default owner of that asset. Payments can be made to transfer the default owner
or to take the asset out of the contract. If the contract is closed, the default owner can redeem
the assets available in their internal accounts.
\<close>

text \<open>
The accounts, choices, and variables stored in the \<^term>\<open>State\<close> \secref{sec:state} remain
in the \<^term>\<open>State\<close> until the contract is closed. But in the case of accounts and variables,
they are omitted for space efficiency if their value becomes 0, because that is their default value.
\<close>


subsection \<open>Core and Extended\<close>

text \<open>
The set of types and functions that conform the semantics executed in the blockchain is called
 \<^emph>\<open>Marlowe Core\<close>, and it's formalized in chapter \secref{sec:marlowe-core}. To improve usability, there
is another set of types and functions that compile to core, and it is called \<^emph>\<open>Marlowe Extended\<close>.
\<close>
text \<open>In the first version of the extended language, the only modification to the DSL is the addition
 of template parameters. These allows an initial form of contract reutilization, allowing to instantiate
the same contract with different \<^term>\<open>Value\<close>s and \<^term>\<open>Timeout\<close>s. For the moment, the extended
 language is not formalized in this specification but it will be added in the future
\<close>

section \<open>Specification generation and nomenclature \label{sec:generation-nomenclature}\<close>

text \<open>
The Marlowe specification is formalized using the proof assistant Isabelle\<^footnote>\<open>\<^url>\<open>https://isabelle.in.tum.de/\<close>\<close>.
The code is written in a literate programming style and this document is generated from the proofs.
This improves code documentation and lowers the probability of stale information.\<close>

text \<open>
As a drawback, the code/doc organization is more rigid. Isabelle require us to define code in a
bottom-up approach, having to define first the dependencies and later the most complex structures.
\<close>

text \<open>The notation is closer to a Mathematical formula than a functional programming language. There are
some configurations in the \<^emph>\<open>SpecificationLatexSugar\<close> theory file that makes the output be closer to code.
\<close>


(*<*)
end
(*>*)
