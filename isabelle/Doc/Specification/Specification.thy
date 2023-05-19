(*<*)
theory Specification
  imports Main CodeExports.CodeExports

begin
(*>*)

chapter \<open>Marlowe \label{sec:marlowe-chaper}\<close>

section \<open>Introduction\<close>

text
\<open>
Marlowe is a domain-specific language (DSL) for multi-party financial contracts. The language and
it's operational semantics are formalized in the Isabelle proof-assistant.
\<close>

text
\<open>
Marlowe has been inspired by financial contract languages popularised in the last decade by academics
and enterprises such as LexiFi \<^footnote>\<open>\<^url>\<open>https://www.lexifi.com/\<close>\<close>, that is providing contract modelling
software for the financial sector.

\<close>

text
\<open>
With Marlowe we have a strong focus on operational semantics, as the goal was to develop a language that
can also run on a blockchain \secref{sec:blockchain-agnostic}.\<close>

text \<open>
Smart contracts are immutable, that means that the assets deposited into a contract will inevitably follow
the contract logic. In order to reduce the probability of not intended behaviour, the Marlowe DSL is designed
with simplicity in mind. Without loops, recursion, or other features that general purposes smart-contract
languages (E.g: Plutus, Solidity) have, it is easier to make certain claims. Each Marlowe contract can be
reasoned with a static analyzer to avoid common pitfalls such as trying to Pay more money than
available.\<close>

text \<open>

Chapter \secref{sec:marlowe-chaper} provides an overview of the Marlowe language. Chapter
\secref{sec:marlowe-core} defines the Core language and semantics in detail. Chapter \secref{sec:marlowe-guarantees} presents
proofs of desirable properties for financial agreements.
\<close>


section \<open>The Marlowe Model\<close>

text \<open>
Marlowe \<^term>\<open>Contract\<close>s describe a series of sequential steps. For example, the contract
@{term "Pay a p t v c"} says ``make a payment of @{term v} number of tokens @{term t} to the party
@{term p} from the account @{term a}, and then follow the contract @{term c}''. We call @{term c} the
continuation of the contract. The \<^term>\<open>Contract\<close> has a tree structure with \<^term>\<open>Close\<close>
\<^term>\<open>Contract\<close>s in the leafs and the branches represent all possible paths of a \<^term>\<open>Contract\<close>.\<close>

subsection \<open>Data types\<close>
text \<open>The \<^term>\<open>Value\<close>s and \<^term>\<open>Observation\<close>s \secref{sec:values-and-observations} are restricted to work with
integers and booleans respectively. There is no native representation of decimal numbers, so in order to
represent currencies it is recommended to work with fractional units (like cents). For example, amounts of
Ada are represented in Lovelaces, because a Lovelace represents a one-millionth of an Ada. Dates are only
used in the context of \<^term>\<open>Timeout\<close>s and they are absolute.
\<close>


subsection \<open>Quiescent \label{sec:Quiescent}\<close>

text \<open>When a transaction is computed, the contract is reduced as far as possible up to a point
where it is considered quiescent, which means that it is either awaiting external input or has been fully executed.\<close>

subsection \<open>Timeouts and Contingencies\<close>
text \<open>
The blockchain can't force a participant to make a transaction. Therefore in order to avoid having a participant blocking
the progression of a contract, there is a \<^term>\<open>Timeout\<close> for applying \<^term>\<open>Input\<close>s together with a continuation
contract in case of a timeout. For each step, we can know in advance how long it can last, and therefore know as well the
maximum duration and the number of transactions of a contract.
\<close>

subsection \<open>Participants, accounts and state\<close>

text \<open>
A contract explicitly defines the participants. The number of participants is therefore fixed for the duration
of the contract, but there are mechanisms to trade participation \secref{sec:participants-roles-and-addresses}.\<close>

text \<open>Each participant has an internal account that allows the contract to keep track of the owner of the
 assets \secref{sec:internal-accounts}. Whenever a \<^term>\<open>Party\<close> deposits an asset into a contract,
they need to assign the owner of that asset. Payments can be made to transfer ownership
or to take the asset out of the contract. When the contract is closed, an owner of an asset can redeem
the available funds.
\<close>

text \<open>
The accounts, choices, and variables are stored in the \<^term>\<open>State\<close> \secref{sec:state} and remain
there until the contract is closed, and in the case of accounts and variables
those are omitted for space efficiency if their value becomes 0.
\<close>


subsection \<open>Core and Extended\<close>

text \<open>
The set of types and functions that conforms to the semantics executed on the blockchain is called
 \<^emph>\<open>Marlowe Core\<close>, and it's formalized in chapter \secref{sec:marlowe-core}. To improve usability, there
is another set of types and functions called \<^emph>\<open>Marlowe Extended\<close> that compile to core.
\<close>
text \<open>In the first version of the extended language, the only modification to the DSL is the addition
 of template parameters. These allows an initial form of contract re-utilization, allowing to instantiate
the same contract with different \<^term>\<open>Value\<close>s and \<^term>\<open>Timeout\<close>s. For the moment, the extended
 language is not formalized in this specification but it will be added in the future.
\<close>

section \<open>Specification generation and nomenclature \label{sec:generation-nomenclature}\<close>

text \<open>
The Marlowe specification is formalized using the proof assistant Isabelle\<^footnote>\<open>\<^url>\<open>https://isabelle.in.tum.de/\<close>\<close>.
The code is written in a literate programming style and this document is generated from the proofs.
This improves code documentation and lowers the probability of stale information.\<close>

text \<open>
As a drawback, the code/doc organization is more rigid. Isabelle requires us to define code in a
bottom-up approach, having to define first the dependencies and later the more complex structures.
\<close>

text \<open>The notation is closer to a mathematical formula than a functional programming language. There are
some configurations in the \<^emph>\<open>SpecificationLatexSugar\<close> theory file that help making the output be closer to code.
\<close>


(*<*)
end
(*>*)
