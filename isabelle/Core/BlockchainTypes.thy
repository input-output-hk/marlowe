(*<*)
\<comment> \<open>This module defines the types we abstract from blockchain specific implementation\<close>
theory BlockchainTypes
imports Main Util.ByteString
begin
(*>*)

section \<open>Blockchain agnostic \label{sec:blockchain-agnostic}\<close>

text \<open>
Marlowe is currently implemented on the Cardano blockchain, but it is designed to be blockchain agnostic.
\<close>

text \<open>
Programs written in languages like Java and Python can be run on different architectures, like amd64 or arm64, because they have
 interpreters and runtimes for them. In the same way, the Marlowe interpreter could be implemented to run on other blockchains,
 like Ethereum, Solana for example.
\<close>

text \<open>
We make the following assumptions on the underlying blockchain that allow Marlowe Semantics to serve
as a common abstraction:
\<close>

text \<open>
In order to define the different \<^term>\<open>Token\<close>s that are used as currency in the participants accounts
\secref{sec:internal-accounts}, deposits, and payments,
 we need to be able to express a \<^term>\<open>TokenName\<close> and \<^term>\<open>CurrencySymbol\<close>.
\<close>
type_synonym TokenName = ByteString
type_synonym CurrencySymbol = ByteString


text \<open>To define a fixed participant in the contract \secref{sec:participants-roles-and-addresses}
and to make payouts to them, we need to express an \<^term>\<open>Address\<close>.\<close>
type_synonym Address = ByteString

text \<open>In the context of this specification, these \<^term>\<open>ByteString\<close> types are opaque, and we don't enforce
a particular encoding or format, only that they can be sorted \secref{sec:bytestring}.\<close>

text \<open>The \<^term>\<open>Timeout\<close>s that prevent us from waiting forever for external \<^term>\<open>Input\<close>s are represented
by the number of milliseconds from the Unix Epoch \<^footnote>\<open>January 1st, 1970 at 00:00:00 UTC\<close>. \<close>
type_synonym POSIXTime = int

type_synonym Timeout = POSIXTime

text \<open>The \<^term>\<open>TimeInterval\<close> that defines the validity of a transaction is a tuple of exclusive start
and end time. \<close>
\<comment> \<open>TODO: Check if exclusive or inclusive\<close>
type_synonym TimeInterval = "POSIXTime \<times> POSIXTime"

(*<*)
end
(*>*)
