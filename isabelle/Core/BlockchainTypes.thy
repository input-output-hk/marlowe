(*<*)
\<comment> \<open>This module defines the types we abstract from BlockChain specific implementation\<close>
theory BlockchainTypes
imports Main Util.Serialisation
begin
(*>*)

section \<open>Blockchain agnostic \label{sec:blockchain-agnostic}\<close>

text \<open>
Marlowe is currently implemented on the Cardano Blockchain, but is designed to be Blockchain agnostic. The same way that
modern languages like C++ and Java have compilers that target intel/ARM, Marlowe could be implemented
in Ethereum and other blockchain platforms.
\<close>

text \<open>
There are some assumptions we make on the underlying Blockchain that allows Marlowe Semantics to serve
as a common abstraction:
\<close>

text \<open>
In order to define the different \<^term>\<open>Token\<close>s that are used as currency in the participants accounts
\secref{sec:internal-accounts},
 we need to be able to express a \<^term>\<open>TokenName\<close> and \<^term>\<open>CurrencySymbol\<close>.
\<close>
type_synonym TokenName = ByteString
type_synonym CurrencySymbol = ByteString


text \<open>To define a fixed participant in the contract \secref{sec:participants-roles-and-addresses}
and to make payouts to them, we need to express an \<^term>\<open>Address\<close>.\<close>
type_synonym Address = ByteString

text \<open>In the context of this specification these string types are opaque, and we don't enforce
a particular encoding or format.\<close>

text \<open>The \<^term>\<open>Timeout\<close>s that prevent us from waiting forever for external \<^term>\<open>Input\<close>s are represented
by the number of milliseconds from the Unix Epoch \<^footnote>\<open>January 1st, 1970 at 00:00:00 UTC\<close>. \<close>
type_synonym POSIXTime = int

type_synonym Timeout = POSIXTime

text \<open>The \<^term>\<open>TimeInterval\<close> that define the validity of a transaction is a tuple of exclusive start 
and end time. \<close>
\<comment> \<open>TODO: Check if exclusive or inclusive\<close>
type_synonym TimeInterval = "POSIXTime \<times> POSIXTime"

(*<*)
end
(*>*)