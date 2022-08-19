(*<*)
theory Specification
  imports Main

begin                                                     
(*>*)

chapter \<open>Marlowe\<close>

section \<open>Introduction\<close>

text \<open>

Marlowe is a special purpose or domain-specific language (DSL) that is designed to be usable by
someone who is expert in the field of financial contracts, somewhat lessening the need for
programming skills.

Marlowe is modelled on special-purpose financial contract languages popularised in the last decade
or so by academics and enterprises such as LexiFi, which provides contract software in the financial
sector. In developing Marlowe, we have adapted these languages to work on blockchain. Marlowe was
implemented on the Cardano blockchain, but is designed to be blockchain agnostic. The same way that
modern languages like C++ and Java has compilers that target intel/ARM, Marlowe could be implemented
in Ethereum and other blockchain platforms.

Where we differ from non-blockchain approaches is in how we make sure that the contract is followed.
This means not only that the instructions of the contract are not disobeyed---``nothing bad
---happens'' but also that the participants don't walk away early, leaving money locked up in the
contract forever: ``good things actually happen''. We do this using timeouts.

A contract can ask a participant to make a deposit of some funds, but obviously the contract cannot
actually force a participant to make a deposit. Instead, the contract can wait for a period of time
for the participant to commit to the contract: when that period of time expires, the contract moves
on to follow some alternative instructions. This prevents a participant stopping a contract by not
taking part, thus making sure that ``things happen''.

All the constructs of Marlowe that require user participation---including user deposits and user
choices---are protected by timeouts. Because of this, it is easy to see that the commitment made by
a participant to a contract is finite: we can predict when the contract will have nothing left to
do---when it can be closed. At this point any unspent funds left in the contract are refunded to
participants, and the contract stops, or terminates. So, any funds put into the contract by a
participant can't be locked up forever: at this point the commitment effectively ends.

What is more, it is easy for us to read off from the contract when it will terminate, we call this
the lifetime of the contract: all participants will therefore be able to find out this lifetime
before taking part in any contract,

In our model, a running contract cannot force a deposit or a choice to happen: all it can do is to
request a deposit or choice from a participant. In other words, for these actions it cannot ``push'',
but it can ``pull''. On the other hand, it can make payments automatically, so some aspects of a
Marlowe contract can ``push'' to make some things happen, e.g. ensuring that a payment is made to a
participant by constructing an appropriate transaction output. FIXME: Does this paragraph make clear
that the contracts aren't continuously running on the blockchain, but instead need to be advanced
forward by participants submitting transactions?

\<close>

text \<open>

The first chapter of the document provides an overview of the Marlowe DSL and semantics. The
following chapter defines the language and semantics in detail. The third, final chapter presents
proofs that guarantee that Marlowe contracts possess properties desirable for financial agreements.

\<close>

section \<open>The Marlowe Model\<close>

text \<open>

Marlowe is designed to support the execution of financial agreements on blockchain (initially
Cardano), and specifically to work on Cardano. Contracts are built by putting together a small
number of constructs that can be combined to describe many different kinds of financial contract.

\<close>

subsection \<open>Contracts\<close>

text \<open>

Contracts in Marlowe run on a blockchain, but need to interact with the off-chain world. The parties
to the contract, whom we also call the participants, can engage in various actions: they can be
asked to deposit money, or to make a choice between various alternatives. Notification is another
form of input that is used to tell the contract that a certain condition has been met, anybody can
do this, and it is only necessary because once a contract becomes dormant (quiescent), it cannot
``wake up'' on its own, it can only respond to inputs.

Running a contract may also produce external effects, by making payments to parties in the contract.

\<close>

subsection \<open>Participants, roles, and public key\<close>

text \<open>

We should separate the notions of participant, role, and public keys in a Marlowe contract. A
participant (or party) in the contract can be represented by either a role or a public key (public
keys will eventually be replaced by addresses).

Roles are represented by tokens and they are distributed to addresses at the time a contract is
deployed to the blockchain. After that, whoever has the token representing a role is able to carry
out the actions assigned to that role, and receive the payments that are issued to that role.

Public key parties, are represented by the hash of a public key (or eventually an addresses). Using
public keys to represent parties is simpler because it does not require handling tokens, but they
cannot be traded, because once you know the private key for a given public key you cannot prove you
have forgotten it.

\<close>

subsection \<open>Accounts\<close>

text \<open>

The Marlowe model allows for a contract to store assets. All parties that participate in the
contract implicitly own an account with their name. All assets stored in the contract must be in
an internal account for one of the parties; this way, when the contract is closed, all assets that
remain in the contract belong to someone, and so can be refunded to their respective owners. These
accounts are local: they only exist within the contract and for the duration of the execution of the
contract, and during that time they are only accessible from within the contract. During the course
of the contract payments may be made into accounts (as deposits), between accounts (as internal
 transfers), or out from accounts (as external payments).

\<close>

subsection \<open>Steps and states\<close>

text \<open>

Marlowe contracts describe a series of steps, typically by describing the first step, together with
another (sub-) contract that describes what to do next. For example, the contract
@{term "Pay a p t v c"} says ``make a payment of value @{term v} of token @{term t} to the party
@{term p} from the account @{term a}, and then follow the contract @{term c}''. We call @{term c} the
continuation of the contract.

In executing a contract, we need to keep track of the current contract (that is, the remaining part
of the contract): after making a step in the example above, the current contract is the
continuation, @{term c}. We also have to keep track of some other information, such as how much is
held in each account: we call this information the state, and this potentially changes at each step,
too. A step can also see an action taking place, such as money being deposited, or an effect being
produced, e.g. a payment.

\<close>

(*<*)
end
(*>*)
