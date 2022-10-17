
chapter "Code exports"

text \<open>This theory contains the necessary code to export a version of the Marlowe Semantics in Haskell.
\<close>

text \<open>We start by importing the theories we want to export and a translation theory. The theory \<^term>\<open>Code_Target_Numeral\<close>
 translates the default representation of numbers (which is suitable for logic reasoning) into a more performant representation.\<close>

theory CodeExports

imports
  Core.Semantics
  Examples.Swap
  "HOL-Library.Code_Target_Numeral"
  HOL.String

begin

text \<open>We provide some Serialization options to use Haskell native \<^term>\<open>String\<close> instead of our logical
represenation of \<^term>\<open>ByteString\<close>\<close>

code_printing
  \<comment> \<open>The first command tells the serializer to use Haskell \<close>
  \<comment> \<open>native \<^term>\<open>String\<close> instead of our logical ByteString\<close>
  type_constructor ByteString
      \<rightharpoonup> (Haskell) "String"
  \<comment> \<open>The next three commands tells the serializer to use the operators provided by\<close>
  \<comment> \<open>the Ord instance instead of the ones that work with the logical representation\<close>
  | constant "less_eq_BS"
      \<rightharpoonup> (Haskell) infix 4 "<="
  | constant "less_BS"
      \<rightharpoonup> (Haskell) infix 4 "<"
  | constant "HOL.equal :: ByteString \<Rightarrow> ByteString \<Rightarrow> bool"
      \<rightharpoonup> (Haskell) infix 4 "=="
  \<comment> \<open>The next command tells the serializer to implode the logical Isabelle string\<close>
  \<comment> \<open>into Haskell string. Because this is a textual rewrite, we need to force the\<close>
  \<comment> \<open>generation of String.implode\<close>
  | constant "BS :: string \<Rightarrow> ByteString"
      \<rightharpoonup> (Haskell) "Stringa.implode"


text \<open>With a \<^bold>\<open>code\_identifier\<close> we hint what the name of the module should be.\<close>

code_identifier
  code_module Swap \<rightharpoonup> (Haskell) Examples.Swap


text \<open>We export all the constants in one statement, because they don't add up, if you export two times,
the second export will overwrite the first one.\<close>

export_code
  \<comment> \<open>With the following exports, we declare that we want to have all the important semantic functions.
     Ideally, just with this we would have everything we need, but we need to force some exports.
    \<close>
  evalValue
  evalObservation
  reductionLoop
  reduceContractUntilQuiescent
  applyAllInputs
  playTrace
  computeTransaction

  \<comment> \<open> Export examples to be used as oracle specificaiton tests\<close>
  swapExample
  happyPathTransactions
  happyPathPayments

  \<comment> \<open>Force the export of string implode (works together with the BS code\_printing hint) \<close>
  String.implode

  \<comment> \<open> Force export of State record selectors\<close>
  txOutContract
  txOutWarnings
  txOutPayments
  txOutState

  \<comment> \<open>Force export of Arith.Int constructor\<close>
  int_of_integer

  \<comment> \<open>Force export of TransactionOutput constructors\<close>
  TransactionOutput

  \<comment> \<open>Force export of TransactionWarning constructors\<close>
  TransactionNonPositiveDeposit

  \<comment> \<open>Force export of TransactionError constructors\<close>
  TEAmbiguousTimeIntervalError

  \<comment> \<open>Force export of Payment constructor\<close>
  Payment

  \<comment> \<open>Force the export of the transaction record\<close>
  Transaction_ext

  \<comment> \<open>Force the export on some equality functions (sadly it does not force the Eq instance)\<close>
  equal_TransactionWarning_inst.equal_TransactionWarning
  equal_Payment_inst.equal_Payment
  equal_Value_inst.equal_Value
  equal_Observation_inst.equal_Observation


  in Haskell (string_classes)

(*
   With these I'm trying to force the output of the Contract Eq instance, but is not working
  "HOL.equal :: Contract \<Rightarrow> Contract \<Rightarrow> bool"
  equal_Contract_inst.equal_Contract

*)
(*<*)
end
(*>*)