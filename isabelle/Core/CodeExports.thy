(*
   This theory contains the code necesary to export a runnable version of the Marlowe Semantics
   in Haskell
*)
theory CodeExports

imports Semantics "HOL-Library.Code_Target_Numeral"

begin

code_printing
  type_constructor ByteString \<rightharpoonup> (Haskell) "String"
  | constant "less_eq_BS" \<rightharpoonup> (Haskell) infix 4 "<=" 
  | constant "HOL.equal :: ByteString \<Rightarrow> ByteString \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="

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

  in Haskell 

(*
   With these I'm trying to force the output of the Contract Eq instance, but is not working
  "HOL.equal :: Contract \<Rightarrow> Contract \<Rightarrow> bool"
  equal_Contract_inst.equal_Contract

*)
end