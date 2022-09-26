(*
   This theory contains the code necesary to export a runnable version of the Marlowe Semantics
   in Haskell
*)
theory CodeExports

imports Semantics "HOL-Library.Code_Target_Numeral" HOL.String

begin

code_printing
  type_constructor ByteString \<rightharpoonup> (Haskell) "String"
  | constant "less_eq_BS" \<rightharpoonup> (Haskell) infix 4 "<=" 
  | constant "HOL.equal :: ByteString \<Rightarrow> ByteString \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="

(*
definition member :: \<Zprime>a list \<Rightarrow> \<Zprime>a \<Rightarrow> bool where
[code_abbrev]: member xs x \<leftarrow>\<rightarrow> x \<in> set xs
*)

(*
lemma [code abstract]:
  "integer_of_nat (nat_of_integer k) = max 0 k"
  by transfer auto
*)

(*lemma [code abstype]:
  "ByteString == String.literal"*)

(*
lift_definition btos :: "ByteString \<Rightarrow> string"
  is "map louqeascii_of"
  oops
*)

export_code
  evalValue
  evalObservation
  reductionLoop
  reduceContractUntilQuiescent
  applyAllInputs
  playTrace
  computeTransaction
  in Haskell
end