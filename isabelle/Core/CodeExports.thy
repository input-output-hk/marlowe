(*
   This theory contains the code necesary to export a runnable version of the Marlowe Semantics
   in Haskell
*)
theory CodeExports

imports Semantics

begin

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