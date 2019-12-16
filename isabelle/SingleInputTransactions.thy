theory SingleInputTransactions

imports Main Semantics

begin

fun inputsToTransactions :: "SlotInterval \<Rightarrow> Input list \<Rightarrow> Transaction list" where
"inputsToTransactions si Nil = Cons \<lparr> interval = si
                                    , inputs = Nil \<rparr> Nil" |
"inputsToTransactions si (Cons inp1 Nil) = Cons \<lparr> interval = si
                                                 , inputs = Cons inp1 Nil \<rparr> Nil" |
"inputsToTransactions si (Cons inp1 rest) = Cons \<lparr> interval = si
                                                 , inputs = Cons inp1 Nil \<rparr>
                                                 (inputsToTransactions si rest)"

fun traceListToSingleInput :: "Transaction list \<Rightarrow> Transaction list" where
"traceListToSingleInput Nil = Nil" |
"traceListToSingleInput (Cons \<lparr> interval = si
                              , inputs = inps \<rparr> rest) = inputsToTransactions si inps @ (traceListToSingleInput rest)"

lemma reductionLoopIdempotent :
  "reductionLoop env state contract wa pa = ContractQuiescent nwa npa nsta ncont \<Longrightarrow>
   reductionLoop env nsta ncont [] [] = ContractQuiescent [] [] nsta ncont"  
  apply (induction env state contract wa pa rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (cases "reduceContractStep env state contract")
    apply (cases "reduceContractStep env nsta ncont")
    apply (simp add:Let_def)
    apply simp
    apply simp
    apply metis
    apply simp
    by simp
  done

lemma reduceContractUntilQuiescentIdempotent :           
  "reduceContractUntilQuiescent env state contract = ContractQuiescent wa pa nsta ncont \<Longrightarrow>
   reduceContractUntilQuiescent env nsta ncont = ContractQuiescent [] [] nsta ncont"
  apply (simp only:reduceContractUntilQuiescent.simps)
  using reductionLoopIdempotent by blast  

lemma applyAllLoopEmptyIdempotent :
  "applyAllLoop env sta cont [] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env nsta ncont [] [] [] = ApplyAllSuccess [] [] nsta ncont"
  apply (simp only:applyAllLoop.simps[of env sta cont])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  using reduceContractUntilQuiescentIdempotent apply auto[1]
  by simp

end