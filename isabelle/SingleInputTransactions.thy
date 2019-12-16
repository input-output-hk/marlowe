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
  "applyAllLoop env sta cont [] a b = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env nsta ncont [] c d = ApplyAllSuccess c d nsta ncont"
  apply (simp only:applyAllLoop.simps[of env sta cont])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  using reduceContractUntilQuiescentIdempotent apply auto[1]
  by simp

lemma applyAllLoopJustAppendsWarningsAndEffects :
  "applyAllLoop env st c list (wa @ wt) (ef @ et) = ApplyAllSuccess (wa @ nwa) (ef @ nef) fsta fcont \<Longrightarrow>
   applyAllLoop env st c list (wa2 @ wt) (ef2 @ et) = ApplyAllSuccess (wa2 @ nwa) (ef2 @ nef) fsta fcont"
  apply (induction list arbitrary: env st c wa wt ef et wa2 ef2 nwa nef)
  subgoal for env st c wa wt ef et wa2 ef2 nwa nef
    apply (simp only:applyAllLoop.simps[of env st c])
    apply (cases "reduceContractUntilQuiescent env st c")
    by simp_all
  subgoal for head tail env st c wa wt ef et wa2 ef2 nwa nef
    apply (simp only:applyAllLoop.simps[of env st c "(head # tail)"])
    apply (cases "reduceContractUntilQuiescent env st c")
    subgoal for tempWa tempEf tempState tempContract
      apply (simp only:ReduceResult.case)
      apply (subst list.case(2)[of _ _ head tail])
      apply (subst (asm) list.case(2)[of _ _ head tail])
      apply (cases "applyInput env tempState head tempContract")
      apply (metis ApplyResult.simps(4) append.assoc)
      by simp
    by simp
  done

lemma applyLoopIdempotent_base_case :
  "applyAllLoop env sta cont [] twa tef = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env nsta ncont t [] [] = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
   applyAllLoop env sta cont t twa tef = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
  apply (simp only:applyAllLoop.simps[of env sta cont])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  apply (simp only:ReduceResult.case list.case)
  apply (simp only:applyAllLoop.simps[of env nsta ncont])
  apply (cases "reduceContractUntilQuiescent env nsta ncont")
  apply (simp only:ReduceResult.case list.case)
  apply (cases t)
  apply (simp only:list.case)
  using reduceContractUntilQuiescentIdempotent apply auto[1]
  apply (simp only:list.case)
  subgoal for x11 x12 x13 x14 x11a x12a x13a x14a a list
    apply (cases "applyInput env x13a a x14a")
    apply (cases "applyInput env x13 a x14")
    apply (simp only:ApplyResult.case)
    apply (smt ApplyAllResult.inject ApplyResult.inject ReduceResult.inject append.right_neutral append_assoc applyAllLoopJustAppendsWarningsAndEffects convertReduceWarnings.simps(1) reduceContractUntilQuiescentIdempotent self_append_conv2)
    using reduceContractUntilQuiescentIdempotent apply auto[1]
    by simp
   apply simp
  by simp

lemma applyLoopIdempotent :
  "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env nsta ncont t [] [] = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
  apply (simp only:applyAllLoop.simps[of env sta cont])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  apply (simp only:ReduceResult.case Let_def list.case)
  subgoal for x11 x12 x13 x14
    apply (cases "applyInput env x13 h x14")
    subgoal for x11a x12a x13a
      using applyLoopIdempotent_base_case by auto
    by simp
  by simp

lemma applyAllIterative :
  "applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllInputs env nsta ncont t = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
   applyAllInputs env sta cont (h#t) = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
  apply (simp only:applyAllInputs.simps)
  using applyLoopIdempotent by blast

end