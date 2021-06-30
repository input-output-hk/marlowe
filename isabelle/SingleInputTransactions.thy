theory SingleInputTransactions

imports Main Semantics

begin

declare [[ smt_timeout = 300 ]]

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
   applyAllLoop env sta cont t twa tef = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont \<Longrightarrow>
   applyAllLoop env nsta ncont t [] [] = ApplyAllSuccess nwa npa fsta fcont"
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
    using reduceContractUntilQuiescentIdempotent by auto
  using reduceContractUntilQuiescentIdempotent apply auto[1]
  by auto

lemma applyLoopIdempotent :
  "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont \<Longrightarrow>
   applyAllLoop env nsta ncont t [] [] = ApplyAllSuccess nwa npa fsta fcont"
  apply (simp only:applyAllLoop.simps[of env sta cont])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  apply (simp only:ReduceResult.case Let_def list.case)
  subgoal for x11 x12 x13 x14
    apply (cases "applyInput env x13 h x14")
    subgoal for x11a x12a x13a
      using applyLoopIdempotent_base_case by auto
    by simp
  by simp
 
 lemma applyLoopIdempotent_base_case2 :
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
 
 lemma applyLoopIdempotent2 :
   "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env nsta ncont t [] [] = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
   apply (simp only:applyAllLoop.simps[of env sta cont])
   apply (cases "reduceContractUntilQuiescent env sta cont")
   apply (simp only:ReduceResult.case Let_def list.case)
   subgoal for x11 x12 x13 x14
     apply (cases "applyInput env x13 h x14")
     subgoal for x11a x12a x13a
       using applyLoopIdempotent_base_case2 by auto
     by simp
   by simp


lemma applyAllIterative :
  "applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllInputs env sta cont (h#t) = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont \<Longrightarrow>
   applyAllInputs env nsta ncont t = ApplyAllSuccess nwa npa fsta fcont"
  apply (simp only:applyAllInputs.simps)
  using applyLoopIdempotent by blast

lemma applyAllIterative2 :
  "applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
  applyAllInputs env nsta ncont t = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
  applyAllInputs env sta cont (h#t) = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
  apply (simp only:applyAllInputs.simps)
  using applyLoopIdempotent2 by blast

lemma applyAllInputsPrefix1:
  "applyAllLoop env sta cont l iwa ipa = ApplyAllSuccess fwa fpa nsta ncont \<Longrightarrow>
   \<exists>nwa. fwa = iwa @ nwa"
  apply (induction env sta cont l iwa ipa arbitrary:fwa fpa nsta ncont rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments fwa fpa nsta ncont
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for reduceWarns reducePays reduceState reduceCont
      apply (simp only:ReduceResult.case)
      apply (cases inputs)
      apply (simp only:list.case)
      apply blast
      subgoal for h t
        apply (simp only:list.case)
        apply (cases "applyInput env reduceState h reduceCont")
        subgoal for applyWarn applyState applyCont
        apply (simp only:ApplyResult.case)
          using append.assoc by blast
        by simp
      done
    by simp
  done

lemma applyAllInputsPrefix2:
  "applyAllLoop env sta cont l iwa ipa = ApplyAllSuccess fwa fpa nsta ncont \<Longrightarrow>
   \<exists>npa. fpa = ipa @ npa"
  apply (induction env sta cont l iwa ipa arbitrary:fwa fpa nsta ncont rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments fwa fpa nsta ncont
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for reduceWarns reducePays reduceState reduceCont
      apply (simp only:ReduceResult.case)
      apply (cases inputs)
      apply (simp only:list.case)
      apply blast
      subgoal for h t
        apply (simp only:list.case)
        apply (cases "applyInput env reduceState h reduceCont")
        subgoal for applyWarn applyState applyCont
        apply (simp only:ApplyResult.case)
          using append.assoc by blast
        by simp
      done
    by simp
  done

lemma beforeApplyAllLoopIsUseless:
  "iwa @ convertReduceWarnings x11 = wa \<Longrightarrow>
   ipa @ x12 = pa \<Longrightarrow>
   applyAllLoop env applyState applyCont t iwa ipa = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   reduceContractUntilQuiescent env applyState applyCont = ContractQuiescent x11 x12 nsta ncont \<Longrightarrow>
   ApplyAllSuccess fwa fpa fsta fcont = applyAllLoop env nsta ncont t wa pa"
  apply (simp only:applyAllLoop.simps[of env applyState])
  apply (simp only:applyAllLoop.simps[of env nsta])
  apply (cases "reduceContractUntilQuiescent env nsta ncont")
  subgoal for x11a x12a x13 x14
  apply (simp only:ReduceResult.case)
  apply (cases t)
    apply (simp only:list.case)
    using reduceContractUntilQuiescentIdempotent apply auto[1]
    subgoal for h t
      apply (simp only:list.case)
      apply (simp only:reduceContractUntilQuiescentIdempotent)
      apply (cases "applyInput env nsta h ncont")
      apply force
      by simp
    done
  using reduceContractUntilQuiescentIdempotent by auto

lemma applyAllInputsPrefix_aux:
  "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   (\<exists> twa x11 x12 applyState applyCont reducePays reduceState reduceCont.
    twa @ convertReduceWarnings x11 = wa \<and>
    reducePays @ x12 = pa \<and>
    applyAllLoop env applyState applyCont t twa reducePays = ApplyAllSuccess fwa fpa fsta fcont \<and>
    reduceContractUntilQuiescent env applyState applyCont = ContractQuiescent x11 x12 nsta ncont)"
    apply (subst (asm) applyAllLoop.simps[of env sta cont "[h]"])
    apply (cases "reduceContractUntilQuiescent env sta cont")
    subgoal for reduceWarns reducePays reduceState reduceCont
      apply (simp only:ReduceResult.case)
      apply (simp only:list.case)
      apply (cases "applyInput env reduceState h reduceCont")
      subgoal for applyWarn applyState applyCont
        apply (simp only:ApplyResult.case)
    apply (subst (asm) applyAllLoop.simps[of env sta cont "(h # t)"])
    apply (cases "reduceContractUntilQuiescent env sta cont")
    subgoal for reduceWarns2 reducePays2 reduceState2 reduceCont2
      apply (simp only:ReduceResult.case)
      apply (simp only:list.case)
      apply (cases "applyInput env reduceState h reduceCont")
      subgoal for applyWarn2 applyState2 applyCont2
        apply (simp only:ApplyResult.case)
        apply (subst (asm) applyAllLoop.simps[of env applyState applyCont "[]"])
        apply (cases "reduceContractUntilQuiescent env applyState applyCont")
        subgoal for x11 x12 x13 x14
          apply (simp only:ReduceResult.case list.case)
          apply (simp del:applyAllLoop.simps reduceContractUntilQuiescent.simps applyInput.simps)
          using append_assoc by blast
        by simp
      by simp
    by simp
  by simp
  by simp

lemma applyAllInputsPrefix1_aux2:
  "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   \<exists>nwa. fwa = wa @ nwa"
  apply (frule applyAllInputsPrefix_aux[of env sta cont h wa pa nsta ncont t fwa fpa fsta fcont])
  apply simp
  by (metis applyAllInputsPrefix1 beforeApplyAllLoopIsUseless)

lemma applyAllPrefix1:
  "applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllInputs env sta cont (h#t) = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   (\<exists> nwa. fwa = wa @ nwa)"
  apply (simp only:applyAllInputs.simps)
  by (simp add: applyAllInputsPrefix1_aux2)

lemma applyAllInputsPrefix2_aux2:
  "applyAllLoop env sta cont [h] [] [] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllLoop env sta cont (h # t) [] [] = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   \<exists>npa. fpa = pa @ npa"
  apply (frule applyAllInputsPrefix_aux[of env sta cont h wa pa nsta ncont t fwa fpa fsta fcont])
  apply simp
  by (metis applyAllInputsPrefix2 beforeApplyAllLoopIsUseless)

lemma applyAllPrefix2:
  "applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa nsta ncont \<Longrightarrow>
   applyAllInputs env sta cont (h#t) = ApplyAllSuccess fwa fpa fsta fcont \<Longrightarrow>
   (\<exists> npa. fpa = pa @ npa)"
  by (simp add: applyAllInputsPrefix2_aux2)

lemma computeAllPrefix1:
  "computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> sta cont =
    TransactionOutput \<lparr>txOutWarnings = wa, txOutPayments = pa, txOutState = nsta, txOutContract = ncont\<rparr> \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = head # tail\<rparr> sta cont =
    TransactionOutput \<lparr>txOutWarnings = fwa, txOutPayments = fpa, txOutState = fsta, txOutContract = fcont\<rparr> \<Longrightarrow>
   (\<exists> nwa. fwa = wa @ nwa)"
  apply (simp only:computeTransaction.simps)
  apply (cases "fixInterval (interval \<lparr>interval = interv, inputs = [head]\<rparr>) sta")
  subgoal for env fixSta
    apply (cases "applyAllInputs env fixSta cont [head]")
    subgoal for warnings payments newState conta
      apply (cases "applyAllInputs env fixSta cont (head # tail)")
      subgoal for warnings2 payments2 newState2 conta2
        apply (simp del:applyAllInputs.simps fixInterval.simps)
        by (metis TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllPrefix1)
      by simp_all
    by simp_all
  by simp

lemma computeAllPrefix2:
  "computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> sta cont =
    TransactionOutput \<lparr>txOutWarnings = wa, txOutPayments = pa, txOutState = nsta, txOutContract = ncont\<rparr> \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = head # tail\<rparr> sta cont =
    TransactionOutput \<lparr>txOutWarnings = fwa, txOutPayments = fpa, txOutState = fsta, txOutContract = fcont\<rparr> \<Longrightarrow>
   (\<exists> npa. fpa = pa @ npa)"
  apply (simp only:computeTransaction.simps)
  apply (cases "fixInterval (interval \<lparr>interval = interv, inputs = [head]\<rparr>) sta")
  subgoal for env fixSta
    apply (cases "applyAllInputs env fixSta cont [head]")
    subgoal for warnings payments newState conta
      apply (cases "applyAllInputs env fixSta cont (head # tail)")
      subgoal for warnings2 payments2 newState2 conta2
        apply (simp del:applyAllInputs.simps fixInterval.simps)
        by (metis TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllPrefix2)
      by simp_all
    by simp_all
  by simp

lemma fixIntervalOnlySummary :
  "minSlot state = low \<Longrightarrow> low \<le> high \<Longrightarrow>
   IntervalTrimmed \<lparr> slotInterval = (low, high) \<rparr> state = fixInterval (low, high) state"
  by simp

lemma fixIntervalOnlySummary2 :
  "fixInterval (low, high) state = IntervalTrimmed \<lparr> slotInterval = (nlow, nhigh) \<rparr> nstate \<Longrightarrow>
   nlow = minSlot nstate \<and> low \<le> high"
  apply (cases "high < low")
  apply simp
  apply (cases "high < minSlot state")
  by (auto simp add:Let_def)

lemma fixIntervalChecksInterval :
  "fixInterval inte sta1 = IntervalTrimmed \<lparr>slotInterval = (low, high)\<rparr> sta2 \<Longrightarrow>
   low \<le> high"
  apply (cases inte)
  apply (simp add:Let_def)
  subgoal for low1 high1
    apply (cases "high1 < low1")
    apply simp_all
    apply (cases "high1 < minSlot sta1")
    apply simp_all
    by linarith
  done

lemma fixIntervalIdempotentOnInterval :
  "minSlot sta4 = minSlot sta2 \<Longrightarrow>
   fixInterval (low1, high1) sta1 = IntervalTrimmed \<lparr>slotInterval = (low, high)\<rparr> sta2 \<Longrightarrow>
   fixInterval (low1, high1) sta4 = fixInterval (low, high) sta4"
  apply (cases "high1 < low1")
  apply simp
  apply (cases "high1 < minSlot sta1")
  by (auto simp add:Let_def)

lemma reductionContractStep_preserves_minSlot :
  "reduceContractStep env state contract = Reduced wa ef sta2 cont2 \<Longrightarrow>
   minSlot state = minSlot sta2"
  apply (cases contract)
  apply (auto split:option.splits simp add:Let_def)
  subgoal for x21 x22 x23 x24 x25
  apply (cases "evalValue env state x24 \<le> 0")
    apply simp
    apply (auto split:prod.splits simp add:Let_def)
    done
  apply (auto split:prod.splits simp add:Let_def)
  by (metis ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject)

lemma reductionLoop_preserves_minSlot :
  "reductionLoop env sta con wa pa = ContractQuiescent reduceWarns pays sta2 con2 \<Longrightarrow> minSlot sta = minSlot sta2"
  apply (induction env sta con wa pa arbitrary:reduceWarns pays sta2 con2 rule:reductionLoop.induct)
  subgoal for env state contract warnings payments reduceWarns pays sta2 con2
    apply (simp only:reductionLoop.simps[of env state contract warnings payments])
    apply (auto split:ReduceStepResult.splits simp del:reductionLoop.simps)
    using reductionContractStep_preserves_minSlot by auto
  done

lemma reduceContractUntilQuiescent_preserves_minSlot :
  "reduceContractUntilQuiescent env sta con = ContractQuiescent reduceWarns pays sta2 con2 \<Longrightarrow> minSlot sta = minSlot sta2"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (simp add: reductionLoop_preserves_minSlot)

lemma applyCases_preserves_minSlot :
  "applyCases env curState head x41 = Applied applyWarn newState newCont \<Longrightarrow>
   minSlot curState = minSlot newState"
  apply (induction env curState head x41 arbitrary:applyWarn newCont newState rule:applyCases.induct)
  subgoal for env state accId1 party1 tok1 amount accId2 party2 tok2 val cont rest applyWarn newCont newState
    apply (cases "accId1 = accId2 \<and> party1 = party2 \<and> tok1 = tok2 \<and> amount = evalValue env state val")
    by auto
  subgoal for env state choId1 choice choId2 bounds cont rest applyWarn newCont newState
    apply (cases "choId1 = choId2 \<and> inBounds choice bounds")
    by auto
  subgoal for env state obs cont rest applyWarn newCont newState
    apply (cases "evalObservation env state obs")
    by auto
  by auto

lemma applyInput_preserves_minSlot :
  "applyInput env curState head cont = Applied applyWarn newState newCont \<Longrightarrow> minSlot curState = minSlot newState"
  apply (cases cont)
  by (auto simp add:applyCases_preserves_minSlot)

lemma applyAllLoop_preserves_minSlot :
  "applyAllLoop env sta con inp wa pa = ApplyAllSuccess wa2 pa2 sta2 con2 \<Longrightarrow> minSlot sta = minSlot sta2"
  apply (induction inp arbitrary:env sta con wa pa wa2 pa2 sta2 con2)
  subgoal for env sta con wa pa wa2 pa2 sta2 con2
    apply (simp only:applyAllLoop.simps[of env sta con "[]" wa pa])
    apply (cases "reduceContractUntilQuiescent env sta con")
    subgoal for reduceWarns pays curState cont
      apply (simp del:reduceContractUntilQuiescent.simps)
      using reduceContractUntilQuiescent_preserves_minSlot by blast
      apply (simp del:reduceContractUntilQuiescent.simps)
    done
  subgoal for head tail env sta con wa pa wa2 pa2 sta2 con2
      apply (simp only:applyAllLoop.simps[of env sta con "(head # tail)" wa pa])
      apply (cases "reduceContractUntilQuiescent env sta con")
      subgoal for reduceWarns pays curState cont
        apply (cases "applyInput env curState head cont")
        subgoal for applyWarn newState newCont
          by (simp add: applyInput_preserves_minSlot reduceContractUntilQuiescent_preserves_minSlot)
        by simp
      by simp
    done

lemma applyAllInputs_preserves_minSlot :
  "applyAllInputs env sta con inp = ApplyAllSuccess wa2 pa2 sta2 con2 \<Longrightarrow>
   minSlot sta = minSlot sta2"
  apply (simp only:applyAllInputs.simps)
  using applyAllLoop_preserves_minSlot by blast

lemma applyAllInputs_preserves_minSlot_rev :
   "applyAllInputs env sta con inp = ApplyAllSuccess wa2 pa2 sta2 con2 \<Longrightarrow>
    minSlot sta2 = minSlot sta"
  by (simp add: applyAllInputs_preserves_minSlot)

lemma fixIntervalIdempotentThroughApplyAllInputs :
  "fixInterval inte sta1 = IntervalTrimmed env2 sta2 \<Longrightarrow>
   applyAllInputs env2 sta2 con3 inp1 = ApplyAllSuccess wa4 pa4 sta4 con4 \<Longrightarrow>
   fixInterval inte sta4 = IntervalTrimmed env2 sta4"
  apply (cases env2)
  subgoal for slotInterval
    apply (cases slotInterval)
    subgoal for low high
      apply (simp del:fixInterval.simps applyAllInputs.simps)
      apply (subst fixIntervalOnlySummary)
      apply (metis applyAllInputs_preserves_minSlot eq_fst_iff fixIntervalOnlySummary2)
      using fixIntervalChecksInterval apply blast
      apply (cases inte)
      subgoal for low1 high1
        using applyAllInputs_preserves_minSlot_rev fixIntervalIdempotentOnInterval by blast
      done
    done
  done
lemma fixIntervalIdempotentThroughApplyAllInputs2 :
  "fixInterval interv sta = IntervalTrimmed fIenv1 fIsta1 \<Longrightarrow>
   applyAllInputs fIenv1 fIsta1 con [head] = ApplyAllSuccess iwa ipa ista con3 \<Longrightarrow>
   fixInterval interv ista = IntervalTrimmed fIenv1 ista"
  using fixIntervalIdempotentThroughApplyAllInputs by blast

lemma smallerSize_implies_different :
  "size cont1 < size cont \<Longrightarrow> cont1 \<noteq> cont"
  by blast

lemma reductionStep_only_makes_smaller :
  "contract \<noteq> ncontract \<Longrightarrow>
   reduceContractStep env state contract = Reduced warning effect newState ncontract \<Longrightarrow> size ncontract < size contract"
  apply (cases contract)
  apply simp
  apply (cases "refundOne (accounts state)")
  apply simp
  apply (simp add: case_prod_beta)
  subgoal for accountId payee token val contract
    apply (simp add:Let_def)
    apply (cases "evalValue env state val \<le> 0")
    apply (simp only:if_True Let_def)
    apply blast
    apply (simp only:if_False Let_def)
    apply (cases "giveMoney accountId payee token (min (moneyInAccount accountId token (accounts state)) (evalValue env state val))
           (updateMoneyInAccount accountId token
             (moneyInAccount accountId token (accounts state) -
              min (moneyInAccount accountId token (accounts state)) (evalValue env state val))
             (accounts state))")
    apply simp
    done
    apply auto[1]
  subgoal for cases timeout contract
    apply simp
    apply (cases "slotInterval env")
    subgoal for low high
      apply simp
      apply (cases "high < timeout")
      apply simp_all
      apply (cases "timeout \<le> low")
      by simp_all
    done
  apply(simp add:Let_def)
  by simp

lemma reductionLoop_only_makes_smaller :
  "cont1 \<noteq> cont \<Longrightarrow>
   reductionLoop env state cont wa pa = ContractQuiescent nwa npa nsta cont1 \<Longrightarrow>
   size cont1 < size cont"
  apply (induction env state cont wa pa arbitrary:cont1 nwa npa nsta rule:reductionLoop.induct)
  subgoal for env state contract warnings payments cont1 nwa npa nsta
    apply (simp only:reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for warning effect newState ncontract
      apply (simp del:reduceContractStep.simps reductionLoop.simps)
      by (metis dual_order.strict_trans reductionStep_only_makes_smaller)
    apply simp
  by simp
  done

lemma reduceContractUntilQuiescent_only_makes_smaller :
  "cont1 \<noteq> cont \<Longrightarrow>
   reduceContractUntilQuiescent env state cont = ContractQuiescent wa pa nsta cont1 \<Longrightarrow>
   size cont1 < size cont"
  apply (simp only:reduceContractUntilQuiescent.simps)
  by (simp add: reductionLoop_only_makes_smaller)

lemma applyCases_only_makes_smaller :
  "applyCases env curState input cases = Applied applyWarn newState cont1 \<Longrightarrow>
   size cont1 < size_list size cases"
  apply (induction env curState input cases rule:applyCases.induct)
  apply auto
  apply (metis ApplyResult.inject less_SucI less_add_Suc1 trans_less_add2)
  apply (metis ApplyResult.inject less_SucI less_add_Suc1 trans_less_add2)
  apply (metis ApplyResult.inject less_SucI less_add_Suc1 trans_less_add2)
  done

lemma applyInput_only_makes_smaller :
  "cont1 \<noteq> cont \<Longrightarrow>
   applyInput env curState input cont = Applied applyWarn newState cont1 \<Longrightarrow>
   size cont1 < size cont"
  apply (cases cont)
  apply simp_all
  subgoal for cases timeout contract
    by (simp add: add.commute applyCases_only_makes_smaller less_SucI trans_less_add2)
  done

lemma applyAllLoop_only_makes_smaller :
  "cont1 \<noteq> cont \<Longrightarrow>
   applyAllLoop env sta cont c wa ef = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow> cont1 \<noteq> cont \<Longrightarrow> size cont1 < size cont"
  apply (induction env sta cont c wa ef rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    apply (simp only:ReduceResult.case)
    subgoal for wa pa nsta cont1
      apply (cases inputs)
      apply (simp only:list.case)
      apply (simp add:reduceContractUntilQuiescent_only_makes_smaller)
      subgoal for head tail
      apply (simp only:list.case)
        apply (cases "applyInput env nsta head cont1")
        subgoal for applyWarn newState cont2
          apply (simp only:ApplyResult.case)
          by (smt applyInput_only_makes_smaller le_trans less_imp_le_nat not_le reduceContractUntilQuiescent_only_makes_smaller)
        by simp
      done
    by simp
  done

lemma applyAllInputs_only_makes_smaller :
  "applyAllInputs env sta cont c = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow>
   cont1 \<noteq> cont \<Longrightarrow> size cont1 < size cont"
  apply (simp only:applyAllInputs.simps)
  using applyAllLoop_only_makes_smaller by blast

lemma applyAllLoop_longer_doesnt_grow :
  "applyAllLoop env sta cont h wa pa = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow>
   applyAllLoop env sta cont (h @ t) wa pa = ApplyAllSuccess cwa2 pa2 sta2 cont2 \<Longrightarrow> size cont2 \<le> size cont1"
  apply (induction h arbitrary: env sta cont t wa pa cwa1 pa1 sta1 cont1 cwa2 pa2 sta2 cont2)
  subgoal for env sta cont t wa pa cwa1 pa1 sta1 cont1 cwa2 pa2 sta2 cont2
  apply (subst (asm) applyAllLoop.simps)
  apply (subst (asm) applyAllLoop.simps[of env sta cont "[] @ t"])
  apply (cases "reduceContractUntilQuiescent env sta cont")   
  apply (simp only:ReduceResult.case)
  apply (simp only:list.case append_Nil)
  subgoal for wa pa nsta ncont
    apply (cases t)
    apply (simp only:list.case)
    apply blast
    apply (simp only:list.case)
    subgoal for head tail
      apply (cases "applyInput env nsta head ncont")  
      apply (simp only:ApplyResult.case)
      apply (metis ApplyAllResult.inject applyAllLoop_only_makes_smaller applyInput_only_makes_smaller less_le_trans not_le_imp_less order.asym)
      by simp
    done
  by simp
  subgoal for hh ht env sta cont t wa pa cwa1 pa1 sta1 cont1 cwa2 pa2 sta2 cont2
  apply (subst (asm) applyAllLoop.simps[of env sta cont "(hh # ht)"])
  apply (subst (asm) applyAllLoop.simps[of env sta cont "(hh # ht) @ t"])
  apply (cases "reduceContractUntilQuiescent env sta cont")
  apply (simp only:ReduceResult.case List.append.append_Cons)
  apply (simp only:list.case)
  subgoal for wa pa nsta ncont
    apply (cases "applyInput env nsta hh ncont")
    apply (simp only:ApplyResult.case)
    by simp
  by simp
  done

lemma applyAllInputs_longer_doesnt_grow :
  "applyAllInputs env sta cont h = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow>
   applyAllInputs env sta cont (h @ t) = ApplyAllSuccess cwa2 pa2 sta2 cont2 \<Longrightarrow>
   size cont2 \<le> size cont1"
  apply (simp only:applyAllInputs.simps)
  by (simp add: applyAllLoop_longer_doesnt_grow)

lemma applyAllInputs_once_modified_always_modified :
  "applyAllInputs env sta cont [h] = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow>
   cont1 \<noteq> cont \<Longrightarrow>
   applyAllInputs env sta cont (h # t) = ApplyAllSuccess cwa2 pa2 sta2 cont2 \<Longrightarrow>
   cont2 \<noteq> cont"
  apply (rule smallerSize_implies_different)
  by (metis append_Cons append_Nil applyAllInputs.simps applyAllLoop_longer_doesnt_grow applyAllLoop_only_makes_smaller not_le)

lemma computeTransactionIterative_aux :
  "fixInterval inte osta = IntervalTrimmed env sta \<Longrightarrow>
   applyAllInputs env sta cont [h] = ApplyAllSuccess wa pa tsta ncont \<Longrightarrow>
   fixInterval inte tsta = IntervalTrimmed nenv nsta \<Longrightarrow>
   applyAllInputs nenv nsta ncont t = ApplyAllSuccess nwa npa fsta fcont \<Longrightarrow>
   applyAllInputs env sta cont (h # t) = ApplyAllSuccess (wa @ nwa) (pa @ npa) fsta fcont"
  using applyAllIterative2 fixIntervalIdempotentThroughApplyAllInputs2 by auto

lemma computeTransactionIterative_aux2 :
  "fixInterval inte sta = IntervalTrimmed fIenv1 fIsta1 \<Longrightarrow>
   applyAllInputs fIenv1 fIsta1 con [h] = ApplyAllSuccess cwa1 pa1 sta1 cont1 \<Longrightarrow>
    \<not> (cont1 = con \<and> (con \<noteq> Close \<or> accounts sta = [])) \<Longrightarrow>
   applyAllInputs fIenv1 fIsta1 con (h # t) = ApplyAllSuccess cwa3 pa3 sta3 cont3 \<Longrightarrow>
    \<not> (cont3 = con \<and> (con \<noteq> Close \<or> accounts sta = []))"
  using applyAllInputs_once_modified_always_modified by blast

lemma computeTransactionIterative :
  "computeTransaction \<lparr> interval = inte
                      , inputs = [h] \<rparr> sta cont = TransactionOutput \<lparr> txOutWarnings = wa
                                                                    , txOutPayments = pa
                                                                    , txOutState = nsta
                                                                    , txOutContract = ncont \<rparr> \<Longrightarrow>
   computeTransaction \<lparr> interval = inte
                      , inputs = t \<rparr> nsta ncont = TransactionOutput \<lparr> txOutWarnings = nwa
                                                                    , txOutPayments = npa
                                                                    , txOutState = fsta
                                                                    , txOutContract = fcont \<rparr> \<Longrightarrow>
   computeTransaction \<lparr> interval = inte
                      , inputs = h#t \<rparr> sta cont = TransactionOutput \<lparr> txOutWarnings = wa @ nwa
                                                                    , txOutPayments = pa @ npa
                                                                    , txOutState = fsta
                                                                    , txOutContract = fcont \<rparr>"
  apply (simp only:computeTransaction.simps)
  apply (cases "fixInterval (interval \<lparr>interval = inte, inputs = [h]\<rparr>) sta")
   subgoal for fIenv1 fIsta1
    apply (simp only:IntervalResult.case Let_def)
    apply (cases "applyAllInputs fIenv1 fIsta1 cont (inputs \<lparr>interval = inte, inputs = [h]\<rparr>)")
    apply (simp only:ApplyAllResult.case)
    subgoal for cwa1 pa1 sta1 con1
      apply (cases "cont = con1 \<and> (cont \<noteq> Close \<or> accounts sta = [])")
      apply simp
      apply (simp only:if_False)
      apply (cases "fixInterval (interval \<lparr>interval = inte, inputs = t\<rparr>) nsta")
      apply (simp only:IntervalResult.case Let_def)
      subgoal for fIenv2 fIsta2
        apply (cases "applyAllInputs fIenv2 fIsta2 ncont (inputs \<lparr>interval = inte, inputs = t\<rparr>)")
        apply (simp only:ApplyAllResult.case)
        subgoal for cwa2 pa2 sta2 con2
          apply (cases "ncont = con2 \<and> (ncont \<noteq> Close \<or> accounts nsta = [])")
          apply simp
          apply (simp only:if_False)
          apply (cases "fixInterval (interval \<lparr>interval = inte, inputs = h # t\<rparr>) sta")
          apply (simp only:IntervalResult.case Let_def)
          subgoal for fIenv3 fIsta3
            apply (cases "applyAllInputs fIenv3 fIsta3 cont (inputs \<lparr>interval = inte, inputs = h # t\<rparr>)")
            apply (simp only:ApplyAllResult.case)
            subgoal for cwa3 pa3 sta3 con3
              apply (cases "(cont = con3) \<and> (cont \<noteq> Close \<or> accounts sta = [])")
              apply (metis IntervalResult.inject(1) Transaction.select_convs(1) Transaction.select_convs(2) computeTransactionIterative_aux2)
              apply (simp only:if_False)
              by (metis ApplyAllResult.inject IntervalResult.inject(1) Transaction.select_convs(1) Transaction.select_convs(2) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps applyLoopIdempotent2 fixIntervalIdempotentThroughApplyAllInputs)
            apply (metis (no_types, lifting) ApplyAllResult.distinct(1) IntervalResult.inject(1) Transaction.select_convs(1) Transaction.select_convs(2) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject computeTransactionIterative_aux)
            by (metis (no_types, lifting) ApplyAllResult.distinct(3) IntervalResult.inject(1) Transaction.select_convs(1) Transaction.select_convs(2) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject computeTransactionIterative_aux)
          by simp
        by simp_all
      by simp
    by simp_all
  by simp

lemma fixIntervalPreservesAccounts :
  "fixInterval interv sta = IntervalTrimmed interv2 sta2 \<Longrightarrow> accounts sta = accounts sta2"
  apply (cases "sta")
  apply (cases "interv")
  subgoal for accounts choices boundValues minSlot low high
    apply simp
    apply (cases "high < low")
    apply simp
    apply (cases "high < minSlot")
    by (auto simp add:Let_def)
  done

lemma applyInput_reducesContract :
  "applyInput fIenv3 curState2 head cont3 = Applied applyWarna newState2 cont4 \<Longrightarrow> size cont3 > size cont4"
  apply (cases cont3)
  apply auto
  by (simp add: add.commute applyCases_only_makes_smaller less_SucI trans_less_add2)

lemma computeTransactionEquivalence_aux3 :
  "rest \<noteq> [] \<Longrightarrow>
   applyAllInputs fIenv3 fIsta1 con [head] = ApplyAllSuccess iwa ipa fIsta3 con3 \<Longrightarrow>
   \<not> applyAllInputs fIenv3 fIsta1 con (head # rest) = ApplyAllSuccess fwa fpa sta3 con3"
  apply (simp only:applyAllInputs.simps)
  apply (simp only:applyAllLoop.simps[of fIenv3 fIsta1])
  apply (cases "reduceContractUntilQuiescent fIenv3 fIsta1 con")
  apply (simp only:ReduceResult.case list.case)
  subgoal for reduceWarns pays curState cont
    apply (cases "applyInput fIenv3 curState head cont")
    subgoal for applyWarn newState cont2
      apply (simp del:reduceContractUntilQuiescent.simps applyInput.simps applyAllLoop.simps)
      apply (cases rest)
      apply blast
      subgoal for head tail
        apply (simp del:reduceContractUntilQuiescent.simps applyInput.simps applyAllLoop.simps)
        apply (simp only:applyAllLoop.simps[of fIenv3 newState])
        apply (cases "reduceContractUntilQuiescent fIenv3 newState cont2")
        subgoal for reduceWarnsa paysa curState2 cont3
          apply (simp only:ReduceResult.case list.case)
          apply (cases "applyInput fIenv3 curState2 head cont3")
          apply (simp only:ApplyResult.case)
          subgoal for applyWarna newState2 cont4
            by (metis ApplyAllResult.inject applyAllLoop_only_makes_smaller applyInput_reducesContract order.asym)
          by simp
        by simp
      done
      by simp
    by simp

lemma computeTransactionStepEquivalence :
  "rest \<noteq> [] \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> sta con
      = TransactionOutput \<lparr> txOutWarnings = iwa
                          , txOutPayments = ipa
                          , txOutState = ista
                          , txOutContract = icont \<rparr> \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = head # rest\<rparr> sta con
      = TransactionOutput \<lparr> txOutWarnings = iwa @ iwa2
                          , txOutPayments = ipa @ ipa2
                          , txOutState = ista2
                          , txOutContract = icont2 \<rparr> \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = rest\<rparr> ista icont
      = TransactionOutput \<lparr> txOutWarnings = iwa2
                          , txOutPayments = ipa2
                          , txOutState = ista2
                          , txOutContract = icont2 \<rparr>"
  apply (simp only:computeTransaction.simps)
 apply (simp del:fixInterval.simps computeTransaction.simps applyAllInputs.simps)
  apply (cases "fixInterval interv sta")
  subgoal for fIenv1 fIsta1
    apply (simp del:fixInterval.simps computeTransaction.simps applyAllInputs.simps)
    apply (cases "applyAllInputs fIenv1 fIsta1 con [head]")
      apply (simp only:ApplyAllResult.case)
      subgoal for cwa1 pa1 sta1 con1
        apply (cases "con = con1 \<and> (con \<noteq> Close \<or> accounts sta = [])")
        apply (simp del:fixInterval.simps computeTransaction.simps applyAllInputs.simps)
        apply (cases "fixInterval interv ista2")
        subgoal for fIenv2 fIsta2
          apply (cases "applyAllInputs fIenv1 fIsta1 con (head # rest)")
          apply (simp only:ApplyAllResult.case if_False)
          subgoal for cwa2 pa2 sta2 con2
            apply (cases "con = con2 \<and> (con \<noteq> Close \<or> accounts sta = [])")
            apply simp
            apply (simp only:if_False)
            apply (cases "fixInterval interv ista")
            apply (simp only:IntervalResult.case Let_def)
            subgoal for fIenv3 fIsta3
              apply (cases "applyAllInputs fIenv3 fIsta3 icont rest")
              apply (simp only:ApplyAllResult.case) 
              subgoal for cwa3 pa3 sta3 con3
                apply (cases "icont = con3 \<and> (icont \<noteq> Close \<or> accounts ista = [])")
                apply (simp only:bool.case refl if_True)
                 apply (metis IntervalResult.inject(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps applyLoopIdempotent2 computeTransactionEquivalence_aux3 fixIntervalIdempotentThroughApplyAllInputs)
                using computeTransactionIterative_aux by auto
               apply (metis (no_types, lifting) ApplyAllResult.simps(3) IntervalResult.inject(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps applyAllPrefix1 applyAllPrefix2 applyLoopIdempotent fixIntervalIdempotentThroughApplyAllInputs2)
               by (metis (no_types, lifting) ApplyAllResult.simps(5) IntervalResult.inject(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps applyAllPrefix1 applyAllPrefix2 applyLoopIdempotent fixIntervalIdempotentThroughApplyAllInputs2)
             by (simp add: fixIntervalIdempotentThroughApplyAllInputs)
            apply simp
           by simp
         subgoal for err2
           apply (cases "applyAllInputs fIenv1 fIsta1 con (head # rest)")
           apply (simp del:fixInterval.simps computeTransaction.simps applyAllInputs.simps)
           apply (metis (no_types, lifting) IntervalResult.distinct(1) TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.select_convs(3) fixIntervalIdempotentThroughApplyAllInputs)
           apply simp
           by simp
         done
        apply simp
       by simp
     by simp

lemma applyAllInputs_prefix_error :
  "a = ApplyAllAmbiguousSlotIntervalError \<or> a = ApplyAllNoMatchError \<Longrightarrow>
   applyAllInputs env fixSta txOutCont [head] = a \<Longrightarrow>
   applyAllInputs env fixSta txOutCont (head # tail) = a"
  apply (simp only:applyAllInputs.simps applyAllLoop.simps[of env fixSta txOutCont])
  apply (cases "reduceContractUntilQuiescent env fixSta txOutCont")
  subgoal for reduceWarns pays curState cont
    apply (simp only:ReduceResult.case list.case)
    apply (cases "applyInput env curState head cont")
    subgoal for applyWarn newState cont2
      apply (simp only:ApplyResult.case)
      apply (simp only:applyAllLoop.simps[of env newState cont2])
      apply (cases "reduceContractUntilQuiescent env newState cont2")
      subgoal for reduceWarns3 pays3 curState3 cont3
        apply (simp only:ReduceResult.case list.case)
        by blast
      by simp
    by simp
  by simp

lemma applyInput_success_changes_contract :
  "applyInput env reduceState head txOutCont = Applied applyWarn applyState applyCont \<Longrightarrow> txOutCont \<noteq> applyCont"
  apply (cases txOutCont)
  apply simp_all
  subgoal for caselist timeout contract
    using applyCases_only_makes_smaller by fastforce
  done

lemma applyAllInputs_noEmpty_changes_contract :
 "applyAllInputs env fixSta txOutCont (head # []) = ApplyAllSuccess warnings payments newState cont \<Longrightarrow>
  txOutCont \<noteq> cont"
  apply (simp del:reduceContractUntilQuiescent.simps)
  apply (cases "reduceContractUntilQuiescent env fixSta txOutCont")
  subgoal for reduceWarns reducePays reduceState reduceCont
  apply (simp only:ReduceResult.case list.case)
    apply (cases "reduceCont = txOutCont")
    apply (cases "applyInput env reduceState head reduceCont")
    subgoal for applyWarn applyState applyCont
      apply (simp only:ApplyResult.case)
      by (metis applyAllLoop_only_makes_smaller applyInput_only_makes_smaller applyInput_success_changes_contract not_less_iff_gr_or_eq)
     apply simp
    apply (cases "applyInput env reduceState head reduceCont")
    subgoal for applyWarn applyState applyCont
      apply (simp only:ApplyResult.case)
      apply (drule reduceContractUntilQuiescent_only_makes_smaller[of reduceCont txOutCont env fixSta reduceWarns reducePays reduceState])
       apply simp
      apply (rule not_sym)
      apply (rule smallerSize_implies_different)
      by (metis applyAllLoop_only_makes_smaller applyInput_only_makes_smaller dual_order.strict_trans)
    by simp
  by simp

lemma computeTransaction_prefix_error :
 "computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> txOutStat txOutCont = TransactionError x \<Longrightarrow>
  computeTransaction \<lparr>interval = interv, inputs = head # tail\<rparr> txOutStat txOutCont = TransactionError x"
  apply (simp del:fixInterval.simps applyAllInputs.simps)
  apply (cases "fixInterval interv txOutStat")
  subgoal for env fixSta
  apply (simp only:IntervalResult.case Let_def)
    apply (cases "applyAllInputs env fixSta txOutCont [head]")
    subgoal for warnings payments newState cont
      apply (simp only:ApplyAllResult.case)
    apply (cases "applyAllInputs env fixSta txOutCont (head # tail)")
    subgoal for warnings2 payments2 newState2 cont2
      apply (simp only:ApplyAllResult.case)
      apply (cases "txOutCont = cont \<and> (txOutCont \<noteq> Close \<or> accounts txOutStat = [])")
      apply (cases "txOutCont = cont2 \<and> (txOutCont \<noteq> Close \<or> accounts txOutStat = [])")
      apply simp
    apply (simp only:if_False)
    using applyAllInputs_noEmpty_changes_contract apply blast
    by auto
   apply (simp add: applyAllInputs_noEmpty_changes_contract)
  by (simp add: applyAllInputs_noEmpty_changes_contract)
  apply (metis (no_types, lifting) applyAllInputs_prefix_error)
  by (metis (no_types, lifting) applyAllInputs_prefix_error)
  by simp

lemma fixInterval_doesnt_care_about_inputs :
  "fixInterval (interval \<lparr>interval = interv, inputs = inp1\<rparr>) sta = IntervalTrimmed env fixSta \<Longrightarrow>
   fixInterval (interval \<lparr>interval = interv, inputs = inp2\<rparr>) sta = IntervalTrimmed env fixSta"
  by simp

lemma reduceContractUntilQuiescent_idempotent :
  "reduceContractUntilQuiescent env newState cont2 = ContractQuiescent reduceWarns2 pays2 ista icont \<Longrightarrow>
   reduceContractUntilQuiescent env ista icont = ContractQuiescent [] [] ista icont"
  using reductionLoopIdempotent by auto

lemma fixInterval_idemp_on_same_minSlot :
  "fixInterval interv sta = IntervalTrimmed env fixSta \<Longrightarrow>
   minSlot fixSta = minSlot ista \<Longrightarrow>
   fixInterval interv ista = IntervalTrimmed env ista"
  apply (cases sta)
  apply (cases ista)
  apply (cases interv)
  apply simp
  by (smt IntervalResult.distinct(1) IntervalResult.inject(1) State.select_convs(4))

lemma fixInterval_idemp_after_computeTransaction :
  "fixInterval interv sta = IntervalTrimmed env fixSta \<Longrightarrow>
   reduceContractUntilQuiescent env fixSta con = ContractQuiescent reduceWarns pays curState cont \<Longrightarrow>
   applyInput env curState head cont = Applied applyWarn newState cont2 \<Longrightarrow>
   reduceContractUntilQuiescent env newState cont2 = ContractQuiescent reduceWarns2 pays2 ista icont \<Longrightarrow>
   fixInterval interv ista = IntervalTrimmed env ista"
  by (simp add: applyInput_preserves_minSlot fixInterval_idemp_on_same_minSlot reductionLoop_preserves_minSlot)

lemma applyAllLoop_independet_of_acc_error1 :
  "applyAllLoop env sta cont htail wa pa = ApplyAllNoMatchError \<Longrightarrow>
   applyAllLoop env sta cont htail wa2 pa2 = ApplyAllNoMatchError"
  apply (induction htail arbitrary: env sta cont wa pa wa2 pa2)
  apply (force split:ReduceResult.split)
  subgoal for head tail env sta cont wa pa wa2 pa2
    apply (simp only:applyAllLoop.simps[of env sta cont "head # tail"])
    by (auto split:ReduceResult.split ApplyResult.split simp del:applyAllLoop.simps)
  done

lemma applyAllLoop_independet_of_acc_error2 :
  "applyAllLoop env sta cont htail wa pa = ApplyAllAmbiguousSlotIntervalError \<Longrightarrow>
   applyAllLoop env sta cont htail wa2 pa2 = ApplyAllAmbiguousSlotIntervalError"
  apply (induction htail arbitrary: env sta cont wa pa wa2 pa2)
  apply (force split:ReduceResult.split)
  subgoal for head tail env sta cont wa pa wa2 pa2
    apply (simp only:applyAllLoop.simps[of env sta cont "head # tail"])
    by (auto split:ReduceResult.split ApplyResult.split simp del:applyAllLoop.simps)
  done

lemma computeTransactionStepEquivalence_error :
  "rest \<noteq> [] \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> sta con
      = TransactionOutput \<lparr> txOutWarnings = iwa
                          , txOutPayments = ipa
                          , txOutState = ista
                          , txOutContract = icont \<rparr> \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = head # rest\<rparr> sta con
      = TransactionError x \<Longrightarrow>
   computeTransaction \<lparr>interval = interv, inputs = rest\<rparr> ista icont
      = TransactionError x"
  apply (cases rest)
  apply simp
  subgoal for hrest htail
    apply (simp only:computeTransaction.simps[of "\<lparr>interval = interv, inputs = [head]\<rparr>"]
                     computeTransaction.simps[of "\<lparr>interval = interv, inputs = head # hrest # htail\<rparr>"] Let_def)
    apply (cases "fixInterval (interval \<lparr>interval = interv, inputs = [head]\<rparr>) sta")
    subgoal for env fixSta
      apply (subst (asm) fixInterval_doesnt_care_about_inputs[of interv "[head]" sta env fixSta "head # hrest # htail"])
      apply blast
      apply (simp only:IntervalResult.case)
      apply (simp only:applyAllInputs.simps applyAllLoop.simps[of env fixSta])
      apply (cases "reduceContractUntilQuiescent env fixSta con")
      subgoal for reduceWarns pays curState cont
        apply (simp del:fixInterval.simps reduceContractUntilQuiescent.simps computeTransaction.simps applyInput.simps)
        apply (cases "applyInput env curState head cont")
        subgoal for applyWarn newState cont2
          apply (simp only:ApplyResult.case)
          apply (simp only:applyAllInputs.simps applyAllLoop.simps[of env newState] computeTransaction.simps Let_def)
          apply (cases "reduceContractUntilQuiescent env newState cont2")
          subgoal for reduceWarns2 pays2 curState2 cont3
            apply (simp only:ReduceResult.case list.case ApplyAllResult.case)
            apply (cases "con = cont3")
            apply (metis applyInput_reducesContract dual_order.strict_trans order.asym reduceContractUntilQuiescent_only_makes_smaller)
            apply (simp del:fixInterval.simps reduceContractUntilQuiescent.simps computeTransaction.simps applyInput.simps)

            apply (simp only:fixInterval_idemp_after_computeTransaction[of interv sta env fixSta con
                                                                           reduceWarns pays curState cont
                                                                           head applyWarn newState cont2
                                                                           reduceWarns2 pays2 ista icont])
            apply (simp only:IntervalResult.case applyAllLoop.simps[of env ista icont])
            apply (simp only:reduceContractUntilQuiescent_idempotent ReduceResult.case Transaction.select_convs list.case)
            apply (cases "applyInput env ista hrest icont")
            subgoal for applyWarna newState2 cont4
              apply (simp only:ApplyResult.case)
              apply (cases "applyAllLoop env newState2 cont4 htail
                                         (([] @ convertReduceWarnings reduceWarns @ convertApplyWarning applyWarn) @
                                          convertReduceWarnings reduceWarns2 @ convertApplyWarning applyWarna)
                                         (([] @ pays) @ pays2)")
              apply (smt ApplyAllResult.simps(8) TransactionOutput.distinct(1) applyAllLoop_only_makes_smaller applyInput_reducesContract dual_order.strict_trans reduceContractUntilQuiescent_only_makes_smaller smallerSize_implies_different)
              using applyAllLoop_independet_of_acc_error1 apply auto[1]
              using applyAllLoop_independet_of_acc_error2 by auto
            by simp
          by simp
        by simp
      by simp
    by simp
  done

lemma playTraceAuxIterative_base_case :
  "playTraceAux \<lparr> txOutWarnings = iwa
                , txOutPayments = ipa
                , txOutState = ista
                , txOutContract = icont\<rparr> (Cons \<lparr> interval = inte
                                               , inputs = [h] \<rparr> (Cons \<lparr> interval = inte
                                                                      , inputs = t \<rparr> Nil))
          = TransactionOutput \<lparr> txOutWarnings = wa
                              , txOutPayments = pa
                              , txOutState = nsta
                              , txOutContract = ncont \<rparr> \<Longrightarrow>
   playTraceAux \<lparr> txOutWarnings = iwa
                , txOutPayments = ipa
                , txOutState = ista
                , txOutContract = icont\<rparr> (Cons \<lparr> interval = inte
                                               , inputs = h#t \<rparr> Nil)
          = TransactionOutput \<lparr> txOutWarnings = wa
                              , txOutPayments = pa
                              , txOutState = nsta
                              , txOutContract = ncont \<rparr>"
  apply (cases "computeTransaction \<lparr>interval = inte, inputs = [h]\<rparr> ista icont")
  subgoal for to1
    apply (cases "computeTransaction \<lparr>interval = inte, inputs = h # t\<rparr> ista icont")
    subgoal for to2
      apply (simp del:computeTransaction.simps add:Let_def)
      apply (cases to1)
      subgoal for txOutWarningsa txOutPaymentsa txOutState txOutContract
        apply (cases "computeTransaction \<lparr>interval = inte, inputs = t\<rparr> txOutState txOutContract")
        apply (simp del:computeTransaction.simps add:Let_def)
        subgoal for x1
          by (smt TransactionOutput.inject(1) TransactionOutputRecord.ext_inject TransactionOutputRecord.surjective TransactionOutputRecord.update_convs(1) TransactionOutputRecord.update_convs(2) TransactionOutputRecord_ext_def append.assoc append.right_neutral append_Nil2 append_assoc computeTransactionIterative)
        by simp
      done
    subgoal for to2
      apply (simp del:computeTransaction.simps add:Let_def)
      apply (cases to1)
      subgoal for txOutWarningsa txOutPaymentsa txOutState txOutContract
        apply (cases "computeTransaction \<lparr>interval = inte, inputs = t\<rparr> txOutState txOutContract")
        apply (simp del:computeTransaction.simps add:Let_def)
        subgoal for x1
          by (metis TransactionOutput.distinct(1) computeTransactionStepEquivalence_error)
        by simp
      done
    done
  by simp

lemma playTraceAuxToSingleInputIsEquivalent_induction_step_aux :
  "(\<And>acc. playTraceAux acc (\<lparr>interval = interv, inputs = a # list\<rparr> # tral) =
               playTraceAux acc (inputsToTransactions interv (a # list) @ traceListToSingleInput tral)) \<Longrightarrow>
   playTraceAux acc3 (\<lparr>interval = interv, inputs = head # a # list\<rparr> # tral) =
   playTraceAux acc3 ((\<lparr>interval = interv, inputs = [head]\<rparr> # inputsToTransactions interv (a # list)) @ traceListToSingleInput tral)"
  apply (cases acc3)
  apply (simp del:computeTransaction.simps add:Let_def)
  subgoal for txOutWarningsa txOutPaymentsa txOutState txOutContract
    apply (cases "computeTransaction \<lparr>interval = interv, inputs = head # a # list\<rparr> txOutState txOutContract")
     apply (simp only:TransactionOutput.case)
     apply (cases "computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> txOutState txOutContract")
      apply (simp only:TransactionOutput.case)
    subgoal for transRes1 transRes2
      apply (cases transRes1)
      subgoal for txOutWarnings1 txOutPayments1 txOutState1 txOutContract1
        apply (cases transRes2)
        subgoal for txOutWarnings2 txOutPayments2 txOutState2 txOutContract2
          apply (simp del:computeTransaction.simps playTraceAux.simps)
          apply (subst exE[of "\<lambda> nwa . txOutWarnings1 = txOutWarnings2 @ nwa"])
          using computeAllPrefix1 apply blast
          apply (subst exE[of "\<lambda> npa . txOutPayments1 = txOutPayments2 @ npa"])
          using computeAllPrefix2 apply blast
          apply (simp del:computeTransaction.simps playTraceAux.simps)
          apply (smt TransactionOutput.case(1) TransactionOutputRecord.simps(1) TransactionOutputRecord.simps(2) TransactionOutputRecord.update_convs(1) TransactionOutputRecord.update_convs(2) append_assoc computeTransactionStepEquivalence list.simps(3) playTraceAux.simps(2))
          apply blast
          by blast
          done
        done
    using computeTransaction_prefix_error apply fastforce
    apply (cases "computeTransaction \<lparr>interval = interv, inputs = [head]\<rparr> txOutState txOutContract")
    apply (simp only:TransactionOutput.case)
    subgoal for transRes1 transRes2
        apply (cases transRes2)
        subgoal for txOutWarnings2 txOutPayments2 txOutState2 txOutContract2
          apply (simp del:computeTransaction.simps playTraceAux.simps)
          subgoal premises facts
            apply(subst facts(1)[symmetric])
            apply (simp only:playTraceAux.simps Let_def)
            apply (subst computeTransactionStepEquivalence_error)
            apply simp
            apply (subst facts(4))
            apply simp
            apply (subst facts(3))
            apply simp
            by (metis (no_types, lifting) TransactionOutput.simps(6) computeTransactionStepEquivalence_error facts(3) facts(4) list.distinct(1))
          done
        done
      using computeTransaction_prefix_error by fastforce
    done

lemma playTraceAuxToSingleInputIsEquivalent_induction_step :
  "(\<And>acc. playTraceAux acc tral = playTraceAux acc (traceListToSingleInput tral)) \<Longrightarrow>
    playTraceAux acc ( \<lparr>interval = interv, inputs = inps\<rparr> # tral)
      = playTraceAux acc (traceListToSingleInput ( \<lparr>interval = interv, inputs = inps\<rparr> # tral))"
  apply (induction inps arbitrary:acc tral)
  apply simp
  subgoal for acc tral
    apply (cases acc)
    subgoal for txOutWarnings txOutPayments txOutState txOutContract
      apply (simp only:playTraceAux.simps)
      done
    done
  subgoal for head tail acc tral
    apply (simp only:traceListToSingleInput.simps)
    apply (cases tail)
     apply (cases acc)
    subgoal for txOutWarnings txOutPayments txOutState txOutContract
      apply (simp only:traceListToSingleInput.simps inputsToTransactions.simps playTraceAux.simps)
      by simp
    apply (simp only:inputsToTransactions.simps)
    apply (cases acc)
    subgoal for tailHead tailTail txOutWarnings txOutPayments txOutState txOutContract
      apply (rule playTraceAuxToSingleInputIsEquivalent_induction_step_aux)
      by blast
    done
  done

lemma playTraceAuxToSingleInputIsEquivalent :
  "playTraceAux acc tral = playTraceAux acc (traceListToSingleInput tral)"
  apply (induction tral arbitrary:acc)
  apply simp
  by (metis Transaction.cases playTraceAuxToSingleInputIsEquivalent_induction_step)

theorem traceToSingleInputIsEquivalent : "playTrace sn co tral = playTrace sn co (traceListToSingleInput tral)"
  apply (simp only:playTrace.simps)
  using playTraceAuxToSingleInputIsEquivalent by blast


lemma transactionPrefixForSingleInput : "h # t = traceListToSingleInput nt \<Longrightarrow> (\<exists> nt2. t = traceListToSingleInput nt2)"
  apply (induction nt rule:traceListToSingleInput.induct)
  apply simp
  subgoal for si inps rest
    apply (induction inps arbitrary: h t rest si)
    apply auto[1]
    subgoal for a inps h t rest si
      apply (simp only:traceListToSingleInput.simps)
      apply (cases inps)
      apply simp
      apply (simp only:refl inputsToTransactions.simps)
      by (metis append_Cons list.inject traceListToSingleInput.simps(2))
    done
  done


lemma traceListToSingleInput_isSingleInput : "\<lparr>interval = inte, inputs = inp_h # inp_t\<rparr> # t = traceListToSingleInput t2 \<Longrightarrow> inp_t \<noteq> [] \<Longrightarrow> False"
  apply (induction t2 rule:traceListToSingleInput.induct)
  apply simp_all
  subgoal for si inps rest
    apply (induction si inps rule:inputsToTransactions.induct)
    by simp_all
  done

fun isSingleInput :: "Transaction list \<Rightarrow> bool" where
"isSingleInput [] = True" |
"isSingleInput (h # t) = (length (inputs h) \<le> 1 \<and> isSingleInput t)"

lemma isSingleInput_dist_with_append : "isSingleInput (a @ b) = (isSingleInput a \<and> isSingleInput b)"
  apply (induction a arbitrary:b)
  by auto

lemma inputToTransactions_isSingleInput : "isSingleInput (inputsToTransactions si inps)"
  apply (induction si inps rule:inputsToTransactions.induct)
  by auto

lemma traceListToSingleInput_isSingleInput2 : "isSingleInput (traceListToSingleInput t)"
  apply (induction t rule:traceListToSingleInput.induct)
  by (simp_all add: inputToTransactions_isSingleInput isSingleInput_dist_with_append)
    
end
