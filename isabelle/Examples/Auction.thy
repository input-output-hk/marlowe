theory Auction
imports Core.Semantics Core.ValidState Core.CloseSafe
begin

definition bid :: ByteString where
"bid = ByteString [1]"

definition token_ada :: Token where
"token_ada = Token (ByteString []) (ByteString [])"

type_synonym AuctionWinner = "(Value \<times> Party) option"

record AuctionTerms = owner :: Party
                      minBid :: int
                      maxBid :: int
                      deadline :: POSIXTime


fun settle :: "AuctionWinner \<Rightarrow> AuctionTerms \<Rightarrow> Contract" where
  "settle None _ = Close" |
  "settle (Some (v, p)) terms = (Pay p (Party (owner terms)) token_ada v Close)"

fun choice :: "Party \<Rightarrow> ChoiceId" where
  "choice p = (ChoiceId bid p)"

(* Los bidders directamente como parties en lugar de String *)
fun partyToValueId :: "Party \<Rightarrow> ValueId" where
  "partyToValueId (Address pk) = ValueId pk" | 
  "partyToValueId (Role r) = ValueId r"

fun remove :: "Party \<Rightarrow> Party list \<Rightarrow> Party list" where
"remove p ls = filter ((\<noteq>) p) ls"

lemma removePresentElementReducesSize : "p \<in> set ls \<Longrightarrow> length (filter ((\<noteq>) p) ls) < length ls"
  by (simp add: length_filter_less)

lemma removeAbsentElementMantainsSize : "p \<notin> set ls \<Longrightarrow> length (filter ((\<noteq>) p) ls) = length ls"
  by (metis (mono_tags, lifting) filter_True)

type_synonym contractLoopType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms"
type_synonym handleChooseType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"
type_synonym handleDepositType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"

fun evalBoundAuction :: "(contractLoopType + (handleChooseType + handleDepositType)) \<Rightarrow> nat" where
"evalBoundAuction (Inl (_, ps, qs, _)) = 2 * length ps + 4 * length qs + 1" |
"evalBoundAuction (Inr (Inl (_, ps, qs, _, p))) = 2 * length ps + 4 * length qs + (if p \<in> set qs then 0 else 8)" |
"evalBoundAuction (Inr (Inr (_, ps, qs, _, p))) = 2 * length ps + 4 * length qs + (if p \<in> set ps then 0 else 8)"

function (sequential) contractLoop :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Contract"
and handleChoose :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Party \<Rightarrow> Case"
and handleDeposit :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Party \<Rightarrow> Case" 
where
"handleChoose m ps qs terms p = Case (Choice (choice p) [(minBid terms, maxBid terms)])
                                               (Let (partyToValueId p) 
                                                  (ChoiceValue (choice p))
                                                  (contractLoop m (p # ps) (remove p qs) terms))" |
"handleDeposit m ps qs terms p = 
   (let v = (UseValue (partyToValueId p)) in
    let ps' = (remove p ps) in
    (Case (Deposit p p token_ada v)
          (case m of
              None          \<Rightarrow> contractLoop (Some (v, p)) ps' qs terms
            | Some (v', p') \<Rightarrow> If (ValueGT v v') 
                                  (contractLoop (Some (v, p)) ps' qs terms) 
                                  (contractLoop m ps' qs terms))))" |

"contractLoop m [] [] terms = settle m terms" |
"contractLoop m ps qs terms = (When ( (map (handleChoose m ps qs terms) qs) @ 
                                      (map (handleDeposit m ps qs terms) ps)) 
                                      (deadline terms) (settle m terms))"  
  by pat_completeness auto
termination
  apply (relation "measure (evalBoundAuction)")
  apply auto 
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize by fastforce


fun auction :: "Party \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Party list \<Rightarrow> POSIXTime \<Rightarrow> Contract" where
"auction own mBid MBid bidders ddl = (contractLoop None [] bidders \<lparr>owner = own, minBid = mBid, maxBid = MBid, deadline = ddl\<rparr>)" 


definition invariantHoldsForAuction :: "AuctionTerms \<Rightarrow> AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> State \<Rightarrow> bool" where
"invariantHoldsForAuction terms m ps qs curState = ((\<forall>x . x \<in> set qs \<longrightarrow> \<not> member (partyToValueId x) (boundValues curState))
                                                  \<and> (\<forall>x . x \<in> set ps \<longrightarrow> findWithDefault 0 (partyToValueId x) (boundValues curState) > 0)
                                                  \<and> (\<forall>x y . m = Some (x, y) \<longrightarrow> ((lookup (y, token_ada) (accounts curState) = lookup (partyToValueId y) (boundValues curState))
                                                          \<and> (findWithDefault 0 (partyToValueId y) (boundValues curState) > 0)
                                                          \<and> (UseValue (partyToValueId y)) = x))
                                                  \<and> (minBid terms > 0)
                                                  \<and> (distinct (ps @ qs)))"

lemma applyCasesOfMap : "(\<And> p applyWarn newState cont2. p \<in> set ps \<Longrightarrow> applyCases env curState head [f p] = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning)
                               \<Longrightarrow> (applyCases env curState head (map f ps) = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning)"
  apply (induction ps)
    apply simp
  apply (elim applyCases.elims)
           apply auto
    apply (smt (verit, ccfv_SIG) ApplyResult.inject applyCases.simps(1))
   apply (meson ApplyResult.inject)
  by (metis applyCases.simps(3))

lemma applyCasesDistributiveAgainstAppend : "(\<And> applyWarn newState cont . applyCases env curState head l1 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                         \<Longrightarrow> (\<And> applyWarn newState cont . applyCases env curState head l2 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                        \<Longrightarrow> (applyCases env curState head (l1 @ l2) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  apply (induction l1)
   apply simp
  apply (elim applyCases.elims)
           apply auto
    apply metis
  apply metis
  by metis

lemma temporaryLemma : "(\<forall>x. x \<in> set ps \<longrightarrow> \<not> member (partyToValueId x) bv) \<Longrightarrow> 
                        y \<in> set ps \<Longrightarrow> 0 = (case lookup (partyToValueId y) bv of None \<Rightarrow> 0 | Some z \<Rightarrow> z)"
  by simp

lemma applyInputContractLoopNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> (\<And> applyWarn newState cont. applyInput env curState head (contractLoop m ps qs terms) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  and applyInputHandleChooseNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set qs \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleChoose m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  and applyInputHandleDepositNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set ps \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleDeposit m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
   apply (induction m ps qs terms and m ps qs terms x and m ps qs terms x rule:"contractLoop_handleChoose_handleDeposit.induct")
  subgoal for m ps qs terms p applyWarn newState cont
    apply (elim applyCases.elims)
             apply auto
    by (metis ApplyResult.inject ApplyResult.simps(3) applyCases.simps(10))
  subgoal for m ps qs terms p applyWarn newState cont
    apply (simp only:handleDeposit.simps Let_def)
    apply (elim applyCases.elims)
             apply simp_all
    apply (split if_split_asm)
    apply (simp only:Let_def)
       apply (split if_split_asm)
    apply (meson ApplyResult.inject)
    subgoal for enva state accId1 party1 tok1 amount accId2
      by (metis MList.findWithDefault.simps invariantHoldsForAuction_def)
    by (metis Semantics.applyCases.simps(10) Semantics.applyInput.simps(2) closeIsSafe_applyInput)
    apply simp
    apply (metis ApplyResult.simps(3) applyInput.simps(2) applyInput.simps(3) settle.elims)
   apply (smt (verit, best) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(2))
  by (smt (verit, ccfv_SIG) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(3))

lemma reduceContractStepPay_preservesCont : "reduceContractStep env fixSta (Pay accId payee token val cont) = Reduced wa ef sta cont2 \<Longrightarrow>
                                             cont2 = cont"
  apply auto
  by (smt (verit, best) ReduceStepResult.inject giveMoney.simps old.prod.case)

lemma auctionSettlementSafe_reduceContractStepEmpty : "invariantHoldsForAuction terms m [] [] fixSta \<Longrightarrow>
                                                       reduceContractStep env fixSta (contractLoop m [] [] terms) = Reduced wa ef sta cont \<Longrightarrow> cont = Close"
  apply (auto)
  apply (cases m)
   apply (simp add: closeIdemp_reduceContractStep)
  apply (auto simp del:reduceContractStep.simps)
  by (meson reduceContractStepPay_preservesCont)

lemma reduceContractLoopEqualsSettlement : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                             invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                             reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow> 
                                             (cont = settle m terms \<and> fixSta = sta)"
  by (smt (verit, ccfv_SIG) ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject case_prod_conv contractLoop.elims old.prod.exhaust reduceContractStep.simps(4))

lemma contractLoopReducedSatisfyInvariant : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                             invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                             reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow>
                                             cont = settle m terms \<Longrightarrow> 
                                             invariantHoldsForAuction terms m [] [] sta"
  apply (simp only:invariantHoldsForAuction_def)
  apply auto
  apply (smt (verit, ccfv_SIG) Contract.inject(1) distinct_append findWithDefault.simps invariantHoldsForAuction_def member.elims(2) reduceContractLoopEqualsSettlement settle.simps(2))
  apply (smt (verit, ccfv_SIG) Contract.inject(1) distinct_append findWithDefault.simps invariantHoldsForAuction_def member.elims(2) reduceContractLoopEqualsSettlement settle.simps(2))
  apply (smt (verit, ccfv_SIG) Contract.inject(1) distinct_append findWithDefault.simps invariantHoldsForAuction_def member.elims(2) reduceContractLoopEqualsSettlement settle.simps(2))
  by (smt (verit, ccfv_SIG) Contract.inject(1) distinct_append findWithDefault.simps invariantHoldsForAuction_def member.elims(2) reduceContractLoopEqualsSettlement settle.simps(2))

lemma auctionSettlementSafe_reduceContractStep : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                  reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow> 
                                                  cont = Close \<or> (cont = settle m terms \<and> invariantHoldsForAuction terms m [] [] sta)"
  by (metis auctionSettlementSafe_reduceContractStepEmpty reduceContractLoopEqualsSettlement contractLoopReducedSatisfyInvariant)
  
lemma auctionIsSafe_reduceContractStepEmpty : "invariantHoldsForAuction terms m [] [] fixSta \<Longrightarrow>
                                               reduceContractStep env fixSta (contractLoop m [] [] terms) = Reduced wa ef newSta cont \<Longrightarrow>
                                               wa = ReduceNoWarning"
  apply (simp only:contractLoop.simps)
  apply (cases m)
   apply (simp add: closeIsSafe_reduceContractStep)
  apply (auto simp only:invariantHoldsForAuction_def settle.simps reduceContractStep.simps Let_def refl
              split:if_split_asm prod.splits)
   apply simp
  by simp

lemma auctionIsSafe_reduceContractStep : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                          reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef newSta cont
                                          \<Longrightarrow> wa = ReduceNoWarning"
  apply (cases ps)
   apply (cases qs)
    apply (meson auctionIsSafe_reduceContractStepEmpty)
   apply (simp only:contractLoop.simps)
  subgoal for a list
    by (auto simp only:settle.simps reduceContractStep.simps Let_def split:if_split_asm prod.splits)
  apply (cases qs)
   by (auto simp only:settle.simps contractLoop.simps reduceContractStep.simps Let_def split:if_split_asm prod.splits)


lemma auctionIsSafe_reductionLoop : "wa = [] \<Longrightarrow> invariantHoldsForAuction terms m ps qs curState \<Longrightarrow>
                                                 reductionLoop reducedBefore env curState (contractLoop m ps qs terms) wa ef = ContractQuiescent reducedAfter reduceWarns pays newState cont
                                     \<Longrightarrow> reduceWarns = []"
  apply (auto simp only:reductionLoop.simps[of reducedBefore env curState "(contractLoop m ps qs terms)" "[]" ef] Let_def split:ReduceStepResult.splits if_split_asm ReduceEffect.splits)
  apply (simp only:reductionLoop.simps)
  apply (simp only:Let_def)
     apply (auto simp only:reductionLoop.simps[of reducedBefore env curState "(contractLoop m ps qs terms)" "[]" ef] Let_def split:ReduceStepResult.splits if_split_asm ReduceEffect.splits)
  apply (metis auctionSettlementSafe_reduceContractStep auctionSettlementSafe_reduceContractStepEmpty closeIdemp_reduceContractStep closeIsSafe_reductionLoop contractLoop.simps(1))
       apply (metis auctionSettlementSafe_reduceContractStep auctionSettlementSafe_reduceContractStepEmpty closeIdemp_reduceContractStep closeIsSafe_reductionLoop contractLoop.simps(1))
      apply (metis auctionIsSafe_reduceContractStep auctionSettlementSafe_reduceContractStep closeIsSafe_reduceContractStep contractLoop.simps(1))
     apply (metis auctionIsSafe_reduceContractStepEmpty auctionSettlementSafe_reduceContractStep closeIsSafe_reduceContractStep contractLoop.simps(1))
  apply (simp only:reductionLoop.simps)
    apply (auto simp only:reductionLoop.simps[of reducedBefore env curState "(contractLoop m ps qs terms)" "[]" ef] Let_def split:ReduceStepResult.splits if_split_asm ReduceEffect.splits)
       apply (metis auctionSettlementSafe_reduceContractStep auctionSettlementSafe_reduceContractStepEmpty closeIdemp_reduceContractStep closeIsSafe_reductionLoop contractLoop.simps(1))
      apply (metis auctionSettlementSafe_reduceContractStep auctionSettlementSafe_reduceContractStepEmpty closeIdemp_reduceContractStep closeIsSafe_reductionLoop contractLoop.simps(1))
     apply (metis auctionIsSafe_reduceContractStepEmpty auctionSettlementSafe_reduceContractStep closeIsSafe_reduceContractStep contractLoop.simps(1))
    apply (metis auctionIsSafe_reduceContractStep auctionSettlementSafe_reduceContractStep closeIsSafe_reduceContractStep contractLoop.simps(1))
   apply (simp add: auctionIsSafe_reduceContractStep)
  by (simp add: auctionIsSafe_reduceContractStep)

lemma auctionIsSafe_reduceContractUntilQuiescent : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                    reduceContractUntilQuiescent env fixSta (contractLoop m ps qs terms) = ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow>
                                                    reduceWarns = []"
  by (metis auctionIsSafe_reductionLoop reduceContractUntilQuiescent.simps)

lemma reduceSettlementUntilQuiescentIsClose : "invariantHoldsForAuction terms m [] [] fixSta \<Longrightarrow>
                                               reductionLoop reducedBefore env curState (settle m terms) wa ef = ContractQuiescent reducedAfter reduceWarns pays newState cont \<Longrightarrow>
                                               cont = Close"
  apply (cases m)
   apply (simp add: closeIdemp_reductionLoop)
  apply (auto simp only:settle.simps reduceContractUntilQuiescent.simps reductionLoop.simps)
  using reduceContractStepPay_preservesCont closeIdemp_reduceContractStep apply simp
    apply (auto simp only:reduceContractStep.simps Let_def split:if_split_asm prod.splits ReduceStepResult.splits)
    using closeIdemp_reductionLoop apply presburger
   using closeIdemp_reductionLoop apply presburger
  using closeIdemp_reductionLoop by presburger

lemma settleIsSafe_applyAllInputs : "invariantHoldsForAuction terms m [] [] fixSta \<Longrightarrow>
                                               applyAllInputs env fixSta (contractLoop m [] [] terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                               warnings = []"
  apply (simp only:contractLoop.simps)
  apply (cases m)
   apply (simp del:applyAllLoop.simps)
   apply (simp add: closeIsSafe_applyAllInputs)
  apply (cases inps)
   apply (smt (z3) ApplyAllResult.distinct(3) ApplyAllResult.inject ReduceResult.exhaust ReduceResult.simps(4) ReduceResult.simps(5) append_Nil2 applyAllInputs.simps applyAllLoop.simps auctionIsSafe_reduceContractUntilQuiescent contractLoop.simps(1) convertReduceWarnings.simps(1) list.simps(4))
  using reduceSettlementUntilQuiescentIsClose auctionIsSafe_reduceContractUntilQuiescent
  by (smt (z3) ApplyAllResult.simps(3) ApplyAllResult.simps(5) ApplyResult.case(2) ReduceResult.exhaust ReduceResult.simps(4) ReduceResult.simps(5) applyAllInputs.simps applyAllLoop.simps applyInput.simps(2) list.simps(5) reduceContractUntilQuiescent.simps) 
  

lemma auctionIsSafe_applyAllInputsToClose : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                      reduceContractUntilQuiescent env fixSta (contractLoop m ps qs terms) = ContractQuiescent reduced1 reduceWarns1 pays1 curState1 Close \<Longrightarrow>
                                      applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                      warnings = []"
  apply (simp del:reduceContractUntilQuiescent.simps)
  by (smt (z3) ApplyAllResult.distinct(1) ApplyAllResult.inject ApplyResult.simps(5) append_Nil applyInput.simps(2) auctionIsSafe_reduceContractUntilQuiescent convertReduceWarnings.simps(1) list.exhaust list.simps(4) list.simps(5))

lemma reduceUntilQuiescentIsFixedOrClose : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                            invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                            reduceContractUntilQuiescent env fixSta (contractLoop m ps qs terms) = ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow>
                                            (cont = Close \<or> (cont = contractLoop m ps qs terms \<and> fixSta = curState))"
  apply (simp only:reduceContractUntilQuiescent.simps reductionLoop.simps)
  apply (split ReduceStepResult.splits)
  subgoal for wa ef sta cont1
    using reduceContractLoopEqualsSettlement
    by (smt (z3) ReduceResult.simps(3) ReduceStepResult.exhaust ReduceStepResult.simps(10) ReduceStepResult.simps(8) ReduceStepResult.simps(9) auctionSettlementSafe_reduceContractStepEmpty closeIdemp_reductionLoop contractLoop.simps(1) contractLoopReducedSatisfyInvariant reduceContractUntilQuiescent.simps reduceSettlementUntilQuiescentIsClose reductionLoop.simps rev.simps(1) settle.elims)
   apply fastforce
  by fastforce

lemma reduceUntilQuiescentApplyInput_isSafe : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                reduceContractUntilQuiescent env fixSta (contractLoop m ps qs terms) = 
                                                ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow>
                                               applyInput env curState head cont = 
                                               Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning"
  apply (cases ps)
   apply (cases qs)
    apply (metis ApplyResult.simps(3) applyInput.simps(2) contractLoop.simps(1) reduceContractUntilQuiescent.simps reduceSettlementUntilQuiescentIsClose)
  using reduceUntilQuiescentIsFixedOrClose apply (metis ApplyResult.simps(3) applyInput.simps(2) applyInputContractLoopNoWarnings list.distinct(1))
  using reduceUntilQuiescentIsFixedOrClose by (metis ApplyResult.simps(3) applyInput.simps(2) applyInputContractLoopNoWarnings list.distinct(1))

(*
  Lemmas con respecto a la preservación de invariante al aplicar un input + algun paso más
*)

lemma applyInputHandleChoosePreservesInvariant : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                  applyInput env fixSta (IChoice (choice p) cho) (contractLoop m ps qs terms) = 
                                                  Applied applyWarn curState (Let (partyToValueId p) (ChoiceValue (choice p)) (contractLoop m (p # ps) (remove p qs) terms)) \<Longrightarrow>
                                                  (invariantHoldsForAuction terms m ps (remove p qs) curState \<and> (findWithDefault 0 (choice p) (choices curState) > 0))"
  sorry

lemma reduceLetAfterApplyInputHandleChoosePreservesInvariant : "findWithDefault 0 (choice p) (choices fixSta) > 0 \<Longrightarrow>
                                                                invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                                reduceContractStep env fixSta (Let (partyToValueId p) (ChoiceValue (choice p)) (contractLoop m (p # ps) (remove p qs) terms)) =
                                                                Reduced wa ef curState (contractLoop m (p # ps) (remove p qs) terms) \<Longrightarrow>
                                                                invariantHoldsForAuction terms m (p # ps) (remove p qs) curState"
  sorry

lemma applyAllInputsPreservesInvariantOrClose : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                 applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                                 cont = Close \<or> (cont = contractLoop newm newps newqs terms \<and> invariantHoldsForAuction terms newm newps newqs newState)"
  sorry

lemma applyAllInputsToClose_isSafe : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                      applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState Close \<Longrightarrow>
                                      warnings = []"
  sorry


lemma auctionIsSafe_applyAllInputs : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                      applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                      warnings = []"
  using applyAllInputsToClose_isSafe applyAllInputsPreservesInvariantOrClose
  by (metis contractLoop.simps(1) settle.simps(1)) 

lemma fixingIntervalPreservesInvariant : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                          fixInterval (low, high) sta = IntervalTrimmed env fixSta \<Longrightarrow> 
                                          invariantHoldsForAuction terms m ps qs fixSta"
  by (smt (verit, best) IntervalResult.distinct(1) IntervalResult.inject(1) State.select_convs(1) State.select_convs(3) State.surjective State.update_convs(4) fixInterval.simps invariantHoldsForAuction_def)


lemma auctionIsSafe_computeTransactionFixSta : "fixInterval (interval tra) sta = IntervalTrimmed env fixSta \<Longrightarrow> 
                                                invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                computeTransaction tra sta (contractLoop m ps qs terms) = TransactionOutput trec \<Longrightarrow>
                                                txOutWarnings trec = []"
  by (smt (z3) ApplyAllResult.exhaust ApplyAllResult.simps(10) ApplyAllResult.simps(8) ApplyAllResult.simps(9) IntervalResult.simps(5) TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject TransactionOutputRecord.surjective auctionIsSafe_applyAllInputs computeTransaction.simps)

lemma auctionIsSafe_computeTransaction : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                          computeTransaction tra sta (contractLoop m ps qs terms) = TransactionOutput trec \<Longrightarrow>
                                          txOutWarnings trec = []"
  using fixingIntervalPreservesInvariant auctionIsSafe_computeTransactionFixSta
  by (smt (verit, ccfv_SIG) IntervalResult.simps(6) closeIsSafe computeTransaction.simps fixInterval.elims)


lemma computeTransactionPreservesInvariantOrClose : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                                      computeTransaction tra sta (contractLoop m ps qs terms) = TransactionOutput trec \<Longrightarrow>
                                                      cont = txOutContract trec \<Longrightarrow> newState = txOutState trec \<Longrightarrow>
                                                      cont = Close \<or> (cont = contractLoop newm newps newqs terms \<and> invariantHoldsForAuction terms newm newps newqs newState)"
  sorry

lemma auctionIsSafe_playTraceAux : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                    playTraceAux \<lparr> txOutWarnings = Nil
                                                 , txOutPayments = Nil
                                                 , txOutState = emptyState sl
                                                 , txOutContract = (contractLoop m ps qs terms) \<rparr> (Cons h t) = TransactionOutput transResRec \<Longrightarrow>
                                    txOutWarnings transResRec = []"
  apply (simp only:playTraceAux.simps Let_def)
  apply (split TransactionOutput.splits)
  defer
   apply simp
  using fixingIntervalPreservesInvariant apply (simp del:applyAllInputs.simps)
  using applyAllInputsToClose_isSafe applyAllInputsPreservesInvariantOrClose


  sorry

lemma auctionIsSafe_contractLoop : "invariantHoldsForAuction terms m ps qs (emptyState slot) \<Longrightarrow>
                         playTrace slot (contractLoop m ps qs terms) txList  = TransactionOutput txOut \<Longrightarrow> 
                         txOutWarnings txOut = []"
  by (smt (verit, best) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject TransactionOutputRecord.surjective auctionIsSafe_playTraceAux playTrace.simps playTraceAux.elims)


lemma emptyStateHoldsInvariant : "mBid > 0 \<Longrightarrow> distinct bidders \<Longrightarrow> invariantHoldsForAuction \<lparr>owner = own, minBid = mBid, maxBid = MBid, deadline = ddl\<rparr> None [] bidders (emptyState slot)"
    apply (simp only:invariantHoldsForAuction_def)
    apply auto
  subgoal for x
      using lookup_empty by blast
    done

theorem auctionIsSafe : "mBid > 0 \<Longrightarrow> distinct bidders \<Longrightarrow> 
  playTrace slot (auction own mBid MBid bidders ddl) txList = TransactionOutput txOut \<Longrightarrow> txOutWarnings txOut = []"
  apply (simp only:auction.simps)
  by (metis Auction.auction.simps auctionIsSafe_contractLoop emptyStateHoldsInvariant)

end
