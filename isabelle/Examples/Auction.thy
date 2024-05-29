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
                                              (contractLoop m (p # ps) (remove p qs) terms)" |
"handleDeposit m ps qs terms p = 
   (let v = ChoiceValue (choice p) in
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
"invariantHoldsForAuction terms m ps qs curState = ((\<forall>x . x \<in> set qs \<longrightarrow> \<not> member (choice x) (choices curState))
                                                  \<and> (\<forall>x . x \<in> set ps \<longrightarrow> findWithDefault 0 (choice x) (choices curState) > 0)
                                                  \<and> (\<forall>x y . m = Some (x, y) \<longrightarrow> ((lookup (y, token_ada) (accounts curState) = lookup (choice y) (choices curState))
                                                          \<and> (findWithDefault 0 (choice y) (choices curState) > 0)
                                                          \<and> (ChoiceValue (choice y) = x)))
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
      by (metis Auction.choice.simps MList.findWithDefault.elims invariantHoldsForAuction_def)
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
  apply (smt (verit, best) Auction.choice.simps MList.findWithDefault.simps MList.member.simps Option.option.inject Product_Type.prod.inject distinct_append invariantHoldsForAuction_def reduceContractLoopEqualsSettlement)
  apply (smt (verit, best) Auction.choice.simps MList.findWithDefault.simps MList.member.simps Option.option.inject Product_Type.prod.inject distinct_append invariantHoldsForAuction_def reduceContractLoopEqualsSettlement)
  apply (smt (verit, best) Auction.choice.simps MList.findWithDefault.simps MList.member.simps Option.option.inject Product_Type.prod.inject distinct_append invariantHoldsForAuction_def reduceContractLoopEqualsSettlement)
  by (smt (verit, best) Auction.choice.simps MList.findWithDefault.simps MList.member.simps Option.option.inject Product_Type.prod.inject distinct_append invariantHoldsForAuction_def reduceContractLoopEqualsSettlement)
  
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

lemma reduceSettlementUntilQuiescentIsClose : "reductionLoop reducedBefore env curState (settle m terms) wa ef = ContractQuiescent reducedAfter reduceWarns pays newState cont \<Longrightarrow>
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

lemma reduceContractUntilQuiescent_of_contractLoop_indempotent : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                                                  reduceContractUntilQuiescent env state (contractLoop m ps qs terms) = ContractQuiescent False [] [] state ncont \<Longrightarrow>
                                                                  ncont = (contractLoop m ps qs terms) \<or> ncont = Close"
  apply (cases ps)
  apply (cases qs)
    apply blast
  subgoal for h t
    apply (simp only:contractLoop.simps reduceContractUntilQuiescent.simps)
    apply (auto split:ReduceStepResult.splits)
    apply (simp only:Let_def)
    apply (auto split:prod.splits)
    by (metis Semantics.ReduceStepResult.distinct(1) Semantics.ReduceStepResult.distinct(3) Semantics.ReduceStepResult.inject Semantics.reductionLoop.elims reduceSettlementUntilQuiescentIsClose)
    apply (simp only:contractLoop.simps reduceContractUntilQuiescent.simps)
    apply (auto split:ReduceStepResult.splits)
    apply (simp only:Let_def)
    apply (auto split:prod.splits)
    by (metis Semantics.ReduceStepResult.distinct(1) Semantics.ReduceStepResult.distinct(3) Semantics.ReduceStepResult.inject Semantics.reductionLoop.simps reduceSettlementUntilQuiescentIsClose)

lemma reduceContractUntilQuiescent_preserves_invariant : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                                              invariantHoldsForAuction terms m ps qs state \<Longrightarrow>
                                                              reduceContractUntilQuiescent env state (contractLoop m ps qs terms) = ContractQuiescent nreduced [] npays ncurState ncont \<Longrightarrow>
                                                              (ncont = Close \<or> invariantHoldsForAuction terms m ps qs ncurState)"
  using reduceUntilQuiescentIsFixedOrClose by blast

lemma auctionIsSafe_applyCases : "When ca t c = contractLoop nm nps nqs terms \<Longrightarrow>
                                  applyCases env ncurState hi ca = Applied applyWarn newState cont \<Longrightarrow>
                                  invariantHoldsForAuction terms nm nps nqs ncurState \<Longrightarrow>
                                  \<exists>nm nps nqs. cont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs newState"
  sorry

lemma auctionIsSafe_applyInput : "applyInput env ncurState hi ncont = Applied applyWarn newState cont \<Longrightarrow>
                                  ncont = contractLoop nm nps nqs terms \<Longrightarrow> invariantHoldsForAuction terms nm nps nqs ncurState \<Longrightarrow>
                                  cont \<noteq> Close \<Longrightarrow>
                                  \<exists>nm nps nqs. cont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs newState"
  apply (cases ncont)
  apply simp
  apply force
  apply force
  subgoal for ca t c
    apply (simp only:applyInput.simps)
    by (metis Semantics.applyInput.simps(1) auctionIsSafe_applyCases)
  apply force
  by force

lemma applyLoop_of_Close_NoWarnings : "applyAllLoop x env state Close ti wa ef = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow> wa = warnings"
  apply (cases ti)
  apply (smt (z3) List.append.right_neutral List.list.simps(4) Semantics.ApplyAllResult.distinct(3) Semantics.ApplyAllResult.inject Semantics.ReduceResult.exhaust Semantics.ReduceResult.simps(4) Semantics.ReduceResult.simps(5) Semantics.applyAllLoop.simps Semantics.convertReduceWarnings.simps(1) closeIsSafe_reduceContractUntilQuiescent)
  by (smt (z3) List.list.case_eq_if List.list.simps(3) Semantics.ApplyAllResult.simps(3) Semantics.ApplyAllResult.simps(5) Semantics.ApplyResult.simps(5) Semantics.ReduceResult.exhaust Semantics.ReduceResult.simps(4) Semantics.ReduceResult.simps(5) Semantics.applyAllLoop.simps Semantics.applyInput.simps(2) closeIdemp_reduceContractUntilQuiescent)

lemma auctionIsSafe_applyLoop : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                 applyAllLoop contractChanged env fixSta (contractLoop m ps qs terms) inps wa ef = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                 warnings = wa"
  apply (induction contractChanged env fixSta "contractLoop m ps qs terms" inps wa ef arbitrary:m ps qs terms rule:applyAllLoop.induct)
  subgoal for contractChanged env state inputs warningsa paymentsa m ps qs terms
    apply (simp only:applyAllLoop.simps[of contractChanged env state "contractLoop m ps qs terms" inputs warningsa paymentsa])
    apply (cases "reduceContractUntilQuiescent env state (contractLoop m ps qs terms)")
    subgoal for nreduced nreduceWarns npays ncurState ncont
      apply (simp only:ReduceResult.case)
      apply (subgoal_tac "nreduceWarns = []")
      subgoal
      apply (cases inputs)
      apply simp
      subgoal for hi ti
        apply (cases "ps = [] \<and> qs = []")
        subgoal
          using reduceSettlementUntilQuiescentIsClose by fastforce
        subgoal
          apply (cases "applyInput env ncurState hi ncont")
          apply (simp only:list.case ApplyResult.case)
          subgoal for applyWarn newState cont
            apply (cases "ncont = Close")
            apply simp
            apply (cases "cont = Close")
            apply (metis Semantics.convertApplyWarning.simps(1) Semantics.convertReduceWarnings.simps(1) append_Nil2 applyLoop_of_Close_NoWarnings reduceUntilQuiescentApplyInput_isSafe)
            apply (subgoal_tac "applyWarn = ApplyNoWarning")
            subgoal
              apply (subgoal_tac "\<exists> nm nps nqs. (cont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs newState)")
              subgoal
                using Semantics.convertApplyWarning.simps(1) Semantics.convertReduceWarnings.simps(1) by blast
              subgoal
                apply (subgoal_tac "\<exists>nm nps nqs. (ncont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs ncurState)")
                subgoal
                  by (meson auctionIsSafe_applyInput)
                subgoal
                  by (metis reduceUntilQuiescentIsFixedOrClose)
                  done
                done
              by (meson reduceUntilQuiescentApplyInput_isSafe)
            by force
          done
        done
      by (meson auctionIsSafe_reduceContractUntilQuiescent)
    by force
  done

lemma auctionIsSafe_applyAllInputs : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                      applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                      warnings = []"
  apply (simp only:applyAllInputs.simps)
  by (simp add: auctionIsSafe_applyLoop)


lemma applyLoopPreservesInvariant : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
    applyAllLoop contractChanged env fixSta (contractLoop m ps qs terms) inps wa ef = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
    cont \<noteq> Close \<Longrightarrow> \<exists>nm nps nqs. cont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs newState"
  sorry

lemma applyAllInputsPreservesInvariant : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                              applyAllInputs env fixSta (contractLoop m ps qs terms) inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow>
                                              cont \<noteq> Close \<Longrightarrow>
                                               (\<exists> nm nps nqs . cont = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs newState)"
  apply (simp only:applyAllInputs.simps)
  by (simp add: applyLoopPreservesInvariant)

lemma fixingIntervalPreservesInvariant : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                          fixInterval (low, high) sta = IntervalTrimmed env fixSta \<Longrightarrow> 
                                          invariantHoldsForAuction terms m ps qs fixSta"
  apply (simp only:fixInterval.simps Let_def)
  apply (split if_split_asm)
  apply blast
  apply (split if_split_asm)
  apply force
  apply (cases sta)
  apply (cases fixSta)
  using invariantHoldsForAuction_def by force

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

lemma computeTransactionPreservesInvariant : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                              computeTransaction tra sta (contractLoop m ps qs terms) = TransactionOutput \<lparr>txOutWarnings = txOutWarningsa, txOutPayments = txOutPaymentsa, txOutState = txOutStatea, txOutContract = txOutContracta\<rparr> \<Longrightarrow>
                                              txOutContracta \<noteq> Close \<Longrightarrow>
                                               (\<exists> nm nps nqs . txOutContracta = contractLoop nm nps nqs terms \<and> invariantHoldsForAuction terms nm nps nqs txOutStatea)"
  apply (simp only:computeTransaction.simps Let_def)
  apply (cases "fixInterval (interval tra) sta")
   apply (simp only:IntervalResult.case)
     subgoal for env fixSta
       apply (cases "applyAllInputs env fixSta (contractLoop m ps qs terms) (inputs tra)")
         apply (simp only:ApplyAllResult.case)
         apply (metis Semantics.TransactionOutput.inject(1) Semantics.TransactionOutput.simps(4) Semantics.TransactionOutputRecord.ext_inject applyAllInputsPreservesInvariant)
        apply simp
       by simp
     by simp

lemma applyLoopOfCloseIsClose : "applyAllLoop x env fixSta Close inps wa err = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow> cont = Close"
  apply (induction inps arbitrary:x env fixSta inps wa err)
  subgoal for x env fixSta inps wa err
    apply (simp only:applyAllLoop.simps[of x env fixSta Close inps wa err])
    apply (cases "reduceContractUntilQuiescent env fixSta Close")
    subgoal for reduced reduceWarns pays curState cont
      apply (simp only:ReduceResult.case)
    by (metis (no_types, lifting) List.list.simps(4) List.list.simps(5) Semantics.ApplyAllResult.distinct(1) Semantics.ApplyAllResult.inject Semantics.ApplyResult.simps(5) Semantics.applyInput.simps(2) Semantics.reduceContractUntilQuiescent.elims closeIdemp_reductionLoop neq_Nil_conv)
  by simp
  by blast

lemma applyAllInputsOfCloseIsClose : "applyAllInputs env fixSta Close inps = ApplyAllSuccess reduced warnings payments newState cont \<Longrightarrow> cont = Close"
  by (simp add: applyLoopOfCloseIsClose)

lemma playTraceOfClose_isSafe : "playTraceAux \<lparr>txOutWarnings = wa, txOutPayments = ef, txOutState = sta, txOutContract = Close\<rparr> t = TransactionOutput transResRec \<Longrightarrow> txOutWarnings transResRec = wa"
  apply (induction t arbitrary:wa ef sta transResRec)
  apply auto[1]
  subgoal for a t wa ef sta transResRec
    apply (simp only:playTraceAux.simps)
    apply (simp only:computeTransaction.simps)
    apply (cases "fixInterval (interval a) sta")
     apply (simp only:IntervalResult.case)
    subgoal for env fixSta
      apply (cases "applyAllInputs env fixSta Close (inputs a)")
      subgoal for reduced warnings payments newState cont
        apply (simp only:ApplyAllResult.case Let_def)
        apply (split if_split_asm)
         apply simp
        apply (simp only:TransactionOutput.case)
        apply (simp del:playTraceAux.simps applyAllInputs.simps)
        by (metis append_self_conv applyAllInputsOfCloseIsClose closeIsSafe_applyAllInputs)
       apply simp
      by force
    by simp
  done

lemma auctionIsSafe_playTraceAux : "invariantHoldsForAuction terms m ps qs sta \<Longrightarrow>
                                    playTraceAux \<lparr> txOutWarnings = Nil
                                                 , txOutPayments = ef
                                                 , txOutState = sta
                                                 , txOutContract = contractLoop m ps qs terms \<rparr> l = TransactionOutput transResRec \<Longrightarrow>
                                    txOutWarnings transResRec = []"
  apply (induction "\<lparr> txOutWarnings = Nil
                    , txOutPayments = ef
                    , txOutState = sta
                    , txOutContract = contractLoop m ps qs terms \<rparr>" l arbitrary:m ps qs sta ef transResRec rule:playTraceAux.induct)
  subgoal for m ps qs sta ef transResRec
    by auto
    subgoal for warnings payments state cont h t m ps qs sta ef transResRec
      apply (simp only:playTraceAux.simps(2)[of "[]" "ef" "sta" "contractLoop m ps qs terms" "h" "t"] Let_def)
      apply (cases "computeTransaction h sta (contractLoop m ps qs terms)")
       apply (simp only:TransactionOutput.case)
      subgoal for x2
        apply (cases x2)
        subgoal for txOutWarningsa txOutPaymentsa txOutStatea txOutContracta
          apply (cases "txOutContracta = Close")
           apply (metis Semantics.TransactionOutputRecord.update_convs(1) Semantics.TransactionOutputRecord.update_convs(2) auctionIsSafe_computeTransaction eq_Nil_appendI playTraceOfClose_isSafe)
          by (smt (verit, ccfv_threshold) List.append.right_neutral Semantics.TransactionOutputRecord.ext_inject Semantics.TransactionOutputRecord.update_convs(1) Semantics.TransactionOutputRecord.update_convs(2) auctionIsSafe_computeTransaction computeTransactionPreservesInvariant)
        done
      by force
    done

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
