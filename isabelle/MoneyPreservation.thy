theory MoneyPreservation
imports Semantics PositiveAccounts
begin

fun moneyInPayment :: "Payment \<Rightarrow> int" where
"moneyInPayment (Payment _ x) = x"

fun moneyInReduceEffect :: "ReduceEffect \<Rightarrow> int" where
"moneyInReduceEffect (ReduceWithPayment p) = moneyInPayment p" |
"moneyInReduceEffect ReduceNoPayment = 0"

fun moneyInAccounts :: "(AccountId \<times> Money) list \<Rightarrow> int" where
"moneyInAccounts Nil = 0" |
"moneyInAccounts (Cons (_, m) rest) = m + moneyInAccounts rest"

fun moneyInState :: "State \<Rightarrow> int" where
"moneyInState state = moneyInAccounts (accounts state)"

fun moneyInReduceStepResult :: "State \<Rightarrow> ReduceStepResult \<Rightarrow> int" where
"moneyInReduceStepResult _ (Reduced _ reduceEffect state _) =
   moneyInReduceEffect reduceEffect + moneyInState state" |
"moneyInReduceStepResult state NotReduced = moneyInState state" |
"moneyInReduceStepResult state AmbiguousSlotIntervalReductionError = moneyInState state"

fun moneyInRefundOneResult :: "(AccountId \<times> Money) list \<Rightarrow>
                               ((Party \<times> Money) \<times> ((AccountId \<times> Money) list)) option \<Rightarrow> int" where
"moneyInRefundOneResult accs None = moneyInAccounts accs" |
"moneyInRefundOneResult _ (Some ((_, m), newAccs)) = m + moneyInAccounts newAccs"

fun moneyInPayments :: "Payment list \<Rightarrow> int" where
"moneyInPayments (Cons h t) = moneyInPayment h + moneyInPayments t" |
"moneyInPayments Nil = 0"

lemma moneyInPayments_rev_cons : "moneyInPayments (h # payments) = moneyInPayments (payments @ [h])"
  apply (induction payments)
  by auto

lemma moneyInPayments_works_on_rev : "moneyInPayments payments = moneyInPayments (rev payments)"
  apply (induction payments)
  apply simp
  using moneyInPayments_rev_cons by auto

fun moneyInReduceResult :: "Payment list \<Rightarrow> State \<Rightarrow> ReduceResult \<Rightarrow> int" where
"moneyInReduceResult pa sta (ContractQuiescent wa newPa newSta cont) = moneyInState newSta + moneyInPayments newPa" |
"moneyInReduceResult pa sta RRAmbiguousSlotIntervalError = moneyInState sta + moneyInPayments pa"

fun moneyInInput :: "Input \<Rightarrow> int" where
"moneyInInput (IDeposit accId party money) = max 0 money" |
"moneyInInput (IChoice choId val) = 0" |
"moneyInInput INotify = 0"

fun moneyInInputs :: "Input list \<Rightarrow> int" where
"moneyInInputs (Cons head tail) = moneyInInput head + moneyInInputs tail" |
"moneyInInputs Nil = 0"

fun moneyInApplyResult :: "State \<Rightarrow> Input \<Rightarrow> ApplyResult \<Rightarrow> int" where
"moneyInApplyResult state inp (Applied warns newState newCont) = moneyInState newState" |
"moneyInApplyResult state inp ApplyNoMatchError = moneyInState state + moneyInInput inp"

fun moneyInApplyAllResult :: "State \<Rightarrow> Input list \<Rightarrow> Payment list \<Rightarrow> ApplyAllResult \<Rightarrow> int" where
"moneyInApplyAllResult state inps pa (ApplyAllSuccess newWa newPa newSta newCont) =
  moneyInState newSta + moneyInPayments newPa" |
"moneyInApplyAllResult state inps pa ApplyAllNoMatchError =
  moneyInState state + moneyInInputs inps + moneyInPayments pa" |
"moneyInApplyAllResult state inps pa ApplyAllAmbiguousSlotIntervalError =
  moneyInState state + moneyInInputs inps + moneyInPayments pa"

fun moneyInTransactionOutput :: "State \<Rightarrow> Input list \<Rightarrow> TransactionOutput \<Rightarrow> int" where
"moneyInTransactionOutput st inp (TransactionOutput txOut) = moneyInState (txOutState txOut) + moneyInPayments (txOutPayments txOut)" |
"moneyInTransactionOutput st inp (TransactionError te) = moneyInState st + moneyInInputs inp"

fun inputsFromTransactions :: "Transaction list \<Rightarrow> Input list" where
"inputsFromTransactions (Cons head tail) = (inputs head) @ (inputsFromTransactions tail)" |
"inputsFromTransactions Nil = Nil"

fun moneyInTransactions :: "Transaction list \<Rightarrow> int" where
"moneyInTransactions traList = moneyInInputs (inputsFromTransactions traList)"

fun moneyInPlayTraceResult :: "Transaction list \<Rightarrow> TransactionOutput \<Rightarrow> int" where
"moneyInPlayTraceResult traList (TransactionOutput txOut) = moneyInState (txOutState txOut) + moneyInPayments (txOutPayments txOut)" |
"moneyInPlayTraceResult traList (TransactionError te) = moneyInTransactions traList"

lemma refundOne_preserves_money :
  "allAccountsPositive accs \<Longrightarrow>
   moneyInAccounts accs = moneyInRefundOneResult accs (refundOne accs)"
  apply (induction accs)
  apply simp
  subgoal for h t
    apply (cases h)
    apply (simp only:refundOne.simps)
    subgoal for part mon
      apply (cases "0 < mon")
      apply simp
      using allAccountsPositiveMeansFirstIsPositive by blast
    done
  done

lemma updateMoneyInAccount_no_match :
  "valid_map ((thisAccId, money) # tail) \<Longrightarrow>
   accId \<noteq> thisAccId \<Longrightarrow>
   y \<ge> 0 \<Longrightarrow>
   allAccountsPositive ((thisAccId, money) # tail) \<Longrightarrow>
   moneyInAccounts (updateMoneyInAccount accId y ((thisAccId, money) # tail))
   = money + moneyInAccounts (updateMoneyInAccount accId y tail)"
  apply (simp only:updateMoneyInAccount.simps)
  apply (cases "y \<le> 0")
  apply (simp only:bool.case if_True moneyInAccounts.simps)
  using delete_step apply fastforce
  apply (simp only:bool.case if_False)
  by (smt MList.insert.simps(1) MList.insert.simps(2) MList.remove_from_middle leI le_less_trans moneyInAccounts.simps(2) not_less_iff_gr_or_eq refundOne.cases)

lemma moneyInAccount_head_no_match :
  "valid_map ((thisAccId, money) # tail) \<Longrightarrow>
   accId \<noteq> thisAccId \<Longrightarrow>
   moneyInAccount accId ((thisAccId, money) # tail) = moneyInAccount accId tail"
  apply (simp only:moneyInAccount.simps)
  by (meson findWithDefault_step)

lemma updateMoneyInAccount_money :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   moneyToPay \<ge> 0 \<Longrightarrow>
   let balance = moneyInAccount accId accs;
       paidMoney = min balance moneyToPay in
   moneyInAccounts (updateMoneyInAccount accId (balance - paidMoney) accs) =
   moneyInAccounts accs - paidMoney"
  apply (induction accs arbitrary:accId)
  apply simp
  subgoal for head tail accId
    apply (cases head)
    subgoal for thisAccId money
      apply (cases "accId = thisAccId")
      apply simp
      apply linarith
      apply (simp only:Let_def)
      apply (subst updateMoneyInAccount_no_match[of thisAccId money tail accId 
                                                    "(moneyInAccount accId ((thisAccId, money) # tail)
                                                      - min (moneyInAccount accId ((thisAccId, money) # tail)) moneyToPay)"])
      apply blast
      apply blast
      apply linarith
      apply blast
      apply (simp only:moneyInAccounts.simps moneyInAccount_head_no_match)
      by (metis MList.sublist_valid add_diff_eq allAccountsPositiveMeansAllAccountsInTailArePositive findWithDefault_step moneyInAccount.simps)
    done
  done

lemma updateMoneyInAccount_money2_aux :
  "valid_map ((thisAccId, money) # tail) \<Longrightarrow>
   allAccountsPositive ((thisAccId, money) # tail) \<Longrightarrow>
   moneyToPay \<ge> 0 \<Longrightarrow>
   moneyInAccount thisAccId ((thisAccId, money) # tail) + moneyToPay > 0"
  apply (simp only:moneyInAccount.simps findWithDefault.simps lookup.simps refl if_True option.case)
  using add_pos_nonneg allAccountsPositiveMeansFirstIsPositive by blast

lemma updateMoneyInAccount_money2 :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   moneyToPay \<ge> 0 \<Longrightarrow>
   let balance = moneyInAccount accId accs in
   moneyInAccounts (updateMoneyInAccount accId (balance + moneyToPay) accs) =
   moneyInAccounts accs + moneyToPay"
  apply (induction accs arbitrary:accId)
  apply simp
  subgoal for head tail accId
    apply (cases head)
    subgoal for thisAccId money
      apply (cases "accId = thisAccId")
      apply (simp only:moneyInAccounts.simps updateMoneyInAccount.simps)
      apply (cases "moneyInAccount thisAccId ((thisAccId, money) # tail) + moneyToPay \<le> 0")
      apply (meson not_less updateMoneyInAccount_money2_aux)
      apply simp
      apply (simp only:moneyInAccounts.simps moneyInAccount_head_no_match)
      by (smt MList.sublist_valid allAccountsPositiveMeansAllAccountsInTailArePositive moneyInAccount_head_no_match updateMoneyInAccount.simps updateMoneyInAccount_no_match)
    done
  done

lemma giveMoneyToParty_does_not_modify_accs :
  "(snd (giveMoney (Party p) paidMoney accs)) = accs"
  by simp

lemma removeMoneyFromAccount_preservation :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   moneyToPay \<ge> 0 \<Longrightarrow>
   balance = moneyInAccount accId accs \<Longrightarrow>
   paidMoney = min balance moneyToPay \<Longrightarrow>
   moneyInAccounts (snd (giveMoney (Party p) paidMoney (updateMoneyInAccount accId (balance - paidMoney) accs))) =
   moneyInAccounts accs - paidMoney"
  by (metis giveMoneyToParty_does_not_modify_accs updateMoneyInAccount_money)

lemma state_account_red : "accounts (state\<lparr> accounts := a\<rparr>) = a"
  by simp

lemma reduceContractStep_preserves_money_acc_to_party :
  "valid_map (accounts state) \<Longrightarrow>
   allAccountsPositive (accounts state) \<Longrightarrow>
   moneyToPay > 0 \<Longrightarrow>
   balance = moneyInAccount accId (accounts state) \<Longrightarrow>
   moneyToPay = evalValue env state val \<Longrightarrow>
   paidMoney = min balance moneyToPay \<Longrightarrow>
   moneyInAccounts (accounts state) =
   moneyInReduceStepResult state
    (case giveMoney (Party x2) paidMoney
             (updateMoneyInAccount accId (balance - paidMoney) (accounts state)) of
     (payment, finalAccs) \<Rightarrow>
       Reduced (if paidMoney < moneyToPay
                then ReducePartialPay accId (Party x2) paidMoney moneyToPay
                else ReduceNoWarning)
               payment (state\<lparr>accounts := finalAccs\<rparr>) cont)"
  apply (cases "giveMoney (Party x2) paidMoney
                          (updateMoneyInAccount accId (balance - paidMoney) (accounts state))")
  subgoal for a b
    apply (cases a)
    apply simp
    subgoal for x2a
      apply (cases x2a)
      apply (simp only:prod.case moneyInReduceStepResult.simps moneyInReduceEffect.simps)
      apply (simp only:moneyInState.simps "state_account_red")
      by (metis add_diff_cancel_left' add_diff_eq giveMoney.simps(1) le_less moneyInPayment.simps moneyInReduceEffect.simps(1) prod.inject updateMoneyInAccount_money)
    done
  done

lemma allAccountsPositive_implies_one_is_positive_aux :
  "positiveMoneyInAccountOrNoAccount accId accs \<Longrightarrow> MList.lookup accId accs = Some x \<Longrightarrow> x > 0"
  by simp

lemma allAccountsPositive_implies_one_is_positive :
  "allAccountsPositive accs \<Longrightarrow> MList.lookup accId accs = Some x \<Longrightarrow> x > 0"
  using allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount allAccountsPositive_implies_one_is_positive_aux by blast

lemma addMoneyToAccountIf_ge_zero :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   0 < moneyToPay \<Longrightarrow>
   min (moneyInAccount accId accs) moneyToPay \<noteq> 0 \<Longrightarrow>
   min (moneyInAccount accId accs) moneyToPay > 0"
  apply (simp only:moneyInAccount.simps findWithDefault.simps)
  apply (cases "lookup accId accs")
  apply simp
  using allAccountsPositive_implies_one_is_positive by auto

lemma transferMoneyBetweenAccounts_preserves_aux :
 "valid_map accs \<Longrightarrow>
  allAccountsPositive accs \<Longrightarrow>
  0 < moneyToPay \<Longrightarrow>
  valTrans = min (moneyInAccount accId accs) moneyToPay \<Longrightarrow>
  interAccs = updateMoneyInAccount accId (moneyInAccount accId accs - valTrans) accs \<Longrightarrow>
  moneyInAccounts (updateMoneyInAccount accId (moneyInAccount accId accs - valTrans) accs)
  = moneyInAccounts accs - valTrans"
  by (metis (full_types) min.cobounded2 min.strict_order_iff updateMoneyInAccount_money)

lemma transferMoneyBetweenAccounts_preserves_aux2 :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   valid_map interAccs \<Longrightarrow>
   allAccountsPositive interAccs \<Longrightarrow>
   0 < moneyToPay \<Longrightarrow>
   valTrans = min (moneyInAccount accId accs) moneyToPay \<Longrightarrow>
   moneyInAccounts (updateMoneyInAccount acc (moneyInAccount acc interAccs + valTrans) interAccs) =
   moneyInAccounts interAccs + valTrans"
  by (metis (full_types) addMoneyToAccountIf_ge_zero min.order_iff min.strict_order_iff not_less updateMoneyInAccount_money2)

lemma transferMoneyBetweenAccounts_preserves_aux3 :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   0 < moneyToPay \<Longrightarrow>
   valTrans = min (moneyInAccount accId accs) moneyToPay \<Longrightarrow>
   interAccs = updateMoneyInAccount accId (moneyInAccount accId accs - valTrans) accs \<Longrightarrow>
   moneyInAccounts (updateMoneyInAccount acc (moneyInAccount acc interAccs + valTrans) interAccs) =
   moneyInAccounts accs"
  apply (subst transferMoneyBetweenAccounts_preserves_aux2[of accs interAccs moneyToPay valTrans accId acc])
  apply blast
  apply blast
  using updateMoneyInAccount_preserves_valid_map apply blast
  apply (smt MList_delete_preserves_gtZero allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive updateMoneyInAccount.simps updateMoneyInAccount_gtZero updateMoneyInAccount_preserves_valid_map)
  apply blast
  apply blast
  by (metis (full_types) diff_add_cancel not_less not_less_iff_gr_or_eq updateMoneyInAccount_money)

lemma transferMoneyBetweenAccounts_preserves :
  "valid_map accs \<Longrightarrow>
   allAccountsPositive accs \<Longrightarrow>
   moneyToPay > 0 \<Longrightarrow>
   balance = moneyInAccount accId accs \<Longrightarrow>
   paidMoney = min balance moneyToPay \<Longrightarrow>
   moneyInAccounts (snd (giveMoney (Account acc) paidMoney (updateMoneyInAccount accId (balance - paidMoney) accs))) =
   moneyInAccounts accs"
  apply (simp only:giveMoney.simps addMoneyToAccount.simps Let_def)
  apply (cases "min (moneyInAccount accId accs) moneyToPay = 0")
  apply (simp only:bool.case if_True snd_def prod.case)
  apply (simp only:Orderings.preorder_class.order_refl if_True)
  apply (metis diff_zero min.commute min.right_idem order_refl updateMoneyInAccount_money)
  using addMoneyToAccountIf_ge_zero transferMoneyBetweenAccounts_preserves_aux3 by fastforce

lemma reduceContractStep_preserves_money_acc_to_acc_aux :
  "validAndPositive_state state \<Longrightarrow>
   econt = Pay accId (Account x1) val cont \<Longrightarrow>
   \<not> evalValue env state val \<le> 0 \<Longrightarrow>
   moneyToPay = evalValue env state val \<Longrightarrow>
   balance = moneyInAccount accId (accounts state) \<Longrightarrow>
   paidMoney = min balance moneyToPay \<Longrightarrow>
   giveMoney (Account x1) paidMoney
    (updateMoneyInAccount accId
      (moneyInAccount accId (accounts state) - paidMoney) (accounts state)) =
   rgm \<Longrightarrow> moneyInAccounts (snd rgm) = moneyInAccounts (accounts state)"
  using transferMoneyBetweenAccounts_preserves by auto

lemma reduceContractStep_preserves_money_acc_to_acc :
  "valid_state state \<Longrightarrow>
   allAccountsPositiveState state \<Longrightarrow>
   econt = Pay accId payee val cont \<Longrightarrow>
   \<not> moneyToPay \<le> 0 \<Longrightarrow>
   payee = Account x1 \<Longrightarrow>
   moneyToPay = evalValue env state val \<Longrightarrow>
   balance = moneyInAccount accId (accounts state) \<Longrightarrow>
   paidMoney = min balance moneyToPay \<Longrightarrow>
   moneyInAccounts (accounts state)
    = moneyInReduceStepResult state
          (case giveMoney payee paidMoney (updateMoneyInAccount accId (balance - paidMoney) (accounts state)) of
                (payment, finalAccs) \<Rightarrow> Reduced wa payment (state\<lparr>accounts := finalAccs\<rparr>) cont)"
  apply (cases "giveMoney payee paidMoney (updateMoneyInAccount accId (balance - paidMoney) (accounts state))")
  apply (simp del:valid_map.simps allAccountsPositive.simps moneyInAccount.simps moneyInAccounts.simps giveMoney.simps updateMoneyInAccount.simps)
  subgoal for a b
    apply (cases a)
    apply (simp only:moneyInReduceEffect.simps)
    using transferMoneyBetweenAccounts_preserves apply auto[1]
    by simp
  done

lemma reduceContractStep_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state = moneyInReduceStepResult state (reduceContractStep env state cont)"
  apply (cases cont)
  apply (simp only: reduceContractStep.simps)
  apply (cases "refundOne (accounts state)")
  apply simp
  subgoal for head
    apply (cases head)
    subgoal for part mon
      apply (cases part)
      apply (simp del:refundOne.simps moneyInReduceStepResult.simps allAccountsPositiveState.simps)
      by (simp add: refundOne_preserves_money)
    done
  apply (simp only:reduceContractStep.simps)
  subgoal for accId payee val cont
    apply (cases "evalValue env state val \<le> 0")
    apply simp
    apply (simp del:validAndPositive_state.simps valid_map.simps allAccountsPositive.simps moneyInAccount.simps moneyInAccounts.simps giveMoney.simps updateMoneyInAccount.simps)
    apply (cases payee)
    apply (simp only:Let_def)
    subgoal for x1
      using reduceContractStep_preserves_money_acc_to_acc_aux by force
    apply (simp only:Let_def)
    subgoal for x2
      using reduceContractStep_preserves_money_acc_to_party by auto
    done
    apply simp
  subgoal for cases timeout contr
    apply (simp only:reduceContractStep.simps)
    apply (cases "snd (slotInterval env) < timeout")
    apply (simp add: case_prod_beta')
    apply (cases "timeout \<le> fst (slotInterval env)")
    apply (simp add: case_prod_beta')
    by (simp add: case_prod_beta')
  subgoal for valId val cont
    apply (simp only:reduceContractStep.simps)
    by (metis State.simps(1) State.simps(8) State.surjective add.left_neutral moneyInReduceEffect.simps(2) moneyInReduceStepResult.simps(1) moneyInState.simps)
  done

lemma applyCases_preserves_money_aux :
  "validAndPositive_state state \<Longrightarrow>
   money > 0 \<Longrightarrow>
   moneyInState state + moneyInInput (IDeposit accId2 party2 money) =
   moneyInState (state\<lparr>accounts := updateMoneyInAccount accId2 (moneyInAccount accId2 (accounts state) + money) (accounts state)\<rparr>)"
  apply (simp only:moneyInState.simps state_account_red)
  by (smt allAccountsPositiveState.simps moneyInInput.simps(1) updateMoneyInAccount_money2 validAndPositive_state.simps valid_state.simps)

lemma applyCases_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInInput inp = moneyInApplyResult state inp (applyCases env state inp caseList)"
  apply (induction env state inp caseList rule:applyCases.induct)
  subgoal for env state accId1 party1 money accId2 party2 val cont rest
    apply (simp only:applyCases.simps)
    apply (cases "accId1 = accId2 \<and> party1 = party2 \<and> money = evalValue env state val")
    apply (auto simp del:evalValue.simps moneyInState.simps moneyInInput.simps moneyInApplyResult.simps validAndPositive_state.simps updateMoneyInAccount.simps moneyInAccount.simps)
    apply (simp only:Let_def moneyInApplyResult.simps)
    apply (cases "evalValue env state val \<le> 0")
    apply simp
    apply (simp only:bool.case if_False)
    using applyCases_preserves_money_aux not_le by blast
  subgoal for env state choId1 choice choId2 bounds cont rest
    by simp
  by simp_all

lemma applyInput_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInInput inp = moneyInApplyResult state inp (applyInput env state inp cont)"
  apply (cases cont)                                                        
  by (simp_all add:applyCases_preserves_money del:validAndPositive_state.simps moneyInState.simps)

lemma reductionLoop_preserves_money_NoPayment_not_ReduceNoWarning :
  "warning \<noteq> ReduceNoWarning \<Longrightarrow>
   x = warning # warnings \<Longrightarrow>
   (validAndPositive_state newState \<Longrightarrow>
    moneyInState newState + moneyInPayments payments = moneyInReduceResult xa newState (reductionLoop env newState ncontract x xa)) \<Longrightarrow>
    validAndPositive_state state \<Longrightarrow>
    reduceContractStep env state contract = Reduced warning ReduceNoPayment newState ncontract \<Longrightarrow>
    moneyInState state + moneyInPayments payments = moneyInReduceResult payments state (reductionLoop env newState ncontract x xa)"
  by (metis ReduceResult.exhaust add.left_neutral moneyInReduceEffect.simps(2) moneyInReduceResult.simps(1) moneyInReduceResult.simps(2) moneyInReduceStepResult.simps(1) reduceContractStep_preserves_money reduceContractStep_preserves_validAndPositive_state)

lemma reductionLoop_preserves_money_NoPayment :
  "x = (if warning = ReduceNoWarning then warnings else warning # warnings) \<Longrightarrow>
   (validAndPositive_state newState \<Longrightarrow>
    moneyInState newState + moneyInPayments payments = moneyInReduceResult xa newState (reductionLoop env newState ncontract x xa)) \<Longrightarrow>
    validAndPositive_state state \<Longrightarrow>
    reduceContractStep env state contract = Reduced warning ReduceNoPayment newState ncontract \<Longrightarrow>
    moneyInState state + moneyInPayments payments = moneyInReduceResult payments state (reductionLoop env newState ncontract x xa)"
  by (metis ReduceResult.exhaust add.left_neutral moneyInReduceEffect.simps(2) moneyInReduceResult.simps(1) moneyInReduceResult.simps(2) moneyInReduceStepResult.simps(1) reduceContractStep_preserves_money reduceContractStep_preserves_validAndPositive_state)

lemma reductionLoop_preserves_money_Payment_not_ReduceNoWarning :
  "\<And>x2.
     (\<And>x xa.
      x = reWa # warnings \<Longrightarrow>
      xa = (case ReduceWithPayment x2 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) \<Longrightarrow>
      validAndPositive_state reSta \<Longrightarrow>
      moneyInState reSta +
      moneyInPayments (case ReduceWithPayment x2 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) =
      moneyInReduceResult (case ReduceWithPayment x2 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments) reSta
       (reductionLoop env reSta reCont (if reWa = ReduceNoWarning then warnings else reWa # warnings)
         (case ReduceWithPayment x2 of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments))) \<Longrightarrow>
   validAndPositive_state state \<Longrightarrow>
   reduceContractStep env state contract = Reduced reWa (ReduceWithPayment x2) reSta reCont \<Longrightarrow>
   reEf = ReduceWithPayment x2 \<Longrightarrow>
   reWa \<noteq> ReduceNoWarning \<Longrightarrow>
   moneyInState state + moneyInPayments payments =
   moneyInReduceResult payments state (reductionLoop env reSta reCont (reWa # warnings) (x2 # payments))"
  by (smt ReduceEffect.simps(5) ReduceResult.exhaust moneyInPayments.simps(1) moneyInReduceEffect.simps(1) moneyInReduceResult.simps(1) moneyInReduceResult.simps(2) moneyInReduceStepResult.simps(1) reduceContractStep_preserves_money reduceContractStep_preserves_validAndPositive_state)

lemma reductionLoop_preserves_money_Payment :
  "\<And>x2. (\<And>x xa.
              x = warnings \<Longrightarrow>
              xa = x2 # payments \<Longrightarrow>
              validAndPositive_state reSta \<Longrightarrow>
              moneyInState reSta +
              moneyInPayments xa =
              moneyInReduceResult xa reSta (reductionLoop env reSta reCont warnings xa)) \<Longrightarrow>
          validAndPositive_state state \<Longrightarrow>
          reduceContractStep env state contract = Reduced ReduceNoWarning (ReduceWithPayment x2) reSta reCont \<Longrightarrow>
          reEf = ReduceWithPayment x2 \<Longrightarrow>
          reWa = ReduceNoWarning \<Longrightarrow>
          moneyInState state + moneyInPayments payments =
          moneyInReduceResult payments state (reductionLoop env reSta reCont warnings (x2 # payments))"
  by (smt ReduceEffect.simps(5) ReduceResult.exhaust moneyInPayments.simps(1) moneyInReduceEffect.simps(1) moneyInReduceResult.simps(1) moneyInReduceResult.simps(2) moneyInReduceStepResult.simps(1) reduceContractStep_preserves_money reduceContractStep_preserves_validAndPositive_state)

lemma reductionLoop_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInPayments pa = moneyInReduceResult pa state (reductionLoop env state cont wa pa)"
  apply (induction env state cont wa pa rule:reductionLoop.induct)
  subgoal for env state contract warnings payments
    apply (simp only:reductionLoop.simps[of env state contract warnings payments])
    apply (cases "reduceContractStep env state contract")
    subgoal for reWa reEf reSta reCont
      apply (cases reEf)
      apply (cases "reWa = ReduceNoWarning")
      apply (simp only:Let_def ReduceResult.case ReduceEffect.case ReduceWarning.case)
      apply (simp del:validAndPositive_state.simps moneyInState.simps reductionLoop.simps)
      apply (metis reductionLoop_preserves_money_NoPayment)
      apply (simp only:Let_def ReduceResult.case ReduceEffect.case ReduceWarning.case)
      apply (simp del:validAndPositive_state.simps moneyInState.simps reductionLoop.simps)
      using reductionLoop_preserves_money_NoPayment_not_ReduceNoWarning apply auto[1]
      apply (cases "reWa = ReduceNoWarning")
      apply (simp only:Let_def ReduceResult.case ReduceEffect.case ReduceWarning.case)
      apply (simp del:validAndPositive_state.simps moneyInState.simps reductionLoop.simps)
      apply (metis ReduceEffect.simps(5) reductionLoop_preserves_money_Payment)
      apply (simp only:Let_def ReduceResult.case ReduceEffect.case ReduceWarning.case)
      apply (simp del:validAndPositive_state.simps ReduceEffect.simps moneyInState.simps reductionLoop.simps)
      apply (simp only:ReduceEffect.case)
      by (metis reductionLoop_preserves_money_Payment_not_ReduceNoWarning)
    using moneyInPayments_works_on_rev apply force
    by simp
  done
lemma reduceContractUntilQuiescent_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state = moneyInReduceResult [] state (reduceContractUntilQuiescent env state cont)"
  using reductionLoop_preserves_money by auto

lemma moneyInInputs_distrib : "moneyInInputs (a @ b) = moneyInInputs a + moneyInInputs b"
  apply (induction a)
  by simp_all

lemma moneyInTransactions_cons : "moneyInTransactions (a # b) = moneyInTransactions [a] + moneyInTransactions b"
  apply simp
  by (simp add: moneyInInputs_distrib)

lemma moneyInPayments_distrib : "moneyInPayments (a @ b) = moneyInPayments a + moneyInPayments b"
  apply (induction a)
  by simp_all

lemma applyAllLoop_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInInputs inp + moneyInPayments pa
    = moneyInApplyAllResult state inp pa (applyAllLoop env state cont inp wa pa)"
  apply (induction env state cont inp wa pa rule:applyAllLoop.induct)
  subgoal for env state contract inputs warnings payments
    apply (simp only:applyAllLoop.simps[of env state contract inputs warnings payments])
    apply (cases "reduceContractUntilQuiescent env state contract")
    subgoal for redWa redPa redSta redCont
      apply (simp only:ReduceResult.simps)
      apply (cases "inputs")
      apply (simp only:list.simps)
      apply (simp only:moneyInApplyAllResult.simps moneyInInputs.simps)
      apply (smt moneyInPayments_distrib moneyInReduceResult.simps(1) reduceContractUntilQuiescent_preserves_money)
      apply (simp only:list.simps)
      subgoal for head tail
        apply (cases "applyInput env redSta head redCont")
        apply (simp only:ApplyResult.simps moneyInApplyAllResult.simps)
        subgoal for appWarn appState appCont
          apply (cases "(applyAllLoop env appState appCont tail (warnings @ convertReduceWarnings redWa @ convertApplyWarning appWarn) (payments @ redPa))")
          apply (smt applyInput_preserves_money applyInput_preserves_preserves_validAndPositive_state moneyInApplyAllResult.simps(1) moneyInApplyResult.simps(1) moneyInInputs.simps(1) moneyInPayments_distrib moneyInReduceResult.simps(1) reduceContractUntilQuiescent_preserves_money reduceContractUntilQuiescent_preserves_validAndPositive_state)
          by simp_all
        by simp
      done
    by simp
  done

lemma applyAllInputs_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInInputs inp
    = moneyInApplyAllResult state inp [] (applyAllInputs env state contract inp)"
  using applyAllLoop_preserves_money by auto

lemma fixInterval_preserves_money :
  "fixInterval inte state = IntervalTrimmed env newState \<Longrightarrow>
   moneyInState state = moneyInState newState"
  apply (cases inte)
  apply (simp add:Let_def)
  by (metis IntervalResult.inject(1) IntervalResult.simps(4) State.simps(1) State.simps(9) State.surjective)

lemma computeTransaction_preserves_money :
  "validAndPositive_state state \<Longrightarrow>
   moneyInState state + moneyInInputs (inputs tra) = moneyInTransactionOutput state (inputs tra) (computeTransaction tra state contract)"
  apply (simp only:computeTransaction.simps)    
  apply (cases "fixInterval (interval tra) state")
  subgoal for env fixSta
    apply (simp only:IntervalResult.simps Let_def)
    apply (cases "applyAllInputs env fixSta contract (inputs tra)")
    subgoal for newWarn newPay newState newCont
      apply (simp only:ApplyAllResult.simps)
      apply (cases "contract = newCont")
      apply (simp add:refl)
      apply (simp only:bool.case if_False)
      by (metis TransactionOutputRecord.select_convs(2) TransactionOutputRecord.select_convs(3) applyAllInputs_preserves_money fixInterval_preserves_money fixInterval_preserves_preserves_validAndPositive_state moneyInApplyAllResult.simps(1) moneyInTransactionOutput.simps(1))
    by simp_all
  by simp

lemma playTraceAux_preserves_money :
  "validAndPositive_state (txOutState txInRec) \<Longrightarrow>
   playTraceAux txInRec tra = TransactionOutput txOutRec \<Longrightarrow>
   moneyInState (txOutState txOutRec) + moneyInPayments (txOutPayments txOutRec)
   = moneyInState (txOutState txInRec) + moneyInPayments (txOutPayments txInRec) + moneyInTransactions tra"
  apply (induction tra arbitrary: txInRec)
  apply simp
  apply (subst moneyInTransactions_cons)
  subgoal for head tail txInRec
    apply (cases txInRec)
    subgoal for txOutWarningsV txOutPaymentsV txOutStateV txOutContractV
      apply (simp only:playTraceAux.simps(2)[of txOutWarningsV txOutPaymentsV txOutStateV txOutContractV head tail])
      apply (cases "computeTransaction head txOutStateV txOutContractV")
      apply (simp only:TransactionOutput.simps Let_def)
      apply (smt TransactionOutputRecord.select_convs(2) TransactionOutputRecord.select_convs(3) TransactionOutputRecord.surjective TransactionOutputRecord.update_convs(1) TransactionOutputRecord.update_convs(2) computeTransaction_preserves_money computeTransaction_preserves_validAndPositive_state inputsFromTransactions.simps(1) inputsFromTransactions.simps(2) moneyInPayments_distrib moneyInTransactionOutput.simps(1) moneyInTransactions.simps self_append_conv)
      by simp
    done
  done

theorem playTrace_preserves_money :
  "moneyInTransactions tra = moneyInPlayTraceResult tra (playTrace sl contract tra)"
  apply (simp only:playTrace.simps)
  apply (cases "playTraceAux \<lparr>txOutWarnings = [], txOutPayments = [], txOutState = emptyState sl, txOutContract = contract\<rparr> tra")
  apply (simp only: moneyInPlayTraceResult.simps)
  subgoal for newTra
    apply (subst playTraceAux_preserves_money[of "\<lparr>txOutWarnings = [], txOutPayments = [], txOutState = emptyState sl, txOutContract = contract\<rparr>" tra newTra])
    using validAndPositive_initial_state apply auto[1]
    apply blast
    by (simp add:MList.empty_def)
  by simp

theorem playTrace_preserves_money2 :
  "playTrace sl contract tra = TransactionOutput txOut \<Longrightarrow>
   moneyInTransactions tra = moneyInState (txOutState txOut) + moneyInPayments (txOutPayments txOut)"
  by (metis moneyInPlayTraceResult.simps(1) playTrace_preserves_money)

end
