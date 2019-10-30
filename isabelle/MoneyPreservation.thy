theory MoneyPreservation
imports Semantics PositiveAccounts
begin

fun moneyInReduceEffect :: "ReduceEffect \<Rightarrow> int" where
"moneyInReduceEffect (ReduceWithPayment (Payment _ x)) = x" |
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
      by (metis add.commute diff_add_cancel giveMoney.simps(1) moneyInReduceEffect.simps(1) not_less not_less_iff_gr_or_eq prod.sel(1) snd_conv updateMoneyInAccount_money)
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
  "valid_map (accounts state) \<Longrightarrow>
   allAccountsPositive (accounts state) \<Longrightarrow>
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
  "valid_map (accounts state) \<Longrightarrow>
   allAccountsPositive (accounts state) \<Longrightarrow>
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
    apply (metis add.left_neutral reduceContractStep_preserves_money_acc_to_acc_aux snd_conv)
    by simp
  done

lemma reduceContractStep_preserves_money :
  "valid_map (accounts state) \<Longrightarrow>
   allAccountsPositiveState state \<Longrightarrow>
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
    apply (simp del:valid_map.simps allAccountsPositive.simps moneyInAccount.simps moneyInAccounts.simps giveMoney.simps updateMoneyInAccount.simps)
    apply (cases payee)
    apply (simp only:Let_def)
    subgoal for x1
      using reduceContractStep_preserves_money_acc_to_acc by blast
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

end
