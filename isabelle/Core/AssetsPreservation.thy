theory AssetsPreservation
imports Semantics PositiveAccounts MultiAssets
begin

section "Assets helpers"
text "This section defines helper functions and lemmas to see how many assets are stored in
different semantic types"

subsection "Assets in Accounts"

text "Given a function that adds an entry of the account map to some accumulator"
fun addAccountAssets :: "((AccountId \<times> Token) \<times> int) \<Rightarrow> Assets \<Rightarrow> Assets" where
"addAccountAssets ((_, t), v) b = b + asset t (nat v)"

text "We can express the \<^bold>\<open>assets in the account\<close> as a simple foldr over the accounts array"
fun assetsInAccounts :: "Accounts \<Rightarrow> Assets" where
"assetsInAccounts accs = foldr addAccountAssets accs 0"

text "The \<^emph>\<open>addAccountAssets\<close> function is commutative over composition, which allows to operate
with the fold in different ways."
lemma addAccountAssetsCommutesComposition :
  "addAccountAssets a \<circ> addAccountAssets b = addAccountAssets b \<circ> addAccountAssets a"
proof -
  have "\<forall> c. addAccountAssets a (addAccountAssets b c) = addAccountAssets b (addAccountAssets a c)"
    by (metis addAccountAssets.simps ab_semigroup_add_class.add.commute semigroup_add_class.add.assoc Product_Type.prod.exhaust)
  then show ?thesis
    by fastforce
qed

text "And to be able to express it as a normal \<^emph>\<open>fold\<close> enables more lemmas to work with."
lemma assetsInAccountFold : "assetsInAccounts accs = fold addAccountAssets accs 0"
  by (simp add: addAccountAssetsCommutesComposition foldr_fold)

subsubsection "Ordering of assets in account"

text "Because we are adding positive numbers, adding an account entry to some accumulator is always
going to be the same size or bigger"

lemma addAccountAssets_AlwaysIncreases : "accu \<le> addAccountAssets entry accu"
  by (metis AssetsPreservation.addAccountAssets.elims add_increasing2 order_le_less zero_le)

text "Moreover, filtering an account list is always lower or equal to the unfiltered version"
lemma filtered_as_leq_as : "assetsInAccounts (filter P accs) \<le> assetsInAccounts accs"
proof (induction accs)
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  then show ?case
  proof (cases "P head")
    case True
    then show ?thesis
      by auto (metis addAccountAssets.elims addAccountAssets.simps assetsInAccounts.simps Cons add_le_cancel_right)
  next
    case False
    then show ?thesis
      by auto (metis assetsInAccounts.simps Cons addAccountAssets_AlwaysIncreases order_trans)
  qed
qed

subsubsection "Assets in account distributes over insert"

text "The main theorem of this section \<^emph>\<open>assetsInAccounts_distrib_insert\<close> describes how assets
are distributed when we insert a new entry. To build up to that theorem, we start by analysing
how it distributes when there wasn't a previous entry for that pair."
lemma assetsInAccounts_distrib_insert_not_member :
  assumes "valid_map accs"
  assumes "(accId, tok) \<notin> keys accs"
  shows "assetsInAccounts (MList.insert (accId, tok) val accs) = assetsInAccounts accs + asset tok (nat val)"
proof -
  have "foldr addAccountAssets (MList.insert (accId, tok) val accs) = addAccountAssets ((accId, tok), val) \<circ> foldr addAccountAssets accs" (is "?l = ?r")
    by (meson foldr_insert keys_member_r assms addAccountAssetsCommutesComposition)
  then have "?l 0 = ?r 0"
    by fastforce
  then show ?thesis
    by simp
qed

text "Following the simple case, we provide two lemmas around what happens if there was an existing
entry"

lemma assetsInAccounts_distrib_insert_deleted :
  assumes "valid_map accs"
  shows "assetsInAccounts (MList.insert (accId, tok) val accs) = assetsInAccounts (MList.delete (accId, tok) accs) + asset tok (nat val)"
  by auto (metis AssetsPreservation.assetsInAccounts.elims MList.delete_lookup_None MList.delete_valid MList.member.elims(2) assetsInAccounts_distrib_insert_not_member assms insertOverDeleted keys_member_r)
 

lemma assetsInAccounts_of_deleted :
  assumes "valid_map accs"
  shows "assetsInAccounts (MList.delete (accId, tok) accs)
       = assetsInAccounts accs - asset tok (nat (moneyInAccount accId tok accs))"
proof (cases "(accId, tok) \<in> keys accs")
  case True
  then obtain v where "MList.lookup (accId, tok) accs = Some v"
    by (meson MList.member.simps assms keys_member_r not_None_eq)
  then show ?thesis
    by auto (metis AssetsPreservation.assetsInAccounts.simps add_diff_cancel_right' assetsInAccounts_distrib_insert_deleted assms insertDeleted insertOverDeleted)
next
  case False
  then have "moneyInAccount accId tok accs = 0"
    by auto (metis False MList.member.elims(3) Option.option.simps(4) assms keys_member_r)
  then show ?thesis
    by auto (metis False assms deleteNotMember keys_member_r)
qed

text "And finally the general case"
theorem assetsInAccounts_distrib_insert :
  assumes "valid_map accs"
  shows "assetsInAccounts (MList.insert (accId, tok) val accs)
       = assetsInAccounts accs - asset tok (nat (moneyInAccount accId tok accs)) + asset tok (nat val)"
  using assetsInAccounts_distrib_insert_deleted assetsInAccounts_of_deleted assms by auto

corollary AssetsInAccount_distrib_on_cons :
  "valid_map rest \<Longrightarrow>
  assetsInAccounts (((accId, tok), val) # rest) =  asset tok (nat val) + assetsInAccounts rest"
  by (simp add: Groups.ab_semigroup_add_class.add.commute)


subsubsection "Account assets"

(* These helpers were translated from an older representation, they doesn't help prove that
the assets are preserved, but they help understand the assets of different Parties, so I leave
them around for future usage *)

text "These definitions allows to filter only the assets for a particular accountId"
fun entryInAccount :: "AccountId \<Rightarrow> ((AccountId \<times> Token) \<times> int) \<Rightarrow> bool" where
"entryInAccount accId ((entryAccId, _), _) = (entryAccId = accId)"

fun accountAssets :: "AccountId \<Rightarrow> Accounts \<Rightarrow> Assets" where
"accountAssets accId accs = assetsInAccounts (filter (entryInAccount accId) accs)"

lemma accountAssetsOfEmpty :
  "accountAssets accId [] = 0"
  by simp

lemma accountAssets_without_accId_isZero :
  fixes accId
  assumes "\<And> tok val. ((accId, tok), val) \<notin> set accs"
  shows "accountAssets accId accs = 0"
proof -
  have "filter (entryInAccount accId) accs = []"
    by (metis (full_types) AssetsPreservation.entryInAccount.simps Product_Type.prod.exhaust_sel assms empty_filter_conv)
  then show ?thesis
    by simp
qed

lemma accountAssets_leq_assetsInAccount:
  assumes "valid_map accs"
  shows "accountAssets accId accs \<le> assetsInAccounts accs"
  using filtered_as_leq_as by auto


subsubsection "Money in account"

lemma positiveAccounts_implies_positiveMoneyInAccount :
  assumes "valid_map accs"
      and "allAccountsPositive accs"
    shows "moneyInAccount accId tok accs \<ge> 0"
proof (cases "lookup (accId, tok) accs")
  case None
  then show ?thesis
    by simp
next
  case (Some val)
  moreover note assms
  moreover have "moneyInAccount accId tok accs = val"
    using calculation by force
  ultimately show ?thesis
    using allAccountsPositive_implies_lookup_is_positive by fastforce
qed

text "In order to do assets arithmetic and be able to cancel substractions
we need to know that the assets obtained from \<^term>\<open>moneyInAccount\<close> are always
lower or equal to the total assets. We prove that by expressing the assets
from \<^term>\<open>moneyInAccount\<close> as a filter."
lemma assetsOfMoneyInAccountAsFilter :
  assumes "valid_map accs"
  shows
    "asset token (nat (moneyInAccount accId token accs))
     = assetsInAccounts (filter (\<lambda>(k,_). k = (accId, token)) accs)"
    (is "_ = assetsInAccounts ?filtered")
proof (cases "(accId, token) \<in> keys accs")
  assume "(accId, token) \<in> keys accs"
  moreover note assms
  moreover obtain v1 where "lookup (accId, token) accs = Some v1"
    by (meson MList.member.elims(1) calculation assms keys_member_r not_None_eq)
  moreover have "?filtered = [((accId, token), v1)]"
    using calculation
    by (simp add: lookupAsFilter)
  ultimately show ?thesis
    by auto
next
  assume "(accId, token) \<notin> keys accs"
  moreover have "?filtered = []"
    using calculation filter_empty_conv image_iff
    by auto fastforce
  ultimately show ?thesis
    using assms keys_member_r by fastforce
qed

lemma moneyInAccount_leq_assetsInAccount :
   "valid_map accs
   \<Longrightarrow> asset token (nat (moneyInAccount accId token accs))
     \<le> assetsInAccounts accs"
  using assetsOfMoneyInAccountAsFilter filtered_as_leq_as by presburger

subsubsection "Update money in account"

lemma assetsInAccounts_distrib_on_update:
  assumes "valid_map accs"
  shows "assetsInAccounts (updateMoneyInAccount accId tok val accs)
       = assetsInAccounts accs - asset tok (nat (moneyInAccount accId tok accs)) + asset tok (nat val)"
proof (cases "val \<le> 0")
  case True
  then show ?thesis
    using assms assetsInAccounts_of_deleted by force
next
  case False
  then show ?thesis
    using assms assetsInAccounts_distrib_insert by force
qed

subsubsection "Add money to account"

lemma addMoneyToAccount_distrib:
  assumes "allAccountsPositive accs"
      and "valid_map accs"
    shows "assetsInAccounts (addMoneyToAccount accId tok val accs)
         = assetsInAccounts accs + asset tok (nat val)"
proof (cases "val \<le> 0")
  assume "val \<le> 0"
  then show ?thesis
    by auto
next
  note assms
  moreover assume "\<not> val \<le> 0"
  moreover have "moneyInAccount accId tok accs \<ge> 0"
    using assms positiveAccounts_implies_positiveMoneyInAccount by blast
  moreover have "nat (moneyInAccount accId tok accs + val) = nat (moneyInAccount accId tok accs) + nat val"
    by (meson calculation nat_add_distrib nle_le)
  ultimately show ?thesis
    by (smt (verit, best) Groups.group_cancel.add1 Orderings.preorder_class.dual_order.trans Semantics.addMoneyToAccount.simps moneyInAccount_leq_assetsInAccount assetsDistributesPlus assetsInAccounts_distrib_on_update diff_add )
qed

subsection "Assets in state"

fun assetsInState :: "State \<Rightarrow> Assets" where
"assetsInState state = assetsInAccounts (accounts state)"

lemma state_account_red : "accounts (state \<lparr> accounts := a \<rparr>) = a"
  by simp

subsection "Assets in payment"

fun assetsInExternalPayment :: "Payment \<Rightarrow> Assets" where
"assetsInExternalPayment (Payment _ (Party _) tok val) = asset tok (nat val)" |
"assetsInExternalPayment (Payment _ (Account _) _ _) = 0"

fun addExternalPaymentAssets :: "Payment \<Rightarrow> Assets \<Rightarrow> Assets" where
"addExternalPaymentAssets p a = assetsInExternalPayment p + a"

lemma addExternalPaymentAssetsCommutesComposition :
  "addExternalPaymentAssets a \<circ> addExternalPaymentAssets b = addExternalPaymentAssets b \<circ> addExternalPaymentAssets a"
proof -
  have "\<forall> c. addExternalPaymentAssets a (addExternalPaymentAssets b c) = addExternalPaymentAssets b (addExternalPaymentAssets a c)"
    using Groups.group_cancel.add2 by auto
  then show ?thesis
    by fastforce
qed

fun assetsInExternalPayments :: "Payment list \<Rightarrow> Assets" where
"assetsInExternalPayments ps = foldr addExternalPaymentAssets ps 0"

lemma assetsInPayments_rev : "assetsInExternalPayments payments = assetsInExternalPayments (rev payments)"
proof (induction payments)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  then show ?case
    by (metis assetsInExternalPayments.simps addExternalPaymentAssetsCommutesComposition fold_rev foldr_conv_fold)
qed

lemma assetsInPayments_append : "assetsInExternalPayments (xs @ ys) = assetsInExternalPayments xs + assetsInExternalPayments ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: Groups.semigroup_add_class.add.assoc)
qed

subsection "Assets in input"

fun assetsInInput :: "Input \<Rightarrow> Assets" where
  "assetsInInput (IDeposit _ _ tok money) = asset tok (nat money)" |
  "assetsInInput (IChoice _ _) = 0" |
  "assetsInInput INotify = 0"

fun addInputAssets :: "Input \<Rightarrow> Assets \<Rightarrow> Assets" where
  "addInputAssets i a = assetsInInput i + a"

lemma addInputAssetsCommutesComposition :
  "addInputAssets a \<circ> addInputAssets b = addInputAssets b \<circ> addInputAssets a"
proof -
  have "\<forall> c. addInputAssets a (addInputAssets b c) = addInputAssets b (addInputAssets a c)"
    using Groups.group_cancel.add2 by auto
  then show ?thesis
    by fastforce
qed

fun assetsInInputs :: "Input list \<Rightarrow> Assets" where
  "assetsInInputs inps = foldr addInputAssets inps 0"

subsection "Assets in transaction"

fun assetsInTransaction :: "Transaction \<Rightarrow> Assets" where
  "assetsInTransaction tx = assetsInInputs (inputs tx)"

fun addTransactionAssets :: "Transaction \<Rightarrow> Assets \<Rightarrow> Assets" where
  "addTransactionAssets tx a = assetsInTransaction tx + a"

lemma addTransactionAssetsCommutesComposition :
  "addTransactionAssets a \<circ> addTransactionAssets b = addTransactionAssets b \<circ> addTransactionAssets a"
proof -
  have "\<forall> c. addTransactionAssets a (addTransactionAssets b c) = addTransactionAssets b (addTransactionAssets a c)"
    using Groups.group_cancel.add2 by auto
  then show ?thesis
    by fastforce
qed

fun assetsInTransactions :: "Transaction list \<Rightarrow> Assets" where
  "assetsInTransactions txs = foldr addTransactionAssets txs 0"

section "Asset preservation"

subsection "Fix Interval"

lemma fixInterval_preserves_assets :
  "fixInterval inte state = IntervalTrimmed env newState \<Longrightarrow>
   assetsInState state = assetsInState newState"
  apply (cases inte)
  apply (simp add:Let_def)
  by (metis IntervalResult.inject(1) IntervalResult.simps(4) State.simps(1) State.simps(9) State.surjective)

subsection "Refund one"

text "In order to prove that refundOne preserves assets we first show that for a valid account, the
only way to have 0 assets is to have an empty account."

lemma assetsInAccountIsZero_iff_AccsIsNil :
  "(assetsInAccounts accs = 0 \<and> allAccountsPositive accs) \<longleftrightarrow> (accs = Nil)"
proof -
  have "accs = Nil \<Longrightarrow> allAccountsPositive accs"
    by simp
  moreover have "accs = Nil \<Longrightarrow> assetsInAccounts accs = 0"
    by simp
  moreover have "assetsInAccounts accs = 0 \<and> allAccountsPositive accs \<Longrightarrow> accs = Nil"
    proof (rule ccontr)
      assume "assetsInAccounts accs = 0 \<and> allAccountsPositive accs"
      moreover assume "\<not> accs = Nil"
      moreover obtain hAccId hTok hVal rest where "accs = ((hAccId, hTok), hVal) # rest"
        using Semantics.refundOne.cases calculation by blast
      moreover have "hVal > 0"
        using calculation allAccountsPositiveMeansFirstIsPositive by blast
      moreover have "assetsInAccounts accs = assetsInAccounts rest + asset hTok (nat hVal)"
        using AssetsInAccount_distrib_on_cons calculation by auto
      ultimately show False
        by auto (metis assetValueOfSingleAsset assetValueOfZero linorder_not_le nat_0_iff)
    qed
  ultimately show ?thesis
    by meson
qed

theorem refundOnePreservesAssets :
  assumes "allAccountsPositive accs"
  shows "assetsInAccounts accs = (
           case refundOne accs of
             Some ((accId, tok, val), rest) \<Rightarrow> assetsInAccounts rest + asset tok (nat val)
           | None \<Rightarrow> 0
         )"
proof (cases "refundOne accs")
  case None
  hence "accs = Nil"
    by (metis assms option.simps(3) refundOne.cases refundOne.simps(1) allAccountsPositiveMeansFirstIsPositive)
  then show ?thesis
    by simp
next
  note assms
  case (Some refund)
  moreover obtain accId tok val rest where "refund = ((accId, tok, val), rest)"
    by (metis surj_pair)
  moreover have "accs = ((accId, tok), val) # rest"
    by (smt (verit, ccfv_threshold) Option.option.inject Option.option.simps(3) Pair_inject Semantics.refundOne.elims allAccountsPositiveMeansFirstIsPositive assms calculation(1) calculation(2))
  ultimately show ?thesis
    by auto
qed


subsection "Reduce contract step"

lemma transferBetweenAccountsPreservesMoney :
  assumes "balance = moneyInAccount payFrom token accs"
      and "paidMoney \<ge> 0"
      and "paidMoney \<le> balance"
      and "valid_map accs"
      and "allAccountsPositive accs"
    shows "assetsInAccounts accs
         = assetsInAccounts
            (addMoneyToAccount payTo token paidMoney
              (updateMoneyInAccount payFrom token (balance - paidMoney) accs))"
proof -
  have "nat (balance - paidMoney) = nat balance - nat paidMoney"
    using assms nat_diff_distrib by presburger
  moreover have "nat balance - nat paidMoney + nat paidMoney = nat balance"
    using assms by force
  moreover have "asset token (nat balance) \<le> assetsInAccounts accs"
    using moneyInAccount_leq_assetsInAccount assms by presburger
  moreover have "allAccountsPositive (updateMoneyInAccount payFrom token (balance - paidMoney) accs)"
    using assms
    by (metis diff_ge_0_iff_ge updateMoneyIsPositive)
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) semigroup_add_class.add.assoc addMoneyToAccount_distrib assetsDistributesPlus assetsInAccounts_distrib_on_update assms diff_add updateMoneyInAccount_preserves_valid_map)
qed

fun assetsInReduceEffect :: "ReduceEffect \<Rightarrow> Assets" where
"assetsInReduceEffect (ReduceWithPayment p) = assetsInExternalPayment p" |
"assetsInReduceEffect ReduceNoPayment = 0"

text
"
In order to prove that reduceContractStep preserves assets we only need to check the paths that
leads to the contract being \<^emph>\<open>Reduced\<close>. The other possible outcomes (\<^emph>\<open>NotReduced\<close> and \<^emph>\<open>AmbiguousTimeIntervalReductionError\<close>)
doesn't modify the state nor produce payments.
"

theorem reduceContractStep_preserves_assets :
  "\<lbrakk> validAndPositive_state state
   ; reduceContractStep env state cont = Reduced warnings effect newState newCont
   \<rbrakk> \<Longrightarrow>
   assetsInState state = assetsInReduceEffect effect + assetsInState newState"
proof (cases cont)
  (* Close only reduces the contract if the accounts are not empty.
     If it has it will refundOne (which preserves assets)
   *)
  case Close
  assume
    "validAndPositive_state state"
    "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  moreover have "refundOne (accounts state) \<noteq> None"
    by (smt (verit, best) Close Option.option.simps(4) Semantics.ReduceStepResult.simps(3) Semantics.reduceContractStep.simps(1) calculation(2))
  moreover obtain party token val newAccs where "refundOne (accounts state) = Some ((party, token, val), newAccs)"
    using calculation(3) by fastforce
  moreover have "reduceContractStep env state cont
                  = Reduced
                      ReduceNoWarning
                      (ReduceWithPayment (Payment party (Party party) token val))
                      (state \<lparr> accounts := newAccs \<rparr>)
                      Close"
    by (simp add: Close calculation(4))
  moreover have "newState = (state \<lparr> accounts := newAccs \<rparr>) \<and> effect = ReduceWithPayment (Payment party (Party party) token val)"
    using Semantics.ReduceStepResult.inject calculation(2) calculation(5) by presburger
  ultimately show ?thesis
    using Groups.ab_semigroup_add_class.add.commute refundOnePreservesAssets by auto
next
  case (Pay payFrom payTo payTok payVal payCont)
  assume assms: "validAndPositive_state state"
                "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  then have validAccountMap: "valid_map (accounts state)"
    using validAndPositiveImpliesValid assms valid_state_valid_accounts by blast
  obtain moneyToPay where moneyToPay: "moneyToPay = evalValue env state payVal"
    by blast
  (* If the money to Pay is negative, a warning is raised but no payments are made and the state remains
     the same *)
  then show ?thesis
  proof (cases "moneyToPay \<le> 0")
    assume "moneyToPay \<le> 0"
    then obtain w where "reduceContractStep env state cont =
      Reduced
        w
        ReduceNoPayment
        state
        payCont"
      by (simp add: Pay moneyToPay)
    then show ?thesis
      by (simp add: assms)
  next
    (* If we do have money to pay, the effect and account state depends on the payment being
       internal (transfer between accounts), or an external payout. But both options share a lot
       of common proofs.
     *)
    assume moneyToPayIsPositive: "\<not> moneyToPay \<le> 0"
    obtain balance paidMoney newBalance accsWOFrom payEffect finalAccs where letBindings:
       "balance = moneyInAccount payFrom payTok (accounts state)"
       "paidMoney = min balance moneyToPay"
       "newBalance = balance - paidMoney"
       "accsWOFrom = updateMoneyInAccount payFrom payTok newBalance (accounts state)"
       "(payEffect, finalAccs) = giveMoney payFrom payTo payTok paidMoney accsWOFrom"
      by simp
    then obtain w where payReduced: "reduceContractStep env state cont = Reduced w payEffect (state \<lparr> accounts := finalAccs \<rparr>) payCont"
      by (smt (verit) Product_Type.old.prod.case Semantics.reduceContractStep.simps(2) SemanticsTypes.State.fold_congs(1) letBindings moneyToPayIsPositive assms  moneyToPay Pay)
    then have reducedEffect: "effect = ReduceWithPayment (Payment payFrom payTo payTok paidMoney)"
      using letBindings assms(2) by simp
    then have reducedState: "newState = state \<lparr> accounts := finalAccs \<rparr>"
      using payReduced Semantics.ReduceStepResult.inject assms by presburger
    then have paidMoney_leq_balance: "paidMoney \<le> balance"
      by (simp add: letBindings)
    then have balanceNatSplit: "nat (balance - paidMoney) = nat balance - nat paidMoney"
      using letBindings moneyToPayIsPositive nat_diff_distrib' positiveAccounts_implies_positiveMoneyInAccount assms by force
    show ?thesis
    proof (cases payTo)
      (* If the pay is internal, the assets of the effect are discarded, and the assets removed from payFrom account are added to the
         payTo account *)
      case (Account payToInternal)
      moreover have "assetsInReduceEffect effect = 0"
        by (simp add: calculation  reducedEffect)
      moreover have "assetsInState newState = assetsInAccounts ( addMoneyToAccount payToInternal payTok paidMoney accsWOFrom)"
        by (metis letBindings(5) reducedState  Account AssetsPreservation.assetsInState.simps Product_Type.prod.inject Semantics.giveMoney.elims SemanticsTypes.Payee.simps(5) state_account_red)
      ultimately show ?thesis
        by (smt (verit, best) AssetsPreservation.assetsInState.elims PositiveAccounts.allAccountsPositiveState.elims(2) PositiveAccounts.validAndPositive_state.simps add_cancel_right_left assms(1) balanceNatSplit diff_le_self letBindings(1) letBindings(3) letBindings(4) nat_le_eq_zle paidMoney_leq_balance positiveAccounts_implies_positiveMoneyInAccount transferBetweenAccountsPreservesMoney validAccountMap)
    next
      (* If the pay is external, the assets of the effect are the paid money, and the assets in the account are the ones without the paid money *)
      case (Party payToExternal)
      moreover have "assetsInReduceEffect effect = asset payTok (nat paidMoney)"
        using AssetsPreservation.assetsInExternalPayment.simps(1) AssetsPreservation.assetsInReduceEffect.simps(1) calculation reducedEffect by presburger
      moreover have  "finalAccs = accsWOFrom"
        using letBindings calculation by simp
      moreover have "assetsInState newState = assetsInAccounts accsWOFrom"
        by (metis state_account_red reducedState  AssetsPreservation.assetsInState.simps calculation(3))
      ultimately show ?thesis
        by simp (smt (verit, best) AssetsPreservation.assetsInAccounts.simps Groups.ab_semigroup_add_class.add.commute Groups.semigroup_add_class.add.assoc assetsDistributesPlus assetsInAccounts_distrib_on_update balanceNatSplit diff_add diff_is_0_eq eq_nat_nat_iff letBindings(1) letBindings(3) letBindings(4) moneyInAccount_leq_assetsInAccount nat_le_linear nat_zero_as_int paidMoney_leq_balance validAccountMap)
    qed
  qed
next
  (* If doesn't modify the state nor produce a payment *)
  case (If obs trueCont falseCont)
  assume contractIsReduced: "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  moreover obtain w c where
    "reduceContractStep env state cont = Reduced w ReduceNoPayment state c"
    by (simp add: If)
  ultimately show ?thesis
    by simp
next
  (* When is only reduced if there is a timeout, if there is, the state is preserved and no payments are made *)
  case (When cases timeout tCont)
  assume "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  moreover obtain startTime endTime where "timeInterval env = (startTime, endTime)"
    by fastforce
  moreover have "reduceContractStep env state cont =  Reduced ReduceNoWarning ReduceNoPayment state tCont"
    by (smt (verit, best) Semantics.ReduceStepResult.simps(3) Semantics.ReduceStepResult.simps(5) Semantics.reduceContractStep.simps(4) When calculation(1) calculation(2) case_prod_conv)
  ultimately show ?thesis
    by simp
next
  (* Let doesn't produce a Payment, and it changes the state, but not the accounts *)
  case (Let valId val letCont)
  assume "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  moreover obtain evaluatedValue boundVals newState w where
      "evaluatedValue = evalValue env state val"
      "boundVals = boundValues state"
      "newState = state \<lparr> boundValues := MList.insert valId evaluatedValue boundVals \<rparr>"
      "reduceContractStep env state cont = Reduced w ReduceNoPayment newState letCont"
    by (metis Let Semantics.reduceContractStep.simps(5))
  ultimately show ?thesis
    by force
next
  (* Assert may raise a warning, but doesn't modify the state nor produce a payment *)
  case (Assert obs assertCont)
  assume "reduceContractStep env state cont = Reduced warnings effect newState newCont"
  moreover obtain w where "reduceContractStep env state cont = Reduced w ReduceNoPayment state assertCont"
    by (simp add: Assert)
  ultimately  show ?thesis
    by simp
qed

subsection "Reduce contract until quiescent"

lemma reductionLoop_preserves_assets :
  assumes  "validAndPositive_state inState"
      and  "reductionLoop inReduced inEnv inState inContract inWarnings inPayments
            = ContractQuiescent outReduced outWarnings outPayments outState outContract"
    shows "assetsInState inState + assetsInExternalPayments inPayments
           = assetsInState outState + assetsInExternalPayments outPayments"
using assms proof (induction inReduced inEnv inState inContract inWarnings inPayments rule:reductionLoop_induct)
  case (reductionLoopInduction reduced env state contract warnings payments)
  then show ?case
  proof (cases "reduceContractStep env state contract")
    case (Reduced rWarn rEff rState rCont)
    (* This variable corresponds to the `let newPayments` inside the reductionLoop function *)
    let ?newPayments = "(case rEff of ReduceNoPayment \<Rightarrow> payments | ReduceWithPayment payment \<Rightarrow> payment # payments)"
    have "validAndPositive_state rState"
      using reductionLoopInduction.prems Reduced reduceContractStep_preserves_validAndPositive_state by blast
    with reductionLoopInduction Reduced have newPaymentAssets:
      "assetsInState rState + assetsInExternalPayments ?newPayments = assetsInState outState + assetsInExternalPayments outPayments"
      by simp metis
    with reductionLoopInduction.prems Reduced reduceContractStep_preserves_assets
      have induction_reduceContractStep_preserves_assets:
      "assetsInState state = assetsInReduceEffect rEff + assetsInState rState"
      by blast
    show ?thesis
    proof (cases rEff)
      case ReduceNoPayment
      with newPaymentAssets induction_reduceContractStep_preserves_assets show ?thesis
        by simp
    next
      case (ReduceWithPayment reducePayment)
      with newPaymentAssets induction_reduceContractStep_preserves_assets show ?thesis
         by (simp add: Groups.ab_semigroup_add_class.add.left_commute Groups.semigroup_add_class.add.assoc)
    qed
  next
    case NotReduced
    with reductionLoopInduction assetsInPayments_rev show ?thesis by auto
  next
    case AmbiguousTimeIntervalReductionError
    with reductionLoopInduction show ?thesis by simp
  qed
qed

theorem reduceContractUntilQuiescent_preserves_assets :
  assumes "validAndPositive_state state"
      and "reduceContractUntilQuiescent env state contract
           = ContractQuiescent reduced warnings payments newState cont"
    shows "assetsInState state = assetsInState newState + assetsInExternalPayments payments"
proof -
  have "assetsInState state + assetsInExternalPayments [] = assetsInState newState + assetsInExternalPayments payments"
    by (metis reduceContractUntilQuiescent.simps assms reductionLoop_preserves_assets)
  with assms show ?thesis
    by simp
qed

subsection "Apply input"

(* Custom induction rule for better readability of the proof *)
lemmas applyCases_preserves_assets_induct = applyCases.induct[case_names CaseDeposit CaseChoice CaseNotify a b c d]

lemma applyCases_preserves_assets :
  assumes "validAndPositive_state inState"
      and "applyCases env inState input cases
           = Applied warnings outState cont"
    shows "assetsInState inState + assetsInInput input = assetsInState outState"
using assms proof (induction env inState input cases rule: applyCases_preserves_assets_induct )
  case (CaseDeposit env state inputAccId inputParty inputTok inputAmount caseAccId caseParty caseTok caseAmount caseCont rest)
  have validAccount: "valid_map (accounts state)"
    using "CaseDeposit.prems" validAndPositiveImpliesValid valid_state_valid_accounts by blast
  with CaseDeposit show ?case
    by simp (metis assetsInAccounts.elims allAccountsPositive.elims(3) ApplyResult.inject validAccount addMoneyToAccount_distrib state_account_red)
next
  case (CaseChoice env state inputChoId inputChoice caseChoId caseBounds caseCont rest)
  then show ?case
    by (cases "inputChoId = caseChoId \<and> inBounds inputChoice caseBounds")
       auto
next
  case (CaseNotify env state obs cont rest)
  then show ?case
    by simp (metis ApplyResult.inject)
qed simp_all

theorem applyInput_preserves_assets :
  assumes "validAndPositive_state inState"
      and "applyInput env inState input contract = Applied warnings outState cont"
    shows "assetsInState inState + assetsInInput input = assetsInState outState"
using assms proof (cases contract)
  case (When cs timeout timeoutCont)
  with assms applyCases_preserves_assets show ?thesis
    by simp
qed auto

subsection "Apply all inputs"

lemma applyAllLoop_preserves_assets :
  assumes "validAndPositive_state inState"
      and "applyAllLoop inContractChanged env inState inContract inputs' inWarnings inPayments
          = ApplyAllSuccess outContractChanged outWarnings outPayments outState cont"
    shows "assetsInState inState + assetsInInputs inputs' + assetsInExternalPayments inPayments
          = assetsInState outState + assetsInExternalPayments outPayments"
using assms proof (induction  inContractChanged env inState inContract inputs' inWarnings inPayments rule: applyAllLoop_induct)
  case (applyAllLoopInduction contractChanged env state contract inputs warnings payments)
  have "reduceContractUntilQuiescent env state contract \<noteq> RRAmbiguousTimeIntervalError"
    using local.applyAllLoopInduction.prems(2) by force
  then obtain reduced rWarns rPayments rState rCont
    where contractIsReduced:
      "reduceContractUntilQuiescent env state contract
       = ContractQuiescent reduced rWarns rPayments rState rCont"
    using Semantics.ReduceResult.exhaust by simp blast
  hence preservedReducedAssets:
    "assetsInState state = assetsInState rState + assetsInExternalPayments rPayments"
    using local.applyAllLoopInduction.prems(1) reduceContractUntilQuiescent_preserves_assets by blast
  show ?case
  proof (cases inputs)
    case Nil
    moreover note contractIsReduced preservedReducedAssets applyAllLoopInduction
    moreover have "assetsInInputs inputs = 0"
      using calculation by simp
    moreover have "outPayments = payments @ rPayments"
                  "outState = rState"
      using calculation by auto
    ultimately show ?thesis
      by (metis Groups.group_cancel.add2 add_cancel_left_right assetsInPayments_append)
  next
    case (Cons inputHead inputTail)
    show ?thesis
    proof (cases "applyInput env rState inputHead rCont")
      case (Applied applyWarn applyState applyCont)
      moreover note contractIsReduced preservedReducedAssets applyAllLoopInduction Cons
      moreover have "validAndPositive_state rState"
        using calculation reduceContractUntilQuiescent_preserves_validAndPositive_state
        by meson
      moreover have "validAndPositive_state applyState"
        using calculation applyInput_preserves_preserves_validAndPositive_state
        by meson
      moreover have "applyAllLoop
                  True env applyState applyCont inputTail
                  (warnings @ convertReduceWarnings rWarns
                            @ convertApplyWarning applyWarn)
                  (payments @ rPayments)
              = ApplyAllSuccess outContractChanged outWarnings outPayments outState cont"
        using calculation by auto
      moreover have
         "assetsInState applyState + assetsInInputs inputTail + assetsInExternalPayments (payments @ rPayments)
          = assetsInState outState + assetsInExternalPayments outPayments"
        using calculation by blast
      moreover have "assetsInState rState + assetsInInput inputHead = assetsInState applyState"
        using calculation by (meson applyInput_preserves_assets)
      moreover have "assetsInInputs inputs = assetsInInput inputHead + assetsInInputs inputTail"
        using Cons by auto
      ultimately show ?thesis
        by (metis Groups.ab_semigroup_add_class.add.commute Groups.group_cancel.add2 assetsInPayments_append)
    next
      case ApplyNoMatchError
      with contractIsReduced Cons applyAllLoopInduction show ?thesis by simp
    qed
  qed
qed

theorem applyAllInputs_preserves_assets :
  assumes "validAndPositive_state inState"
      and "applyAllInputs env inState inContract inputs'
          = ApplyAllSuccess outContractChanged outWarnings outPayments outState cont"
    shows "assetsInState inState + assetsInInputs inputs'
          = assetsInState outState + assetsInExternalPayments outPayments"
  using assms applyAllLoop_preserves_assets by fastforce

subsection "Compute transaction"

theorem computeTransaction_preserves_assets :
  assumes "validAndPositive_state state"
      and "computeTransaction tx state contract = TransactionOutput out"
    shows "assetsInState state + assetsInTransaction tx
          = assetsInState (txOutState out) + assetsInExternalPayments (txOutPayments out)"
proof -
  obtain env fixSta
    where fixedTx: "fixInterval (interval tx) state = IntervalTrimmed env fixSta"
    by (smt (verit, best) assms TransactionOutput.distinct(1) computeTransaction.elims IntervalResult.exhaust IntervalResult.simps(6))
  then obtain reduced warnings payments newState cont
    where applyAllInputsSuccess: "applyAllInputs env fixSta contract (inputs tx) = ApplyAllSuccess reduced warnings payments newState cont"
    by (metis (no_types, lifting) ApplyAllResult.exhaust ApplyAllResult.simps(10) ApplyAllResult.simps(9) TransactionOutput.distinct(1) computeTransaction.simps IntervalResult.simps(5) assms(2))
  show ?thesis
  proof (cases "(\<not> reduced) \<and> ((contract \<noteq> Close) \<or> (accounts state = []))")
    case True
    with assms fixedTx applyAllInputsSuccess show ?thesis by simp
  next
    case False
    moreover note assms fixedTx applyAllInputsSuccess
    moreover have "validAndPositive_state fixSta"
      using calculation fixInterval_preserves_preserves_validAndPositive_state validAndPositiveImpliesValid
      by blast
    moreover have "validAndPositive_state newState"
      using calculation applyAllInputs_preserves_preserves_validAndPositive_state
      by blast
    moreover have "assetsInState fixSta + assetsInInputs (inputs tx)
          = assetsInState newState + assetsInExternalPayments payments"
      using calculation applyAllInputs_preserves_assets
      by blast
    moreover have "newState = txOutState out"
                  "payments = txOutPayments out"
      using calculation by auto
    ultimately show ?thesis
      by (metis AssetsPreservation.assetsInTransaction.simps fixInterval_preserves_assets)
  qed
qed

subsection "Play Trace"

lemma playTraceAux_preserves_assets :
  assumes "validAndPositive_state (txOutState prevOut)"
      and "playTraceAux prevOut txs = TransactionOutput nextOut"
    shows "assetsInState (txOutState prevOut)
             + assetsInExternalPayments (txOutPayments prevOut)
             + assetsInTransactions txs
          = assetsInState (txOutState nextOut)
             + assetsInExternalPayments (txOutPayments nextOut)"
using assms proof (induction txs arbitrary: prevOut)
  case Nil
  then show ?case by simp
next
  case (Cons h t)
  obtain prevWarn prevPays prevState prevCont where prevOutPattern:
    "prevOut = \<lparr> txOutWarnings = prevWarn
               , txOutPayments = prevPays
               , txOutState = prevState
               , txOutContract = prevCont
               \<rparr>"
    using TransactionOutputRecord.cases by blast

  show ?case
  proof (cases "computeTransaction h prevState prevCont")
    case (TransactionOutput transRes)
    let ?updTransRes = "transRes  \<lparr> txOutPayments := prevPays @ txOutPayments transRes
                                  , txOutWarnings := prevWarn @ txOutWarnings transRes \<rparr>"
    note prevOutPattern TransactionOutput Cons
    moreover have "validAndPositive_state prevState"
                  "validAndPositive_state (txOutState transRes)"
                  "validAndPositive_state (txOutState ?updTransRes)"
      using calculation computeTransaction_preserves_validAndPositive_state by auto
    moreover have "assetsInState prevState + assetsInTransaction h
                  = assetsInState (txOutState transRes) + assetsInExternalPayments (txOutPayments transRes)"
      using calculation computeTransaction_preserves_assets by presburger
    moreover have "playTraceAux ?updTransRes t = TransactionOutput nextOut"
      using calculation by simp
    moreover have
      "assetsInState (txOutState ?updTransRes)
        + assetsInExternalPayments (txOutPayments ?updTransRes)
        + assetsInTransactions t
     = assetsInState (txOutState nextOut)
        + assetsInExternalPayments (txOutPayments nextOut)"
      using calculation by blast
    ultimately show ?thesis
      using assetsInPayments_append
      by (simp add: ab_semigroup_add_class.add.commute ab_semigroup_add_class.add.left_commute)
  next
    case (TransactionError err)
    with Cons prevOutPattern show ?thesis
      by simp
  qed
qed

theorem playTrace_preserves_assets :
  assumes "playTrace slot contract txs = TransactionOutput out"
    shows "assetsInTransactions txs
         = assetsInState (txOutState out) + assetsInExternalPayments (txOutPayments out)"
proof -
  let ?iniState = "\<lparr> txOutWarnings = []
                   , txOutPayments = []
                   , txOutState = emptyState slot
                   , txOutContract = contract
                   \<rparr>"
  have  "validAndPositive_state (txOutState ?iniState)"
    and "playTraceAux ?iniState txs = TransactionOutput out"
    using assms validAndPositive_initial_state by auto
  moreover
  have "assetsInState (txOutState ?iniState)
         + assetsInExternalPayments (txOutPayments ?iniState)
         + assetsInTransactions txs
      = assetsInState (txOutState out) + assetsInExternalPayments (txOutPayments out)"
    using calculation playTraceAux_preserves_assets by blast
  ultimately show ?thesis
     by (auto simp add: MList.empty_def)
qed

end
