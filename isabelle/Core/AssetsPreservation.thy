theory AssetsPreservation
imports Semantics PositiveAccounts
begin

section "Assets"

text "We represent Multi-token assets as a function from Token to natural numbers." 
(*
TODO: decide if we want to change this definition to a (Token \<rightharpoonup> nat) Map with a 
finite domain. This could help if we try to generate code from this theory as this definition yields 
Wellsortedness error (see last dummy section).

The problem that I see with changing the definition is that converting to a Map makes the 0 definition
more complex or some theorems like assetZero not true, as having (\<forall> t. None) is not the same as (asset tok 0).
One way to aliviate that is to also require the asset to be strictly bigger than 0, but is it worth it?
*)

typedef Assets = "{assets :: Token \<Rightarrow> nat. True}"
  by auto 

setup_lifting type_definition_Assets

text 
"
The \<^emph>\<open>asset\<close> definition allows us to create a single-token asset
"
lift_definition asset :: "Token \<Rightarrow> nat \<Rightarrow> Assets" 
  is "\<lambda>tok val. \<lambda>t. if t = tok then val else 0"
  by simp

text 
"
The \<^emph>\<open>assetValue\<close> definition allow us to obtain how many \<^emph>\<open>tokens\<close> (for a particular token)
are in the Assets
"
lift_definition assetValue :: "Token \<Rightarrow> Assets \<Rightarrow> nat" is 
  "\<lambda>t a. a t" .

lemma assetValueOfSingleAsset : "assetValue tok (asset tok b) = b"
  by transfer simp

lemma assetValueOfDifferentToken : "tok1 \<noteq> tok2 \<Longrightarrow> assetValue tok1 (asset tok2 b) = 0"
  by transfer simp

lemma assetsEqByValue: "a = b \<longleftrightarrow> (\<forall> tok. assetValue tok a = assetValue tok b)"
  by transfer auto

subsection "Ordering"
text "
We define partial order for assets instead of total order because we cannot compare values of different tokens.
"

text "We need to define order because Assets can't be negative, so we can only simplify things like
\<^term>\<open>a + (b - a) = b\<close> if \<^term>\<open>a \<le> b\<close>.
"
instantiation Assets :: ord
begin


lift_definition less_eq_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> bool" 
  is "\<lambda>a b. \<forall>t. a t \<le> b t " .

lift_definition less_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> bool" 
  is "\<lambda>a b. (\<forall>rt. a rt \<le> b rt) \<and> (\<exists> st. a st < b st) " .

instance ..

end

instantiation Assets :: preorder 
begin 
instance proof
 fix a b c :: Assets

 show "a \<le> a"
   by transfer simp
    
 show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
   using le_trans by transfer blast 

 show "a < b = ( a \<le> b \<and> \<not>  b \<le> a)"
   by transfer (metis leD leI)    
qed
end

instantiation Assets :: order 
begin 
instance proof 
  fix a b :: Assets
  show " a \<le> b \<Longrightarrow>  b \<le> a \<Longrightarrow> a = b"     
    using le_antisym by transfer blast
qed
end

text "If we create a single asset from a multi-asset, then the single asset is going to be lower or 
equal to the multi-asset"
lemma singleAsset_leq_than_asset: "asset t (assetValue t a) \<le> a" 
  by transfer simp


subsection "Arithmetic"

instantiation Assets :: zero
begin

lift_definition zero_Assets :: Assets
  is "\<lambda>_. 0"
  by simp

instance ..
end

text "Creating a single asset with 0 tokens is the same as creating the zero_Assets"
lemma assetZero : "asset tok 0 = 0"
  by transfer auto


text "If we try to create a single asset from a negative integer is also the same as creating the zero_Assets"
corollary assetOfNegInt : "(i :: int) \<le> 0 \<Longrightarrow> asset t (nat i) = 0 "
  by (simp add: assetZero)

text "Trying to count the amount of tokens of the zero_Assets is 0"
lemma assetValueOfZero : "assetValue t 0 = 0"
  by transfer simp


instantiation Assets :: plus
begin

lift_definition plus_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> Assets" 
  is "\<lambda>x y. \<lambda>tok. x tok + y tok"
  by auto

instance ..
end

lemma assetsDistributesPlus : "asset tok (a + b) = asset tok a + asset tok b"
  by transfer auto

lemma assetsJoinPlus : "asset tok a + asset tok b = asset tok (a + b)" 
  by (simp add: assetsDistributesPlus)

instantiation Assets :: minus
begin

lift_definition minus_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> Assets" 
  is "\<lambda>x y. \<lambda>tok. x tok - y tok"
  by auto

instance ..
end

lemma assetsDistributesMinus : "asset tok (a - b) = asset tok a - asset tok b"
  by transfer auto

instantiation Assets :: semigroup_add
begin
instance proof
  fix a b c :: Assets 

  show "(a + b) + c = a + (b + c)"
    by transfer (simp add: Groups.ab_semigroup_add_class.add_ac(1))
qed
end

instantiation Assets :: ab_semigroup_add
begin
instance proof
  fix a b :: Assets

  show "a + b = b + a" 
    by transfer (simp add: Groups.ab_semigroup_add_class.add.commute)    
qed
end


instantiation Assets :: monoid_add
begin
instance proof 
  fix a :: Assets

  show "0 + a = a" 
    by transfer auto
  show "a + 0 = a" 
    by transfer auto
qed
end

(* TODO: This should be included by monoid_add, but for some reason I cannot delete it *)
instantiation Assets :: comm_monoid_add 
begin
instance by standard simp
end

instantiation Assets :: cancel_ab_semigroup_add 
begin 
instance proof 
  fix a b c :: Assets
  show "a + b - a = b" 
    by transfer force
  show "a - b - c = a - (b + c)"
    using diff_diff_left by transfer presburger
qed
end

instantiation Assets :: comm_monoid_diff
begin 
instance proof 
  fix a :: Assets
  show "0 - a = 0" 
    by transfer simp
qed
end

instantiation Assets :: ordered_ab_semigroup_add 
begin 
instance proof 
  fix a b c :: Assets
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by transfer simp
qed 
end

instantiation Assets :: ordered_ab_semigroup_add_imp_le
begin 
instance proof 
  fix a b c :: Assets
  show "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by transfer simp
qed
end


instantiation Assets :: canonically_ordered_monoid_add 
begin 
instance proof 
  fix a b :: Assets 
  (* TODO: See how to make this proof structured *)
  have "a \<le> b \<Longrightarrow> \<exists>c. b = a + c"
   apply transfer
    subgoal for a2 b2       
      apply (subgoal_tac  "\<And> x. a2 x \<le> b2 x \<Longrightarrow> b2 x = a2 x + (b2 x - a2 x)")
       apply fast
      by simp
    done
  also have "\<exists>c. b = a + c \<Longrightarrow> a \<le> b" 
    by transfer auto

  then show "(a \<le> b) = (\<exists>c. b = a + c)" 
    using calculation by blast
qed
end

instantiation Assets :: ordered_cancel_comm_monoid_diff 
begin
instance by standard 
end



section "Accounts"

text \<open>In the SemanticTypes theory, the Accounts is defined as an associative list, which is good 
to represent executable code. In this theory, we define Accounts as a logical Map which is better
for reasoning \<close>
(* TODO: the previous text is what I intended when I defined Account as a Map, and 
   for some lemma this is true, but I found myself having to define lemmas around the list representation
   instead of the Map representation for the important parts, for example assetsInAccounts_distrib_on_update
*)
(* TODO: most proves regarding this representation requires Accounts to be finite, 
          should I define a typedef with lifting and the finite precondition? I'm worried that this
          would imply to lift a lot of Map lemmas.
*)
type_synonym Accounts = "AccountId \<rightharpoonup> Assets"


fun accountAssets :: "AccountId \<Rightarrow> Accounts \<Rightarrow> Assets" where 
"accountAssets accId m = (case m accId of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

lemma accountAssetsOfEmpty : 
  "accountAssets accId Map.empty = 0" 
  by simp

subsection "Assets in Accounts"

text \<open>We define assetsInAccounts as the sum of Assets for every accId \<close>
definition sum_accs_graph :: "(AccountId \<times> Assets) \<Rightarrow> Assets \<Rightarrow> Assets"
  where "sum_accs_graph t a = snd t + a"

text "The comp_fun_commute_on locale interpretation allows us to better reason
about assetsInAccounts when the Account is finite"
interpretation sum_accs_graph: comp_fun_commute_on  "UNIV" sum_accs_graph
  by unfold_locales (simp add: comp_def add_ac(3) sum_accs_graph_def)

fun assetsInAccounts :: "Accounts \<Rightarrow> Assets" where 
"assetsInAccounts accs = Finite_Set.fold sum_accs_graph 0 (Map.graph accs)" 


lemma assetsInAccounts_distrib: 
  assumes "finite (dom m)" 
  shows "assetsInAccounts (m (accId \<mapsto> a)) = assetsInAccounts (m (accId := None)) + a" 
proof -
  note assms
  moreover obtain entry AccountWOEntry where  
    "entry = (accId, a)"
    "AccountWOEntry = Map.graph (m (accId := None))" 
    by simp

  moreover have "finite AccountWOEntry" 
    using calculation by simp

  moreover have "entry \<notin> AccountWOEntry" 
    using in_graphD calculation by force

  moreover have "Finite_Set.fold sum_accs_graph 0 (Set.insert entry AccountWOEntry) = sum_accs_graph entry (Finite_Set.fold sum_accs_graph 0 AccountWOEntry)"
    using calculation by simp

  ultimately show ?thesis     
    by (simp add: Groups.ab_semigroup_add_class.add.commute sum_accs_graph_def)
qed


corollary assetsInAccountsOfNotMember: 
  assumes "finite (dom m)" and "m accId = None" 
  shows  "assetsInAccounts (m (accId \<mapsto> a)) = assetsInAccounts m + a"
  using assms by (metis assetsInAccounts_distrib fun_upd_triv)

lemma assetsInAccountWithoutAccId : 
"finite (dom m) 
 \<Longrightarrow>
  assetsInAccounts (m (accId := None)) = assetsInAccounts m - accountAssets accId m
" 
  by (smt (verit, best) AssetsPreservation.accountAssets.elims Groups.comm_monoid_add_class.add.comm_neutral Option.option.case_eq_if Option.option.sel add_diff_cancel_right' assetsInAccounts_distrib domD domIff fun_upd_triv)


lemma accountAssets_leq_assetsInAccount:
  assumes "finite (dom accs)"
  shows "accountAssets accId accs \<le> assetsInAccounts accs" 
proof (cases "accs accId")
  case None
  then show ?thesis 
    by (simp add: domIff)
next
  case (Some accIdAsset)

  then obtain restAccount where "accs = restAccount (accId \<mapsto> accIdAsset) \<and> accId \<notin> (dom restAccount)" 
    by (metis Some domIff fun_upd_same fun_upd_triv fun_upd_upd)

  then have "assetsInAccounts accs = assetsInAccounts restAccount + accIdAsset"
    by (metis assetsInAccounts_distrib assms dom_fun_upd finite_insert fun_upd_None_if_notin_dom)
  
  then show ?thesis     
    using Some Groups.ab_semigroup_add_class.add.commute le_iff_add by fastforce
qed


subsection "Merge accounts"

fun mergeAccounts :: "Accounts \<Rightarrow> Accounts \<Rightarrow> Accounts" where 
"mergeAccounts acc1 acc2 = (\<lambda>accId. combine_options (+) (acc1 accId) (acc2 accId))"

lemma mergeAccountsDom: "dom (mergeAccounts acc1 acc2) = dom (acc1) \<union> dom (acc2)" (is "?domM = _")
proof - 
  have belongsAcc1: "\<And>x. x \<in> dom acc1 \<Longrightarrow> x \<in> ?domM" 
    by (smt (verit, del_insts) AssetsPreservation.mergeAccounts.elims combine_options_simps(2) combine_options_simps(3) domD domI domIff)
  have belongsAcc2: "\<And>x. x \<in> dom acc2 \<Longrightarrow> x \<in> ?domM" 
    by (metis AssetsPreservation.mergeAccounts.simps belongsAcc1 combine_options_simps(1) domIff)
  have "\<And>x. x \<notin> dom acc1 \<and> x \<notin> dom acc2 \<Longrightarrow> x \<notin> ?domM" 
    by auto
  then show ?thesis
    by (meson Un_iff belongsAcc1 belongsAcc2 subsetI subset_antisym)
qed

lemma mergeWithEmptyL : "mergeAccounts Map.empty a = a" 
  by auto

lemma mergeWithEmptyR : "mergeAccounts a Map.empty = a" 
  by auto

lemma mergeSingletonWithoutKey : "k \<notin> dom a \<Longrightarrow> mergeAccounts a [k \<mapsto> v] = a (k \<mapsto> v)" 
  by auto 

lemma mergeSingletonWithKey : "a k = Some va \<Longrightarrow> mergeAccounts a [k \<mapsto> v] = a (k \<mapsto> v + va)"
  using Groups.ab_semigroup_add_class.add.commute by fastforce

lemma mergeAccountsAssoc : "mergeAccounts (mergeAccounts a b) c = mergeAccounts a (mergeAccounts b c)" 
  by (simp add: Groups.semigroup_add_class.add.assoc combine_options_assoc)

lemma mergeAccountsComm : "mergeAccounts a b = mergeAccounts b a" 
  by (simp add: Groups.ab_semigroup_add_class.add.commute combine_options_commute)

lemma singleMapFinite : "finite (dom ([k \<mapsto> v]))" 
  by (simp)

lemma assetsInAccounts_distrib_single_asset_merge: 
" finite (dom a1)
  \<Longrightarrow> 
  assetsInAccounts (mergeAccounts a1 [k \<mapsto> v]) = assetsInAccounts a1 + v 
" 
proof (cases "k \<in> dom a1")
  case True
  then obtain va1 where va1: "a1 k = Some va1" 
    by blast
  assume assm1: "finite (dom a1)"
  then show ?thesis 
    by (smt (verit, ccfv_threshold) Groups.ab_semigroup_add_class.add.commute Groups.ab_semigroup_add_class.add.left_commute assetsInAccounts_distrib fun_upd_triv mergeSingletonWithKey va1)
  
next
  case False
  assume assm1: "finite (dom a1)"
  then have "a1(k := None) = a1" 
    by (simp add: False)
  with assm1 False show ?thesis 
    by (metis Groups.ab_semigroup_add_class.add.commute assetsInAccounts_distrib mergeSingletonWithoutKey)
qed

lemma assetsInAccount_distrib_merge :
"\<lbrakk> finite (dom a1)
 ; finite (dom a2) 
 \<rbrakk> \<Longrightarrow>
  assetsInAccounts (mergeAccounts a1 a2) = assetsInAccounts a1 + assetsInAccounts a2"
proof (induction "a1" arbitrary: a2 rule: finite_Map_induct )
  case empty
  then show ?case 
    by simp
next
  case (update a1Id a1Asset a1Rest)
  then show ?case
    by (smt (verit) Groups.ab_semigroup_add_class.add.commute Groups.semigroup_add_class.add.assoc assetsInAccounts_distrib_single_asset_merge finite_Un mergeAccountsAssoc mergeAccountsComm mergeAccountsDom mergeSingletonWithoutKey)      
qed


lemma accountAssets_distrib_merge : "
  \<lbrakk> finite (dom a)
  ; finite (dom b) 
  \<rbrakk> \<Longrightarrow> 
  accountAssets accId (mergeAccounts a b) = accountAssets accId a + accountAssets accId b" 
proof (induction a rule: finite_Map_induct)
  case empty
  then show ?case by simp
next
  case (update k v m)
  then show ?case 
    by (simp add: Option.option.case_eq_if combine_options_def) 
qed



subsection "From Semantic Accounts"

text \<open>The following function converts the list representation of Accounts to the Map representation\<close>

fun fromSemanticAccounts  :: "SemanticsTypes.Accounts \<Rightarrow> Accounts" where 
"fromSemanticAccounts Nil = Map.empty " |
"fromSemanticAccounts (((accId, tok), val) # rest) =
   mergeAccounts 
    [accId \<mapsto> asset tok (nat val)]
    (fromSemanticAccounts rest)
"

text \<open>Maps could theoretically be infinite, but if we create an Accounts using fromSemanticAccounts, then we know
it is finite (which is a handy property for other proofs)\<close>
lemma fromSemanticAccountsIsFinite : "finite (dom (fromSemanticAccounts accs))"
proof (induction accs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons head rest)
  also obtain hAccId hTok hVal where "head = ((hAccId, hTok), hVal)" 
    by (metis surj_pair)
  then show ?case    
    by (metis AssetsPreservation.fromSemanticAccounts.simps(2) calculation finite_Un mergeAccountsDom singleMapFinite)
qed


lemma fromSemanticAccountsOfNotMemberInsert: 
"
\<lbrakk> valid_map accs
; \<not> MList.member (accId, tok) accs 
\<rbrakk> \<Longrightarrow> 
    fromSemanticAccounts (MList.insert (accId, tok) val accs) 
  = mergeAccounts 
      [accId \<mapsto> (asset tok (nat val))] 
      (fromSemanticAccounts accs)"
proof (induction accs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons head rest)

  then have "valid_map rest"
    by simp

  moreover obtain hAccId hTok hVal where pHead: "head = ((hAccId, hTok), hVal)"
    by (metis Product_Type.prod.exhaust_sel)

  ultimately show ?case using Cons  
    by (smt (verit) AssetsPreservation.fromSemanticAccounts.simps(2) MList.insert.simps(2) MList.lookup.simps(2) MList.member.simps mergeAccountsAssoc mergeAccountsComm not_None_eq not_less_iff_gr_or_eq pHead)

qed

fun assetsInSemanticAccounts :: "SemanticsTypes.Accounts \<Rightarrow> Assets" where
"assetsInSemanticAccounts Nil = 0" |
"assetsInSemanticAccounts (Cons ((_, tok), val) rest)  = asset tok (nat val) + assetsInSemanticAccounts rest"

fun assetsInAccounts' :: "SemanticsTypes.Accounts \<Rightarrow> Assets" where 
"assetsInAccounts' accs = assetsInAccounts (fromSemanticAccounts accs)"

lemma assetsInAccount_eq_assetsInSemantic:
 "assetsInAccounts' accs = assetsInSemanticAccounts accs"
proof (induction accs)
  case Nil
  then show ?case using zero_Assets_inst.zero_Assets
    by auto
next
  case (Cons head rest )
  obtain hAccId hTok hVal where hPattern: "head = ((hAccId, hTok), hVal)"
    by (metis eq_fst_iff)
  then show ?case
    using Cons assetsInAccounts_distrib_single_asset_merge fromSemanticAccountsIsFinite mergeAccountsComm Groups.ab_semigroup_add_class.add.commute
    by simp
qed


lemma assetsInAccountCons : 
  "assetsInAccounts' (((accId, tok), val) # rest) =  assetsInAccounts' rest + asset tok (nat val)"
  by (metis assetsInSemanticAccounts.simps(2) ab_semigroup_add_class.add.commute assetsInAccount_eq_assetsInSemantic)
  

subsection "Money in account" 
(* TODO: Haven't proved this yet, but I think it could be useful to start thinking the rest of the code in terms
of Map accounts instead of List accounts *)
lemma moneyInAccountFromSemantic :
"\<lbrakk> valid_map accs
 ; accs' = fromSemanticAccounts accs
 \<rbrakk> \<Longrightarrow>
   moneyInAccount accId tok accs = int (assetValue tok (accountAssets accId accs'))"
proof (induction accs arbitrary: accs')
  case Nil
  
  then have "accountAssets accId accs' = 0"   
     by (simp add: accountAssetsOfEmpty)
  moreover have "moneyInAccount accId tok [] = 0" 
     by simp
 
  ultimately show ?case
    using assetValueOfZero by presburger
  
next
  case (Cons head rest)
  then obtain hAccId hTok hVal where pHead: "head = ((hAccId, hTok), hVal)"
    by (metis Product_Type.prod.exhaust_sel)
  then obtain rest' where pRest: "fromSemanticAccounts rest = rest'"
    by force
  then have 0:"accs' = mergeAccounts [hAccId \<mapsto> asset hTok (nat hVal)] rest'"
    using AssetsPreservation.fromSemanticAccounts.simps(2) local.Cons.prems(2) pHead by presburger
  then show ?case
    apply (subst 0)
    oops

lemma moneyInAccount_leq_accountAssets:
 "
 valid_map accs
   \<Longrightarrow> asset token (nat (moneyInAccount accId token accs))
     \<le> accountAssets accId (fromSemanticAccounts accs)
"
proof (induction accs)
  case Nil
  then show ?case
    by (simp add: assetZero)
next
  case (Cons head rest)
  then obtain hAccId hTok hVal where pHead: "head = ((hAccId, hTok), hVal)" 
    by (metis surj_pair)
  show ?case
  proof (cases "(hAccId, hTok) = (accId, token)")
    case True
    with pHead Cons fromSemanticAccountsIsFinite  show ?thesis      
      apply (subst (2) pHead)
      apply (subst fromSemanticAccounts.simps)
      apply (subst accountAssets_distrib_merge)
        apply auto[2]
      apply simp
      using le_iff_add by blast
  next
    case False
    with pHead Cons fromSemanticAccountsIsFinite show ?thesis    
      by (smt (verit, ccfv_threshold) AssetsPreservation.fromSemanticAccounts.simps(2) Groups.ab_semigroup_add_class.add.commute Groups.ab_semigroup_add_class.add_ac(1) Semantics.moneyInAccount.simps accountAssets_distrib_merge findWithDefault_step le_iff_add singleMapFinite sublist_valid)  
  qed
qed

subsection "Update money in account"


lemma assetsInAccounts_distrib_insert_not_member: "
\<lbrakk> valid_map accs 
; \<not> MList.member (accId, tok) accs 
\<rbrakk> \<Longrightarrow>
  assetsInAccounts' (MList.insert (accId, tok) val accs)
  = assetsInAccounts' accs + asset tok (nat val)
"
  by (metis AssetsPreservation.assetsInAccounts'.simps AssetsPreservation.assetsInSemanticAccounts.simps(2) AssetsPreservation.fromSemanticAccounts.simps(2) Groups.ab_semigroup_add_class.add.commute fromSemanticAccountsOfNotMemberInsert assetsInAccount_eq_assetsInSemantic)

lemma assetsInAccounts_distrib_insert :
 "valid_map accs
 \<Longrightarrow> 
  assetsInAccounts' (MList.insert (accId, tok) val accs)
  = assetsInAccounts' accs - asset tok (nat (moneyInAccount accId tok accs)) + asset tok (nat val)"
(* TODO: simplify proof *)
proof (induction accs rule: MList_induct)
  case empty
  moreover have "MList.insert (accId, tok) val [] = [((accId, tok), val)]" (is "_ = ?m")
    by simp
  moreover have "assetsInAccounts' ?m = asset tok (nat val)" 
    by (metis AssetsPreservation.assetsInAccounts'.elims AssetsPreservation.assetsInSemanticAccounts.simps(1) AssetsPreservation.assetsInSemanticAccounts.simps(2) add_cancel_left_right assetsInAccount_eq_assetsInSemantic)
  ultimately show ?case 
    by (simp add: assetZero)
next
  case (update uKey uVal rest)

  then obtain uAccId uTok where pUpdate: "uKey = (uAccId, uTok)" 
    using Product_Type.old.prod.exhaust by blast
  then have lookupUKeyNone: "lookup (uAccId, uTok) rest = None"
    using local.update.hyps(2) by force
  then show ?case
  proof (cases "(accId, tok) = (uAccId, uTok)")
    case True
    then have 0: "insert (accId, tok) val (insert uKey uVal rest) = insert (accId, tok) val rest"
      using pUpdate insert_replaces_value local.update.hyps(1) by fastforce
    then have 1: "uTok = tok \<and> uAccId = accId" 
      using True by force
    then have 2: "lookup (accId, tok) (insert (uAccId, uTok) uVal rest) = Some uVal"
      by (simp add: insert_lookup_Some)
    then have 3: "moneyInAccount accId tok (insert (uAccId, uTok) uVal rest) = uVal"      
      using 1 2 by simp
    then have 5: "moneyInAccount accId tok rest = 0"
      using 1 lookupUKeyNone 
      by force
    then have 6: "assetsInAccounts' (insert (uAccId, uTok) uVal rest) = assetsInAccounts' rest + asset uTok (nat uVal)"
      using assetsInAccounts_distrib_insert_not_member local.update.hyps(1) local.update.hyps(2) pUpdate by blast
    
    then show ?thesis
      using "0" "1" "3" "5" assetZero local.update.IH pUpdate by fastforce
    
  next
    case False
    then have 0: "lookup (accId, tok) (insert uKey uVal rest) = lookup (accId, tok) rest"
      by (simp add: insert_lookup_different pUpdate)
    then have 1: "moneyInAccount accId tok (insert uKey uVal rest) = moneyInAccount accId tok rest" 
      by simp
    then have 2: "insert (accId, tok) val (insert uKey uVal rest) = insert uKey uVal (insert (accId, tok) val rest)"      
      by (metis False local.update.hyps(1) pUpdate insert_swap)      
    then have 3: "assetsInAccounts' (insert uKey uVal (insert (accId, tok) val rest)) =  assetsInAccounts' (insert (accId, tok) val rest) +  asset uTok (nat uVal) "
      by (metis False MList.member.elims(2) assetsInAccounts_distrib_insert_not_member insert_lookup_different insert_valid local.update.hyps(1) lookupUKeyNone pUpdate)
    then have 4: "assetsInAccounts' (insert uKey uVal rest) =  asset uTok (nat uVal) +  assetsInAccounts' rest  "
      using Groups.ab_semigroup_add_class.add.commute assetsInAccounts_distrib_insert_not_member local.update.hyps(1) local.update.hyps(2) pUpdate by auto
    then have 5: "asset tok (nat (moneyInAccount accId tok rest)) \<le> assetsInAccounts' rest"    
      by (metis AssetsPreservation.assetsInAccounts'.simps Orderings.preorder_class.order.trans accountAssets_leq_assetsInAccount fromSemanticAccountsIsFinite local.update.hyps(1) moneyInAccount_leq_accountAssets)    
    then show ?thesis      
      by (metis "1" "2" "3" "4" Groups.ab_semigroup_add_class.add.commute Groups.ab_semigroup_add_class.add_ac(1) Groups.ordered_cancel_comm_monoid_diff_class.diff_add_assoc local.update.IH)
  qed
qed


lemma assetsInAccounts_distrib_on_update: "
 valid_map accs
 \<Longrightarrow>  assetsInAccounts'(updateMoneyInAccount accId tok val accs)
  =   assetsInAccounts' accs - asset tok (nat (moneyInAccount accId tok accs)) + asset tok (nat val)"
proof (cases "val \<le> 0")
  assume accIsValid: "valid_map accs"
  case True

  then show ?thesis 
  proof (cases "MList.lookup (accId, tok) accs")
    case None   
    with accIsValid have deleteSimp: "delete (accId, tok) accs = accs" 
      by (simp add: None deleteNotMember)
    from None have "moneyInAccount accId tok accs = 0"
      by simp  
    with deleteSimp  show ?thesis using True
      by (simp add: assetZero)
  next
    case (Some existingVal)
    with Some have existingMoneyInAcc: "moneyInAccount accId tok accs = existingVal"
      by simp    

    obtain accsWOKey where accsWOKey: "accsWOKey = MList.delete (accId, tok) accs"
      by blast

    with accIsValid delete_lookup_None 
      have accsWOKey_notMember: "\<not> MList.member (accId, tok) accsWOKey"
      by auto

    from Some accsWOKey have "accs = MList.insert  (accId, tok) existingVal accsWOKey"
      by (metis accIsValid insertDeleted)

    with existingMoneyInAcc accsWOKey_notMember True show ?thesis 
      by (metis Semantics.updateMoneyInAccount.elims accIsValid accsWOKey add_cancel_right_right add_implies_diff assetOfNegInt assetsInAccounts_distrib_insert_not_member delete_valid)
  qed
     
next
  assume accIsValid: "valid_map accs"
  case False
  with accIsValid show ?thesis 
  proof (cases "MList.lookup (accId, tok) accs")
    case None

    hence "moneyInAccount accId tok accs = 0"
      by auto

    with False accIsValid None show ?thesis   
      using assetsInAccounts_distrib_insert by force

  next
    case (Some existingVal)
    
    hence "moneyInAccount accId tok accs = existingVal"
      by auto

    with False accIsValid Some  show ?thesis    
  
    using assetsInAccounts_distrib_insert 
      by simp

  qed
qed


subsection "Add money to account" 


lemma positiveAccounts_implies_positiveMoneyInAccount :
"
\<lbrakk> valid_map accs
; allAccountsPositive accs 
\<rbrakk> \<Longrightarrow>
  moneyInAccount accId tok accs \<ge> 0" 
proof (cases "lookup (accId, tok) accs")
  case None
  then show ?thesis 
    by simp
next
  assume assm: "allAccountsPositive accs" "valid_map accs"
  case (Some val)
  then have "moneyInAccount accId tok accs = val" 
    by force
  with assm Some show ?thesis 
    using allAccountsPositive_implies_lookup_is_positive by fastforce
qed

lemma addMoneyToAccount_distrib:
  assumes "allAccountsPositive accs" and "valid_map accs" 
  shows "assetsInAccounts' (addMoneyToAccount accId tok val accs) = assetsInAccounts' accs + asset tok (nat val)"

proof (cases "val \<le> 0")
  assume "val \<le> 0"
  with assetOfNegInt show ?thesis
    by auto    
next 
  note assms
  moreover assume "\<not> val \<le> 0"

  moreover have "moneyInAccount accId tok accs \<ge> 0" 
    using assms positiveAccounts_implies_positiveMoneyInAccount by blast

  moreover have "nat (moneyInAccount accId tok accs + val) = nat (moneyInAccount accId tok accs) + nat val"
    by (meson calculation nat_add_distrib nle_le)

  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) AssetsPreservation.assetsInAccounts'.elims Groups.group_cancel.add1 Groups.ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add Orderings.preorder_class.order.trans Semantics.addMoneyToAccount.simps accountAssets_leq_assetsInAccount assetsDistributesPlus assetsInAccounts_distrib_on_update fromSemanticAccountsIsFinite moneyInAccount_leq_accountAssets)
qed
  


section "Assets in state"


fun assetsInState :: "State \<Rightarrow> Assets" where
"assetsInState state = assetsInAccounts' (accounts state)"


lemma state_account_red : "accounts (state\<lparr> accounts := a\<rparr>) = a"
  by simp

section "Assets in payment"

fun assetsInPayment :: "Payment \<Rightarrow> Assets" where
"assetsInPayment (Payment _ (Party _) tok val) = asset tok (nat val)" |
"assetsInPayment (Payment _ (Account _) _ _) = 0"

fun assetsInPayments :: "Payment list \<Rightarrow> Assets" where
"assetsInPayments (Cons h t) = assetsInPayment h + assetsInPayments t" |
"assetsInPayments Nil = 0"

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

lemma assetsInAccountIsZero_iff_AccsIsNil: "(assetsInAccounts' accs = 0 \<and> allAccountsPositive accs) \<longleftrightarrow> (accs = Nil) "
proof - 
  have "accs = Nil \<Longrightarrow> allAccountsPositive accs"
    by simp

  moreover have "accs = Nil \<Longrightarrow> assetsInAccounts' accs = 0" 
    by simp

  moreover have "assetsInAccounts' accs = 0 \<and> allAccountsPositive accs \<Longrightarrow> accs = Nil"
    proof (rule ccontr)
      assume "assetsInAccounts' accs = 0 \<and> allAccountsPositive accs" 

      moreover assume "\<not> accs = Nil"
    
      moreover obtain hAccId hTok hVal rest where "accs = ((hAccId, hTok), hVal) # rest"
        using Semantics.refundOne.cases calculation by blast

      moreover have "hVal > 0" 
        using calculation allAccountsPositiveMeansFirstIsPositive by blast

      moreover have "assetsInAccounts' accs = assetsInAccounts' rest + asset hTok (nat hVal)"     
        using assetsInAccountCons calculation by presburger

      ultimately show False
        by (metis assetValueOfSingleAsset assetValueOfZero linorder_not_le nat_0_iff zero_eq_add_iff_both_eq_0)
    qed

  ultimately show ?thesis 
    by meson 
qed

theorem refundOnePreservesAssets : 
  assumes "allAccountsPositive accs"
  shows "
    assetsInAccounts' accs = (
      case (refundOne accs) of
        Some ((accId, tok, val), rest) \<Rightarrow> assetsInAccounts' rest + asset tok (nat val)
      | None \<Rightarrow> 0
    )
  "
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

  ultimately show ?thesis 
    by (smt (verit, ccfv_threshold) option.discI option.simps(5) refundOne.elims allAccountsPositiveMeansFirstIsPositive assetsInAccountCons assms case_prod_conv)

qed


subsection "Reduce contract step"

(* 
TODO: simplify and move to accounts positive *)
lemma updateMoneyIsPositive :
  assumes "allAccountsPositive accs" 
    and "valid_map accs" 
    and "val \<ge> 0"
  shows "allAccountsPositive (updateMoneyInAccount accId token val accs)"
proof (cases "val = 0")
  note assms
  moreover assume "val = 0"
  moreover have "updateMoneyInAccount accId token val accs = MList.delete (accId, token) accs"
    using calculation(4) by force
  
  ultimately show ?thesis
    (* TODO: this should be easier, we should unify
       positiveMoneyInAccountOrNoAccount and allAccountsPositive to avoid unecesary conversion *)
    by (metis MList_delete_preserves_gtZero allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount delete_valid positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive)
next
  note assms
  moreover assume "val \<noteq> 0"

  moreover have "updateMoneyInAccount accId token val accs = MList.insert (accId, token) val accs"
    using calculation(3) calculation(4) by force

  ultimately show ?thesis 
    (* TODO: same note as before *)
    by (smt (verit, del_insts) PositiveAccounts.positiveMoneyInAccountOrNoAccount.simps addMoneyToAccountPositve_match allAccountsPositiveImpliesPositiveMoneyInAccountOrNoAccount insert_lookup_different positiveMoneyInAccountOrNoAccountImpliesAllAccountsPositive updateMoneyInAccount_preserves_valid_map)
qed


lemma transferBetweenAccountsPreservesMoney : 
  assumes "balance = moneyInAccount payFrom token accs"
    and "paidMoney \<ge> 0"
    and "paidMoney \<le> balance" 
    and "valid_map accs" 
    and "allAccountsPositive accs"
  shows "assetsInAccounts' accs 
         = assetsInAccounts'
            (addMoneyToAccount payTo token paidMoney
              (updateMoneyInAccount payFrom token (balance - paidMoney) accs
              )
            )
        "
proof -
  have "nat (balance - paidMoney) = nat balance - nat paidMoney" 
    using assms nat_diff_distrib by presburger
  
  moreover have "nat balance - nat paidMoney + nat paidMoney = nat balance"
    using assms by force

  moreover have "asset token (nat balance) \<le> assetsInAccounts' accs"   
    using calculation assms 
    by (metis assetsInAccounts'.simps accountAssets_leq_assetsInAccount fromSemanticAccountsIsFinite moneyInAccount_leq_accountAssets order_trans)

  moreover have "allAccountsPositive (updateMoneyInAccount payFrom token (balance - paidMoney) accs)"
    using assms
    by (metis diff_ge_0_iff_ge updateMoneyIsPositive)

  ultimately show ?thesis 
    by (smt (verit, ccfv_threshold) semigroup_add_class.add.assoc addMoneyToAccount_distrib assetsDistributesPlus assetsInAccounts_distrib_on_update assms diff_add updateMoneyInAccount_preserves_valid_map)

qed


fun assetsInReduceEffect :: "ReduceEffect \<Rightarrow> Assets" where
"assetsInReduceEffect (ReduceWithPayment p) = assetsInPayment p" |
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
  proof (cases "moneyToPay \<le> 0 ")
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
         payTo account
       *)
      case (Account payToInternal)
      moreover have "assetsInReduceEffect effect = 0" 
        by (simp add: calculation  reducedEffect)
      moreover have "assetsInState newState = assetsInAccounts' ( addMoneyToAccount payToInternal payTok paidMoney accsWOFrom)"
        by (metis letBindings(5) reducedState  Account AssetsPreservation.assetsInState.simps Product_Type.prod.inject Semantics.giveMoney.elims SemanticsTypes.Payee.simps(5) state_account_red)
      ultimately show ?thesis       
        by (smt (verit, best) AssetsPreservation.assetsInState.elims PositiveAccounts.allAccountsPositiveState.elims(2) PositiveAccounts.validAndPositive_state.simps add_cancel_right_left assms(1) balanceNatSplit diff_le_self letBindings(1) letBindings(3) letBindings(4) nat_le_eq_zle paidMoney_leq_balance positiveAccounts_implies_positiveMoneyInAccount transferBetweenAccountsPreservesMoney validAccountMap)      
    next
      (* If the pay is external, the assets of the effect are the paid money, and the assets in the account are the ones without the paid money *)      
      case (Party payToExternal)

      moreover have "assetsInReduceEffect effect = asset payTok (nat paidMoney)"
        using AssetsPreservation.assetsInPayment.simps(1) AssetsPreservation.assetsInReduceEffect.simps(1) calculation reducedEffect by presburger
      moreover have  "finalAccs = accsWOFrom"
        using letBindings calculation by simp
      moreover have "assetsInState newState = assetsInAccounts' accsWOFrom"        
        by (metis state_account_red reducedState  AssetsPreservation.assetsInState.simps calculation(3))    
      ultimately show ?thesis 
        by (smt (verit, best) AssetsPreservation.assetsInAccounts'.elims AssetsPreservation.assetsInState.elims Groups.ab_semigroup_add_class.add.commute Groups.ab_semigroup_add_class.add.left_commute Groups.ordered_cancel_comm_monoid_diff_class.add_diff_inverse accountAssets_leq_assetsInAccount assetsDistributesPlus assetsInAccounts_distrib_on_update balanceNatSplit fromSemanticAccountsIsFinite letBindings(1) letBindings(3) letBindings(4) moneyInAccount_leq_accountAssets nat_mono order_trans paidMoney_leq_balance validAccountMap)
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
  


section "DELETE"


definition "t1 = Token (BS '''') (BS '''')"
definition "t2 = Token (BS ''a'') (BS '''')"
definition "t3 = Token (BS ''c'') (BS '''')"

definition "a1 = asset t1 2"
definition "a2 = asset t1 1 + asset t2 4 + asset t2 1"
definition "a3 = a1 - a2"
definition "a4 = a1 + a2"



value "assetValue t1 a1"
value "assetValue t1 a2"
value "assetValue t2 a2"

value "assetValue t1 a3"
value "assetValue t2 a3"

value "assetValue t1 a4"
value "assetValue t2 a4"

definition "acc1 = Role (BS ''a'')"
definition "acc2 = Role (BS ''b'')"

definition "sAccounts1 = [((acc1, t1), 2)]"

definition "assets1 = assetsInAccounts (fromSemanticAccounts sAccounts1)"

(*value "assetValue t1 assets1"*)


(*
instantiation Assets :: finite
begin
instance 
  apply standard
end
*)
 
end