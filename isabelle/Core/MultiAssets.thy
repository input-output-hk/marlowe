theory MultiAssets
imports Semantics
begin

section "Assets"

text "We represent Multi-token assets as a function from Token to natural numbers."
(*
TODO: I want to replace Asset definition with
typedef Assets = "{assets. (\<forall> t v. fmlookup assets t = Some v \<longrightarrow> v > 0)} :: ((Token, nat) fmap) set

but I need to solve this issue https://isabelle.zulipchat.com/#narrow/stream/238552-Beginner-Questions/topic/Is.20it.20possible.20to.20create.20a.20typedef.20.20of.20a.20typedef.3F/near/340510660
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

lemma assetValueOfSingleAsset [simp] : "assetValue tok (asset tok b) = b"
  by transfer simp

lemma assetValueOfDifferentToken [simp] : "tok1 \<noteq> tok2 \<Longrightarrow> assetValue tok1 (asset tok2 b) = 0"
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
    is "\<lambda>a b. \<forall>t. a t \<le> b t" .
  
  lift_definition less_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> bool"
    is "\<lambda>a b. (\<forall>rt. a rt \<le> b rt) \<and> (\<exists> st. a st < b st)" .
  
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
    show "a \<le> b \<Longrightarrow>  b \<le> a \<Longrightarrow> a = b"
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
lemma assetZero [simp] : "asset tok 0 = 0"
  by transfer auto

text "If we try to create a single asset from a negative integer is also the same as creating the zero_Assets"
corollary assetOfNegInt [simp] : "(i :: int) \<le> 0 \<Longrightarrow> asset t (nat i) = 0"
  by simp

text "Trying to count the amount of tokens of the zero_Assets is 0"
lemma assetValueOfZero [simp] : "assetValue t 0 = 0"
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

lemma assetValue_distrib : "assetValue tok (a + b) = assetValue tok a + assetValue tok b"
  by transfer auto

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

end
