theory MultiAssets
imports SemanticsTypes
begin

section "Assets"
typedef Assets = "{assets :: Token \<rightharpoonup> nat. finite (dom assets) \<and> (\<forall> t v. assets t = Some v \<longrightarrow> v > 0)}"
  apply (rule_tac x = "\<lambda>t. None" in exI)
  by simp


setup_lifting type_definition_Assets

lift_definition asset :: "Token \<Rightarrow> nat \<Rightarrow> Assets" 
  is "\<lambda>tok val. if val = 0 then Map.empty else [tok \<mapsto> val]"
  by simp


lift_definition assetValue :: "Token \<Rightarrow> Assets \<Rightarrow> nat" is 
  "\<lambda>t a. case a t of None \<Rightarrow> 0 | Some v \<Rightarrow> v" .



subsection "Arithmetic"
instantiation Assets :: zero
begin

lift_definition zero_Assets :: Assets
  is "Map.empty"
  by simp

instance ..
end

instantiation Assets :: plus
begin

(* TODO: simplify *)
lift_definition plus_Assets :: "Assets \<Rightarrow> Assets \<Rightarrow> Assets" 
  is "\<lambda>x y. \<lambda>tok. combine_options (+) (x tok) (y tok)"
  subgoal for a b
  proof -
    let ?f = "\<lambda>tok. combine_options (+) (a tok) (b tok)"
    assume assm: "finite (dom a) \<and> (\<forall> t v. a t = Some v \<longrightarrow> v > 0)" "finite (dom b) \<and> (\<forall> t v. b t = Some v \<longrightarrow> v > 0)"

    then have 0: "\<And>tok. tok \<in> dom a \<Longrightarrow> ?f tok \<noteq> None"
      by (metis (mono_tags, opaque_lifting) Option.option.distinct(1) combine_options_simps(2) combine_options_simps(3) domD domIff)
    then have 1: "\<And> tok. tok \<in> dom b \<Longrightarrow> ?f tok \<noteq> None"
      by (metis combine_options_simps(1) domIff)

    with assm 0 1 have "dom ?f = dom a \<union> dom b" 
      by (smt (z3) Collect_cong Option.option.case(1) combine_options_def domIff dom_def dom_map_add map_add_None)
    
    with assm show ?thesis        
      by (smt (verit, ccfv_threshold) Groups.ab_semigroup_add_class.add.commute Option.option.inject add_gr_0 combine_options_commute combine_options_simps(2) combine_options_simps(3) domD domIff finite_Un)    
  qed
  done

instance ..
end


lemma assetsDistributesPlus : "asset tok (a + b) = asset tok a + asset tok b"
  by transfer auto

lemma assetsJoinPlus : "asset tok a + asset tok b = asset tok (a + b)" 
  by (simp add: assetsDistributesPlus)

(*
lemma assetValue_distrib : "assetValue tok (a + b) = assetValue tok a + assetValue tok b" 
  by transfer auto 
*)


instantiation Assets :: semigroup_add
begin
instance proof
  fix a b c :: Assets 

  show "(a + b) + c = a + (b + c)"
    by transfer (simp add: combine_options_assoc)
qed
end

instantiation Assets :: ab_semigroup_add
begin
instance proof
  fix a b :: Assets

  show "a + b = b + a" 
    by transfer (simp add: combine_options_commute)    
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


section "Get one" 
(*
lift_definition getOne' :: "Assets \<Rightarrow> (Token \<times> nat) list" is 
  "\<lambda>a. map_of (Map.graph a)" sorry
*)

definition asList :: "'a set \<Rightarrow> 'a list" where 
  "asList s = Finite_Set.fold (\<lambda>a b. a # b) [] s"

lemma asListC [code] : "asList a = []" 
  sorry

value "asList {2:: nat}"





value "asList {True}" 
lift_definition getOne :: "Assets \<Rightarrow> (Token \<times> nat \<times> Assets) option" is 
  "\<lambda>a. Finite_Set.fold 
         (\<lambda>entry accu. case accu of None \<Rightarrow> Some (fst entry, snd entry, (\<lambda>_. None))
                       | Some (t, v, rest) \<Rightarrow> Some (t, v, rest)
         )
         None 
         (Map.graph a)
 "
  sorry


lemma getOneCode [code] : "getOne a = None" 
  sorry
(*
lift_definition getOne :: "Assets \<Rightarrow> (Token \<times> nat \<times> Assets) option" is 
  "\<lambda>a. (let ag = (Map.graph a) in (if ag = Set.empty then None else None))" 
  sorry
*)
(*definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"*)
lifting_forget Assets.lifting
end