
(*<*)
theory SemanticsGuarantees
imports SemanticsTypes "HOL-Library.Product_Lexorder" Util.MList 
begin
(*>*)

section "Party linorder"
instantiation "Party" :: "ord"
begin

definition less_eq_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where 
  "less_eq_Party a b = (case (a, b) of 
      ((Address _), (Role _)) \<Rightarrow> True
    | ((Role _),(Address _)) \<Rightarrow> False
    | ((Address x), (Address y)) \<Rightarrow> x \<le> y
    | ((Role x), (Role y)) \<Rightarrow> x \<le> y
  )"
declare less_eq_Party_def [simp add]

definition less_Party :: "Party \<Rightarrow> Party \<Rightarrow> bool" where 
  "less_Party a b \<longleftrightarrow> \<not> ( b \<le> a)"

declare less_Party_def [simp add]

instance ..

end


instantiation "Party" :: linorder
begin
instance
proof
  fix x y z :: Party

  show linearParty: "x \<le> y \<or> y \<le> x"    
    by (cases x;cases y) auto
    
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using linearParty by auto
 
  show "x \<le> x" 
    by (cases x) auto 

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"    
    by (cases x; cases y; cases z) auto
    
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"    
    by (cases x; cases y) auto
qed
end

section "Token linorder"

instantiation "Token" :: "ord"
begin
definition less_eq_Token :: "Token \<Rightarrow> Token \<Rightarrow> bool" where 
  "less_eq_Token a b = (case (a, b) of 
    (Token currencyA tokenA, Token currencyB tokenB) \<Rightarrow> 
      if currencyA < currencyB then True 
      else if (currencyB < currencyA) then False 
      else tokenA \<le> tokenB
    )
   "
declare less_eq_Token_def [simp add]

definition less_Token :: "Token \<Rightarrow> Token \<Rightarrow> bool" where 
  "less_Token a b \<longleftrightarrow> \<not> (b \<le> a)"
declare less_Token_def [simp add]

instance ..
end

instantiation "Token" :: linorder
begin
instance
proof
  fix x y z :: Token    
  show linearToken: "x \<le> y \<or> y \<le> x"
    by (cases x;cases y) auto

  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" 
    using less_Token_def linearToken by presburger

  show "x \<le> x" 
    by (cases x) simp 

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (cases x; cases y; cases z)
    apply auto
    apply (metis linorder_neqE order_less_trans)
    by (metis leD order_le_less order_less_trans)    

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (cases x; cases y)
    apply auto  
    apply (meson linorder_neqE order_less_imp_not_less)
    by (metis order_le_less order_less_asym')  
qed
end

section "ChoiceId linorder"

instantiation "ChoiceId" :: "ord"
begin
definition less_eq_ChoiceId :: "ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> bool" where 
  "less_eq_ChoiceId a b = (case (a, b) of 
    (ChoiceId nameA partyA, ChoiceId nameB partyB) \<Rightarrow>
      if nameA < nameB then True 
      else if nameB < nameA then False 
      else partyA \<le> partyB
  )"

declare less_eq_ChoiceId_def [simp add]

definition less_ChoiceId :: "ChoiceId \<Rightarrow> ChoiceId \<Rightarrow> bool" where 
  "less_ChoiceId a b \<longleftrightarrow> \<not> (b \<le> a)"

declare less_ChoiceId_def [simp add]
instance
proof
qed
end

instantiation "ChoiceId" :: linorder
begin
instance
proof
  fix x y z :: ChoiceId

  show linearChoiceId: "x \<le> y \<or> y \<le> x"
    apply (cases x; cases y)
    apply auto
    by (smt (verit, del_insts) case_prod_conv less_eq_Party_def nle_le)

  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using linearChoiceId less_ChoiceId_def
    by presburger
   
  show "x \<le> x"     
    using less_eq_Party_def by (cases x) fastforce

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (cases x; cases y; cases z)
    apply auto
    apply (metis linorder_less_linear order_less_trans)
    by (smt (verit, best) Orderings.preorder_class.dual_order.trans case_prod_conv less_eq_Party_def not_less_iff_gr_or_eq)
    
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (cases x; cases y)
    apply auto    
    by (meson nle_le not_less_iff_gr_or_eq)+  
qed
end


section "ValueId linorder"

instantiation "ValueId" :: "ord"
begin

definition less_eq_ValueId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where
  "less_eq_ValueId a b = (case (a, b) of 
    (ValueId a, ValueId b) \<Rightarrow> a \<le> b
  )"
declare less_eq_ValueId_def [simp add]

definition less_ValueId :: "ValueId \<Rightarrow> ValueId \<Rightarrow> bool" where 
  "less_ValueId a b = (case (a, b) of 
    (ValueId a, ValueId b) \<Rightarrow> a < b
  )"

declare less_ValueId_def [simp add]
instance ..
end

instantiation "ValueId" :: linorder
begin
instance
proof
  fix x y z :: ValueId
  show linearValueId: "x \<le> y \<or> y \<le> x" 
    by (cases x;cases y) auto
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (cases x;cases y) auto

  show "x \<le> x" 
    by (cases x) simp

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x;cases y;cases z) auto

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x;cases y) auto
qed
end


fun valid_state :: "State \<Rightarrow> bool" where
"valid_state state = (valid_map (accounts state)
                     \<and> valid_map (choices state)
                     \<and> valid_map (boundValues state))"

(*<*)
end
(*>*)

