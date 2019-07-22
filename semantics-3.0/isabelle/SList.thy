theory SList
imports Main
begin

fun valid_set :: "'a::linorder list \<Rightarrow> bool" where
  "valid_set x = (List.distinct x \<and> List.sorted x)"

definition empty :: "'a::linorder list" where
  "empty = Nil"

lemma valid_empty : "valid_set empty"
  by (simp add:SList.empty_def)

fun insert :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert a Nil = Cons a Nil" |
  "insert a (Cons x z) =
    (if a < x
     then (Cons a (Cons x z))
     else (if a > x
           then (Cons x (insert a z))
           else (Cons x z)))"

lemma insert_in_middle : "x < a \<Longrightarrow> valid_set (a # z)
                            \<Longrightarrow> valid_set (x # a # z)"
  by auto

lemma remove_from_middle : "valid_set (x # a # z) \<Longrightarrow> x < a"
  by auto

lemma sublist_valid : "valid_set (x # c) \<Longrightarrow>
                       valid_set c"
  by simp

lemma insert_valid_aux :
  "x < a \<Longrightarrow>
   valid_set (x # c) \<Longrightarrow>
   valid_set (SList.insert a c) \<Longrightarrow>
   valid_set (x # SList.insert a c)"
  apply (induction c arbitrary: a x)
  apply auto[1]
  by (metis insert.simps(2) insert_in_middle remove_from_middle)

lemma insert_valid_aux2 :
  "(\<And>a. valid_set c \<Longrightarrow> valid_set (SList.insert a c)) \<Longrightarrow>
    valid_set (x # c) \<Longrightarrow>
    x < a \<Longrightarrow>
    valid_set (x # SList.insert a c)"
  using insert_valid_aux sublist_valid by blast

lemma insert_valid_aux3 :
  "(\<And>a. valid_set c \<Longrightarrow> valid_set (SList.insert a c)) \<Longrightarrow>
   valid_set (x # c) \<Longrightarrow> valid_set (SList.insert a (x # c))"
  apply (simp only:insert.simps)
  apply (cases "a < x")
  apply auto[1]
  apply (cases "x < a")
  apply (smt insert_valid_aux2)
  by auto

theorem insert_valid : "valid_set c \<Longrightarrow> valid_set (SList.insert a c)"
  apply (induction c arbitrary:a)
  apply simp
  using insert_valid_aux3 by blast

fun delete :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delete a Nil = Nil" |
  "delete a (Cons x z) =
    (if a = x
     then z
     else (if a > x
           then (Cons x (delete a z))
           else (Cons x z)))"

lemma delete_valid_aux :
  "valid_set (a # c) \<Longrightarrow> valid_set (a # delete b c)"
  apply (induction c arbitrary: a b)
  apply simp
  by fastforce

lemma delete_valid_aux2 :
  "(\<And>a. valid_set c \<Longrightarrow> valid_set (delete a c)) \<Longrightarrow>
   valid_set (b # c) \<Longrightarrow> valid_set (delete a (b # c))"
  using delete_valid_aux by auto

theorem delete_valid : "valid_set c \<Longrightarrow> valid_set (SList.delete a c)"
  apply (induction c arbitrary: a)
  apply auto[1]
  using delete_valid_aux2 by blast

fun element :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> bool" where
  "element a Nil = False" |
  "element a (Cons x z) =
    (if a = x
     then True
     else (if a > x
           then element a z
           else False))"

lemma delete_lookup_None_aux :
  "valid_set (c # b) \<Longrightarrow> element c b = False"
  by (metis element.elims(2) not_less_iff_gr_or_eq remove_from_middle)

lemma delete_lookup_None_aux2 :
  "(valid_set b \<Longrightarrow> element a (delete a b) = False) \<Longrightarrow>
   valid_set (c # b) \<Longrightarrow> element a (delete a (c # b)) = False"
  using delete_lookup_None_aux by auto

theorem delete_lookup_None : "valid_set b \<Longrightarrow>
                              SList.element a (SList.delete a b) = False"
  apply (induction b)
  apply simp
  using delete_lookup_None_aux2 by fastforce

theorem insert_lookup_Some : "valid_set c \<Longrightarrow>
                              SList.element a (SList.insert a c) = True"
  apply (induction c)
  apply simp
  by force

lemma different_delete_lookup_aux :
  "(valid_set c \<Longrightarrow> a \<noteq> b \<Longrightarrow> element a (delete b c) = element a c) \<Longrightarrow>
   valid_set (x # c) \<Longrightarrow>
   a \<noteq> b \<Longrightarrow> element a (delete b (x # c)) = element a (x # c)"
  by (metis (full_types) delete.simps(2) delete_lookup_None_aux
      delete_valid_aux element.simps(2) insert_in_middle
      not_less_iff_gr_or_eq sublist_valid)

theorem different_delete_lookup :
  "valid_set c \<Longrightarrow> a \<noteq> b \<Longrightarrow>
   SList.element a (SList.delete b c) = SList.element a c"
  apply (induction c)
  apply simp
  using different_delete_lookup_aux by blast

end
