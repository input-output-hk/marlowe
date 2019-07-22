theory MList
imports Main
begin

fun valid_map :: "('a::linorder \<times> 'b) list \<Rightarrow> bool" where
  "valid_map x = (let y = map fst x in
                  (List.distinct y \<and> List.sorted y))"

definition empty :: "('a::linorder \<times> 'b) list" where
  "empty = Nil"

lemma valid_empty : "valid_map empty"
  by (simp add:MList.empty_def)

fun insert :: "'a::linorder \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "insert a b Nil = Cons (a, b) Nil" |
  "insert a b (Cons (x, y) z) =
    (if a < x
     then (Cons (a, b) (Cons (x, y) z))
     else (if a > x
           then (Cons (x, y) (insert a b z))
           else (Cons (x, b) z)))"

lemma insert_in_middle : "x < a \<Longrightarrow> valid_map ((a, b) # z)
                            \<Longrightarrow> valid_map ((x, y) # (a, c) # z)"
  by auto

lemma remove_from_middle : "valid_map ((x, y) # (a, b) # z) \<Longrightarrow> x < a"
  by auto

lemma sublist_valid : "valid_map ((x, y) # c) \<Longrightarrow>
                       valid_map c"
  by simp

lemma insert_valid_aux :
  "x < a \<Longrightarrow>
   valid_map ((x, y) # c) \<Longrightarrow>
   valid_map (MList.insert a b c) \<Longrightarrow>
   valid_map ((x, y) # MList.insert a b c)"
  apply (induction c arbitrary: a b x y)
  apply auto[1]
  by (metis (no_types, hide_lams) insert.simps(2)
            insert_in_middle prod.collapse remove_from_middle)

lemma insert_valid_aux2 :
  "(\<And>a b. valid_map c \<Longrightarrow> valid_map (MList.insert a b c)) \<Longrightarrow>
    valid_map ((x, y) # c) \<Longrightarrow>
    x < a \<Longrightarrow>
    valid_map ((x, y) # MList.insert a b c)"
  by (meson insert_valid_aux sublist_valid)

lemma insert_valid_aux3 :
  "(\<And>a b. valid_map c \<Longrightarrow> valid_map (MList.insert a b c)) \<Longrightarrow>
   valid_map ((x, y) # c) \<Longrightarrow> valid_map (MList.insert a b ((x, y) # c))"
  apply (simp only:insert.simps)
  apply (cases "a < x")
  apply auto[1]
  apply (cases "x < a")
  apply (smt insert_valid_aux2)
  by auto

theorem insert_valid : "valid_map c \<Longrightarrow> valid_map (MList.insert a b c)"
  apply (induction c arbitrary:a b)
  apply simp
  by (metis insert_valid_aux3 old.prod.exhaust)

fun delete :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "delete a Nil = Nil" |
  "delete a (Cons (x, y) z) =
    (if a = x
     then z
     else (if a > x
           then (Cons (x, y) (delete a z))
           else (Cons (x, y) z)))"

lemma delete_valid_aux :
  "valid_map (a # c) \<Longrightarrow> valid_map (a # delete b c)"
  apply (induction c arbitrary: a b)
  apply simp
  by fastforce

lemma delete_valid_aux2 :
  "(\<And>a. valid_map c \<Longrightarrow> valid_map (delete a c)) \<Longrightarrow>
   valid_map (b # c) \<Longrightarrow> valid_map (delete a (b # c))"
  apply (cases "b")
  apply (simp only:delete.simps)
  by (smt delete_valid_aux sublist_valid)

theorem delete_valid : "valid_map c \<Longrightarrow> valid_map (MList.delete a c)"
  apply (induction c arbitrary: a)
  apply auto[1]
  using delete_valid_aux2 by blast

fun lookup :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup a Nil = None" |
  "lookup a (Cons (x, y) z) =
    (if a = x
     then Some y
     else (if a > x
           then lookup a z
           else None))"

lemma delete_lookup_None_aux :
  "valid_map ((c, d) # b) \<Longrightarrow> lookup c b = None"
  by (metis lookup.elims order.asym remove_from_middle)

lemma delete_lookup_None_aux2 :
  "(valid_map b \<Longrightarrow> lookup a (delete a b) = None) \<Longrightarrow>
   valid_map ((c, d) # b) \<Longrightarrow> lookup a (delete a ((c, d) # b)) = None"
  apply (cases "a > c")
  apply auto[1]
  apply (cases "a = c")
  apply (simp only:delete.simps lookup.simps)
  apply (simp add: delete_lookup_None_aux)
  by auto

theorem delete_lookup_None : "valid_map b \<Longrightarrow>
                              MList.lookup a (MList.delete a b) = None"
  apply (induction b)
  apply simp
  using delete_lookup_None_aux2 by fastforce

theorem insert_lookup_Some : "valid_map c \<Longrightarrow>
                              MList.lookup a (MList.insert a b c) = Some b"
  apply (induction c)
  apply simp
  by force

lemma different_delete_lookup_aux :
  "(valid_map c \<Longrightarrow> a \<noteq> b \<Longrightarrow> lookup a (delete b c) = lookup a c) \<Longrightarrow>
   valid_map ((x, y) # c) \<Longrightarrow>
   a \<noteq> b \<Longrightarrow> lookup a (delete b ((x, y) # c)) = lookup a ((x, y) # c)"
  by (metis delete.simps(2) delete_lookup_None_aux delete_valid insert_in_middle lookup.simps(2) not_less_iff_gr_or_eq)

theorem different_delete_lookup :
  "valid_map c \<Longrightarrow> a \<noteq> b \<Longrightarrow>
   MList.lookup a (MList.delete b c) = MList.lookup a c"
  apply (induction c)
  apply simp
  by (metis different_delete_lookup_aux old.prod.exhaust)

end
