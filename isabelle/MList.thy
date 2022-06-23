theory MList
imports Main Utils
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

lemma insert_length : "length (insert a b c) \<le> (length c + 1)"
  apply (induction c)
  by auto

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
  by (metis (no_types, opaque_lifting) insert.simps(2)
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

lemma delete_length : "length (delete a b) \<le> length b"
  apply (induction b)
  by auto

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

lemma delete_step :
  "valid_map ((k, v) # t) \<Longrightarrow>
   \<not> k2 = k \<Longrightarrow>
   MList.delete k2 ((k, v) # t) = ((k, v)#(MList.delete k2 t))"
  apply (induction t)
  by auto

fun lookup :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup a Nil = None" |
  "lookup a (Cons (x, y) z) =
    (if a = x
     then Some y
     else (if a > x
           then lookup a z
           else None))"

lemma lookup_empty : "MList.lookup y MList.empty = None"
  by (simp add: MList.empty_def)

lemma insert_existing_length : "MList.lookup k l = Some a \<Longrightarrow>
                                length (MList.insert k v l) = length l"
  apply (induction l)
  apply simp
  using not_less_iff_gr_or_eq by fastforce

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

theorem insert_lookup_Some : "MList.lookup a (MList.insert a b c) = Some b"
  apply (induction c)
  apply simp
  by force

theorem insert_lookup_different : "a \<noteq> b \<Longrightarrow> MList.lookup a (MList.insert b c d) = MList.lookup a d"
  apply (induction d)
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

fun unionWith :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow>
                  ('a \<times> 'b) list \<Rightarrow> (('a::linorder) \<times> 'b) list" where
"unionWith f (Cons (x, y) t) (Cons (x2, y2) t2) =
  (if x < x2
   then Cons (x, y) (unionWith f t (Cons (x2, y2) t2))
   else (if x > x2
         then Cons (x2, y2) (unionWith f (Cons (x, y) t) t2)
         else Cons (x, f y y2) (unionWith f t t2)))" |
"unionWith f Nil l = l" |
"unionWith f l Nil = l"

lemma unionWithMonotonic1 :
  "x < x2 \<Longrightarrow> fst ( hd ( unionWith f ((x, y) # t) ((x2, y2) # t2) ) ) = x"
  by simp

lemma insert_before :
  "valid_map c \<Longrightarrow> x < fst ( hd ( c ) ) \<Longrightarrow> valid_map ((x, y) # c)"
  by (metis insert.simps(1) insert_in_middle insert_valid list.exhaust list.sel(1) prod.collapse)

lemma insert_before_union :
  "x < x2 \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x2, y2) # t2) \<Longrightarrow>
   x < fst ( hd ( unionWith f t ((x2, y2) # t2) ) )"
  apply (induction t)
  apply auto[1]
  by auto

lemma insert_before_union2 :
  "x2 < x \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x2, y2) # t2) \<Longrightarrow>
   x2 < fst ( hd ( unionWith f ((x, y) # t) t2 ) )"
  apply (induction t2)
  apply auto[1]
  by force

lemma insert_before_union3 :
  "valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x, y2) # t2) \<Longrightarrow>
   (t \<noteq> [] \<or> t2 \<noteq> []) \<Longrightarrow>
   x < fst ( hd ( unionWith f t t2 ) )"
  apply (induction t)
  apply (metis list.collapse prod.collapse remove_from_middle unionWith.simps(2))
  apply (induction t2)
  apply auto[1]
  by auto

lemma unionWithValidLT_aux :
  "x < x2 \<Longrightarrow>
    (valid_map (unionWith f t ((x2, y2) # t2))) \<Longrightarrow>
    valid_map ((x, y) # t) \<Longrightarrow>
    valid_map ((x2, y2) # t2) \<Longrightarrow>
    valid_map ((x, y) # unionWith f t ((x2, y2) # t2))"
  by (meson insert_before insert_before_union)

lemma unionWithValidLT :
  "x < x2 \<Longrightarrow>
   (valid_map t \<Longrightarrow>
    valid_map ((x2, y2) # t2) \<Longrightarrow>
    valid_map (unionWith f t ((x2, y2) # t2))) \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x2, y2) # t2) \<Longrightarrow>
   valid_map (unionWith f ((x, y) # t) ((x2, y2) # t2))"
  apply (simp only:unionWith.simps sublist_valid)
  by (meson unionWithValidLT_aux)

lemma unionWithValidGT_aux :
  "x2 < x \<Longrightarrow>
   (valid_map (unionWith f ((x, y) # t) t2)) \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x2, y2) # t2) \<Longrightarrow>
   valid_map ((x2, y2) # unionWith f ((x, y) # t) t2)"
  by (meson insert_before insert_before_union2)

lemma unionWithValidGT :
  "x2 < x \<Longrightarrow>
   (valid_map ((x, y) # t) \<Longrightarrow>
    valid_map t2 \<Longrightarrow> valid_map (unionWith f ((x, y) # t) t2)) \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x2, y2) # t2) \<Longrightarrow>
   valid_map (unionWith f ((x, y) # t) ((x2, y2) # t2))"
  apply (simp only:unionWith.simps sublist_valid)
  by (smt order.asym unionWithValidGT_aux)

lemma unionWithValidEQ_aux :
  "(valid_map (unionWith f t t2)) \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x, y2) # t2) \<Longrightarrow>
   valid_map ((x, f y y2) # unionWith f t t2)"
  by (metis insert.simps(1) insert_before insert_before_union3 insert_valid unionWith.simps(2))

lemma unionWithValidEQ :
  "(valid_map t \<Longrightarrow> valid_map t2 \<Longrightarrow> valid_map (unionWith f t t2)) \<Longrightarrow>
   valid_map ((x, y) # t) \<Longrightarrow>
   valid_map ((x, y2) # t2) \<Longrightarrow>
   valid_map (unionWith f ((x, y) # t) ((x, y2) # t2))"
  apply (simp only:unionWith.simps sublist_valid)
  by (smt order.asym unionWithValidEQ_aux)

theorem unionWithValid : "valid_map a \<Longrightarrow> valid_map b \<Longrightarrow>
                          valid_map (unionWith f a b)"
  apply (induction f a b rule:unionWith.induct)
  apply (metis less_linear unionWithValidEQ unionWithValidGT unionWithValidLT)
  by auto

theorem unionWithSym : "valid_map a \<Longrightarrow> valid_map b \<Longrightarrow>
                        unionWith f a b = unionWith (flip f) b a"
  apply (induction f a b rule:unionWith.induct)
  apply auto[1]
  apply (metis list.exhaust unionWith.simps(2) unionWith.simps(3))
  by simp

fun findWithDefault :: "'b \<Rightarrow> 'a \<Rightarrow> (('a::linorder) \<times> 'b) list \<Rightarrow> 'b" where
"findWithDefault d k l = (case lookup k l of
                            None \<Rightarrow> d
                          | Some x \<Rightarrow> x)"

lemma findWithDefault_step :
  "valid_map ((k, v) # tail) \<Longrightarrow>
   k2 \<noteq> k \<Longrightarrow>
   findWithDefault d k2 ((k, v) # tail) = findWithDefault d k2 tail"
  apply simp
  apply (induction tail)
  by auto

fun member :: "'a \<Rightarrow> ((('a::linorder) \<times> 'b) list) \<Rightarrow> bool" where
"member k d = (lookup k d \<noteq> None)"

end
