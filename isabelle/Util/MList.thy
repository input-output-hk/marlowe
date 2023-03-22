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
  by (smt (verit, best) insert.elims insert_in_middle remove_from_middle sublist_valid)

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

lemma insert_replaces_value :
  "valid_map m \<Longrightarrow> MList.insert k v1 (MList.insert k v2 m) = MList.insert k v1 m"
proof (induction m)
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  then obtain hK hV where "head = (hK, hV)"
    by fastforce
  then show ?case
    using Cons.IH Cons.prems by force
qed

lemma insert_swap :
  "\<lbrakk> valid_map m
   ; k1 \<noteq> k2
   \<rbrakk> \<Longrightarrow> MList.insert k1 v1 (MList.insert k2 v2 m) = MList.insert k2 v2 (MList.insert k1 v1 m)"
proof (induction m)
  case Nil
  then show ?case
    by (simp add: not_less_iff_gr_or_eq)
next
  case (Cons head rest)
  then obtain hK hV where pHead: "head = (hK, hV)"
    using prod.exhaust_sel by blast
  then show ?case
  proof (cases rule: linorder_cases[of k2 hK])
    case less
    then show ?thesis
      using Cons.prems(2) pHead by fastforce
  next
    case equal
    then show ?thesis
      using Cons.prems(2) pHead by auto
  next
    case greater
    then show ?thesis
      using Cons.IH Cons.prems(1) Cons.prems(2) pHead by auto
  qed
qed

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

lemma deleteNotMember: "\<lbrakk> \<not> member k m \<rbrakk> \<Longrightarrow> delete k m = m"
proof (induction m)
  case Nil
  then show ?case
    by simp
next
  case (Cons headKeyVal rest)
  obtain hK hV where "headKeyVal = (hK, hV)"
    by fastforce
  with Cons show ?case
    using option.distinct(1) by force
qed

lemma equalMList: "\<lbrakk> valid_map m; valid_map n \<rbrakk> \<Longrightarrow> \<forall>x. lookup x m = lookup x n \<Longrightarrow> m = n"
proof (induction m arbitrary: n)
  case Nil
  then show ?case
    by (metis list.exhaust lookup.simps(1) lookup.simps(2) old.prod.exhaust option.distinct(1))
next
  case (Cons mHead mRest)
  then show ?case
  proof (induction n )
    case Nil
    then show ?case
      by (metis lookup.simps(1) lookup.simps(2) old.prod.exhaust option.distinct(1))
  next
    case (Cons nHead nRest)
    then show ?case
      (* TODO: this takes a little long, simplify *)
      by (metis delete.simps(2) delete_lookup_None_aux different_delete_lookup lookup.simps(2) not_None_eq option.inject order.asym prod.collapse sublist_valid)
  qed
qed

lemma insertDeleted : "\<lbrakk> valid_map m; lookup k m = Some v \<rbrakk> \<Longrightarrow> insert k v (delete k m) = m"
proof (induction m)
  case Nil
  then show ?case
    by simp
next
  case (Cons headKeyVal rest)
  obtain hK hV where headKeyVal: "headKeyVal = (hK, hV)"
    by fastforce
  then have 0: "lookup hK rest = None"
    by (metis Cons.prems(1) delete_lookup_None_aux)
  show ?case
  proof (cases rule: linorder_cases[of hK k])
    case less
    with Cons headKeyVal show ?thesis
      by (metis delete_step insert.simps(2) lookup.simps(2) order.asym sublist_valid)
  next
    case equal
    with equal Cons headKeyVal 0  show ?thesis
      by (smt (verit, best) delete_valid different_delete_lookup equalMList insert_lookup_Some insert_lookup_different insert_valid)
  next
    case greater
    then show ?thesis
      by (metis Cons.prems(2) headKeyVal lookup.simps(2) not_less_iff_gr_or_eq option.discI)
  qed
qed

lemma cons_eq_insert_rest :
"valid_map ((k,v) # rest) \<Longrightarrow>
(k,v) # rest = MList.insert k v rest"
  by (metis delete.simps(2) MList.lookup.simps(2) insertDeleted)

section "As Maps"

lemma insertAsMap : "valid_map mlist \<Longrightarrow> map_of(insert k v mlist) = (map_of mlist) (k\<mapsto>v)"
proof (induction mlist)
  case Nil
  then show ?case
    by auto
next
  case (Cons head rest)
  obtain hK hV where "head = (hK, hV)"
    by fastforce
  then show ?case
    using Cons.IH Cons.prems prod.sel(2) by fastforce
qed

lemma deleteAsMap : "valid_map mlist \<Longrightarrow> map_of (delete k mlist) = (map_of mlist)(k := None)"
proof (induction mlist)
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  obtain hK hV where pHead: "head = (hK, hV)"
    by fastforce
  then show ?case
  by (smt (z3) Cons.IH Cons.prems MList.member.simps delete.simps(2) deleteNotMember delete_lookup_None_aux delete_step fst_conv fun_upd_twist fun_upd_upd map_of.simps(2) sublist_valid)
qed

lemma lookupAsMap : "valid_map mlist \<Longrightarrow> lookup k mlist = (map_of mlist) k"
proof (induction mlist)
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  obtain hK hV where "head = (hK, hV)"
    by fastforce
  then show ?case
    by (smt (verit, ccfv_threshold) Cons.IH Cons.prems deleteNotMember delete_lookup_None delete_step list.inject lookup.simps(2) map_of_Cons_code(2) member.elims(1) sublist_valid)
qed

lemma MList_induct[consumes 1, case_names empty update]:
  assumes "valid_map m"
  assumes "P []"
  assumes "\<And>k v m. valid_map m \<Longrightarrow> \<not> member k m \<Longrightarrow> P m \<Longrightarrow> P (insert k v m)"
  shows "P m"
  using assms(1)
proof(induction m)
  case Nil
  then show ?case by (simp add: assms(2))
next
  case (Cons head rest)
  then obtain hK hV where "head = (hK, hV)"
    by fastforce
  moreover have "valid_map rest"
    using Cons.prems by auto
  moreover have "\<not> member hK rest"
    by (metis Cons.prems MList.member.simps calculation(1) delete_lookup_None_aux)
  moreover have "P rest"
    using Cons.IH calculation(2) by blast
  ultimately  show ?case using assms(3)
    by (metis Cons.prems delete.simps(2) insertDeleted lookup.simps(2))
qed

lemma insertOverDeleted :
  assumes "valid_map m"
  shows "insert k v m = insert k v (delete k m)"
using assms proof (induction m rule: MList_induct)
  case empty
  then show ?case
    by simp
next
  case (update uK uV m)
  then show ?case
    by (smt (verit) delete_valid different_delete_lookup equalMList insert_lookup_Some insert_lookup_different insert_valid)
qed

subsection "keys"

fun keys :: "('k \<times> 'v) list \<Rightarrow> 'k set" where
  "keys m = set (map fst m)"

lemma keys_member_r: "valid_map m \<Longrightarrow> member k m \<longleftrightarrow> k \<in> keys m"
proof (induction m)
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  moreover obtain hK hV where "head = (hK, hV)"
    by fastforce
  moreover have "valid_map rest"
    using calculation by (metis local.Cons.prems sublist_valid)
  moreover have "hK < k \<Longrightarrow> member k rest \<Longrightarrow> k \<in> keys rest"
    using calculation local.Cons.IH by blast
  moreover have "hK < k \<Longrightarrow> k \<in> keys rest \<Longrightarrow> member k rest"
    using calculation local.Cons.IH by blast
  ultimately show ?case
    by (metis keys.elims list.set_map member.simps local.Cons.prems lookupAsMap map_of_eq_None_iff)
qed

section "MList with folds"

text "The following lemma is similar to the second case of the foldr definition, which states

\<^term>\<open>foldr f (x # xs) = f x \<circ> foldr f xs\<close>

Instead of working with Cons this lemma is expressed around MList.insert"

lemma foldr_insert:
  assumes "valid_map m"
  (* We require not having the key in the rest of the list, because otherwise the
     insert would overwrite the value and the lemma would not hold *)
  assumes "\<not> MList.member k m"
  (* We require the function to be commutative over composition because the insert function
    can add the element in any order *)
  assumes "\<forall>a b. f a \<circ> f b = f b \<circ> f a"
  shows "foldr f (MList.insert k v m) = f (k, v) \<circ> foldr f m"
  using assms(1) assms(2) proof (induction m)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  then obtain hK hV where pHead: "head = (hK, hV)"
    by force
  then have "hK \<noteq> k"
    using local.Cons.prems(2) by force
  then show ?case
    by (smt (verit, best) Cons.IH Cons.prems(1) Cons.prems(2) MList.member.simps assms(3) foldr_Cons fun.map_comp insert.simps(2) lookup.simps(2) not_less_iff_gr_or_eq pHead sublist_valid)
qed

text "Similary, \<^term>\<open>foldl_insert\<close> is defined to relate to the foldl second case definition
      \<^term>\<open>foldl f a (x # xs) = foldl f (f a x) xs\<close>"
lemma foldl_insert:
  assumes "valid_map m"
  assumes "\<not> MList.member k m"
  assumes "\<forall> a b z'. f (f z' a) b = f (f z' b) a"
  shows "foldl f z (MList.insert k v m) = foldl f (f z (k, v)) m"

using assms(1) assms(2) proof (induction m  arbitrary: z  )
  case Nil
  then show ?case
    by simp
next
  case (Cons head rest)
  moreover obtain hK hV where "head = (hK, hV)"
    by (meson Product_Type.prod.exhaust_sel)
  moreover have "hK \<noteq> k"
    using calculation  by force
  ultimately show ?case
    using assms(3) by auto
qed

section "MList with filter"

lemma filterOnInsertNotP :
  assumes "valid_map m"
      and "\<forall> v. \<not> P (k, v)"
  shows "filter P (insert k v m) = filter P m"
using assms proof (induction m)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  then obtain hK hV where "head = (hK, hV)"
    by (meson surj_pair)
  then show ?case
    using local.Cons.IH local.Cons.prems(1) local.Cons.prems(2) by auto
qed

lemma filterOnInsertP :
  assumes "valid_map m"
      and "\<forall> v. P (k, v)"
    shows "filter P (insert k v m) = insert k v (filter P m)"
using assms proof (induction m)
  case Nil
  then show ?case by simp
next
  case (Cons head rest)
  then obtain hK hV where pHead: "head = (hK, hV)"
    by (meson surj_pair)
  then show ?case
  proof (cases rule: linorder_cases [of k hK])
    case less
    have "(k, v) # filter P rest = insert k v (filter P rest)"
      by (smt (verit) filter.simps(2) insert.elims assms(2) less local.Cons.IH local.Cons.prems(1) order_less_trans pHead remove_from_middle sublist_valid)
    then show ?thesis
      by (simp add: assms(2) less pHead)
  next
    case equal
    with Cons pHead show ?thesis by simp
  next
    case greater
    with Cons pHead show ?thesis by auto
   qed
 qed

lemma lookupAsFilter :
  assumes "valid_map m" and "lookup k m = Some v"
  shows "filter (\<lambda>(eK, _). eK = k) m = [(k, v)]"
        (is "?f m = _")
  using assms proof (induction m rule: MList_induct)
  case empty
  then show ?case
    by simp
next
  case (update uK uV m)
  then show ?case
  proof (cases "uK = k")
    assume "uK = k"
    moreover have "uV = v"
      by (metis calculation Option.option.sel insert_lookup_Some local.update.prems)
    moreover have "lookup k m = None"
      using calculation local.update.hyps(2) by auto
    moreover have "?f m = []"
      by (smt (verit, del_insts) calculation(3) case_prodE filter_False lookupAsMap map_of_eq_Some_iff option.simps(3) update.hyps(1) valid_map.elims(2))
    moreover have "?f (insert uK uV m) = [(uK, uV)]"
      using calculation filterOnInsertP local.update.hyps(1) by fastforce
    ultimately show ?thesis
      by force
  next
    assume "uK \<noteq> k"
    moreover have "?f (insert uK uV m) = ?f m"
      using calculation filterOnInsertNotP local.update.hyps(1) by fastforce
    ultimately show ?thesis
      by (metis insert_lookup_different local.update.IH local.update.prems)
  qed
qed

end
