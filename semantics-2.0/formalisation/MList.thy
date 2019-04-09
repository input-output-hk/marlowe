theory MList
imports Main
begin

datatype (set: 'a, 'b) mlist = MList "('a \<times> 'b) list"

definition empty :: "('a, 'b) mlist" where
"empty = MList Nil"

fun member :: "'a \<Rightarrow> ('a, 'b) mlist \<Rightarrow> bool" where
"member key (MList Nil) = False" |
"member key (MList (Cons (k, v) t)) =
   (if key = k then True else member key (MList t))"

fun lookup :: "'a \<Rightarrow> ('a, 'b) mlist \<Rightarrow> 'b option" where
"lookup key (MList Nil) = None" |
"lookup key (MList (Cons (k, v) t)) =
   (if key = k then Some v else lookup key (MList t))"

lemma successLookupImpliesMember : "lookup e (MList a) = Some x \<Longrightarrow> member e (MList a)"
  apply (induction a)
  by auto

lemma failedLookupImpliesNotMember : "lookup e (MList a) = None \<Longrightarrow> \<not> member e (MList a)"
  apply (induction a)
  apply auto[1]
  by (metis MList.member.simps(2) lookup.simps(2) option.distinct(1) prod.collapse)

fun lookup_default :: "'b \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mlist \<Rightarrow> 'b" where
"lookup_default def key (MList Nil) = def" |
"lookup_default def key (MList (Cons (k, v) t)) =
   (if key = k then v else lookup_default def key (MList t))"

lemma lookup_and_default_None_aux : "lookup x (MList l) = None \<Longrightarrow> lookup_default d x (MList l) = d"
  apply (induction l)
  by auto

lemma lookup_and_default_None : "lookup x l = None \<Longrightarrow> lookup_default d x l = d"
  apply (cases l)
  by (simp add: lookup_and_default_None_aux)

lemma lookup_and_default_Some_aux : "lookup x (MList l) = Some y \<Longrightarrow> lookup_default d x (MList l) = y"
  apply (induction l)
  by auto

lemma lookup_and_default_Some : "lookup x l = Some y \<Longrightarrow> lookup_default d x l = y"
  apply (cases l)
  by (simp add: lookup_and_default_Some_aux)

fun delete_aux :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
"delete_aux _ Nil = Nil" |
"delete_aux key (Cons (k, v) t) =
  (if key = k then delete_aux key t else (Cons (k, v) (delete_aux key t)))"

lemma delete_aux_step : "(delete_aux a ((a, b) # xa)) = (delete_aux a xa)"
  by simp

lemma not_member_of_delete_aux : "\<not> member x (MList (delete_aux x xb))"
  apply (induction xb)
  apply simp
  by (metis MList.member.simps(2) delete_aux.simps(2) prod.collapse)

fun update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mlist \<Rightarrow> ('a, 'b) mlist" where
"update key val (MList mlist) = MList ((key, val)#(delete_aux key mlist))"

lemma double_update_aux : "update label1 y (update label1 x (MList xa)) = update label1 y (MList xa)"
  apply (induction xa)
  by auto

lemma double_update : "update label1 y (update label1 x z) = update label1 y z"
  by (metis double_update_aux update.elims)

lemma lookup_default_after_update : "MList.lookup_default n x (MList.update x y l) = y"
  apply (cases l)
  by simp

lemma lookup_default_after_update2_aux : "x \<noteq> z \<Longrightarrow> MList.lookup_default n x (MList.update z y (MList l)) =
                                                MList.lookup_default n x (MList l)"
  apply (induction l)
  by auto

lemma lookup_default_after_update2 : "x \<noteq> z \<Longrightarrow> MList.lookup_default n x (MList.update z y l) =
                                                MList.lookup_default n x l"
  apply (cases l)
  by (meson lookup_default_after_update2_aux)

lemma lookup_after_update : "MList.lookup x (update x z e) = MList.lookup x (update x z g)"
  by (metis lookup.simps(2) update.elims)

lemma lookup_after_update2_aux : "x \<noteq> y \<Longrightarrow> lookup x (update y z (MList xa)) = lookup x (MList xa)"
  apply (induction xa)
  by auto

lemma lookup_after_update2 : "x \<noteq> y \<Longrightarrow> MList.lookup x (update y z e) = MList.lookup x e"
  by (metis lookup_after_update2_aux mlist.exhaust)  

lemma lookup_after_update3_aux : "lookup x (update x y (MList xa)) = Some y"
  by simp

lemma lookup_after_update3 : "MList.lookup x (update x y z) = Some y"
  apply (cases z)
  by simp

lemma lookup_after_update4_aux : "lookup x (update x y (MList xa)) = Some y"
  by simp

lemma update_comm_aux : "label1 \<noteq> label2 \<Longrightarrow> lookup a (update label2 x (update label1 y (MList xa))) = lookup a (update label1 y (update label2 x (MList xa)))"
  apply (induction xa arbitrary: label1 label2 x y a)
  apply simp
  by (metis lookup_after_update lookup_after_update2)

lemma update_comm : "label1 \<noteq> label2 \<Longrightarrow> lookup a (update label2 x (update label1 y z)) = lookup a (update label1 y (update label2 x z))"
  by (metis lookup_after_update lookup_after_update2)
  
fun delete :: "'a \<Rightarrow> ('a, 'b) mlist \<Rightarrow> ('a, 'b) mlist" where
"delete k (MList x) = MList (delete_aux k x)"

fun get_min_key_aux :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a" where
"get_min_key_aux a Nil = a" |
"get_min_key_aux a (Cons (k, _) t) =
  (if a \<le> k then get_min_key_aux a t else get_min_key_aux k t)"

fun get_min_key :: "('a::linorder, 'b) mlist \<Rightarrow> 'a option" where
"get_min_key (MList Nil) = None" |
"get_min_key (MList (Cons (k, _) t)) = Some (get_min_key_aux k t)"

fun get_max_key_aux :: "'a::linorder \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a" where
"get_max_key_aux a Nil = a" |
"get_max_key_aux a (Cons (k, _) t) =
  (if a \<ge> k then get_max_key_aux a t else get_max_key_aux k t)"

fun get_max_key :: "('a::linorder, 'b) mlist \<Rightarrow> 'a option" where
"get_max_key (MList Nil) = None" |
"get_max_key (MList (Cons (k, _) t)) = Some (get_max_key_aux k t)"

fun size :: "('a, 'b) mlist \<Rightarrow> nat" where
"size (MList Nil) = 0" |
"size (MList (Cons (k, _) t)) =
  (if (member k (MList t)) then size (MList t) else 1 + (size (MList t)))"

fun map_aux :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'c) list" where
"map_aux f Nil = Nil" |
"map_aux f (Cons (a, b) t) = (Cons (a, f b) (map_aux f t))"

fun map :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mlist \<Rightarrow> ('a, 'c) mlist" where
"map f (MList x) = MList (map_aux f x)"

fun fold_with_key :: "(('a \<times> 'b) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ('a, 'b) mlist \<Rightarrow> 'c" where
"fold_with_key f acc (MList (Nil)) = acc" |
"fold_with_key f acc (MList (Cons h t)) = fold_with_key f (f h acc) (MList t)"

fun delete_until :: "'a \<Rightarrow> ('a, 'b) mlist \<Rightarrow> ('a, 'b) mlist" where
"delete_until dk (MList Nil) = MList Nil" |
"delete_until dk (MList (Cons (k, _) t)) =
  (if dk = k
   then (if (member dk (MList t)) then MList Nil else MList t)
   else delete_until dk (MList t))"

fun reverse_fold_with_key :: "(('a \<times> 'b) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ('a, 'b) mlist \<Rightarrow> 'c" where
"reverse_fold_with_key f acc (MList x) = fold_with_key f acc (MList (rev x))"

lemma reverse_fold_step : "reverse_fold_with_key f x (MList (l @ [a]))
                         = reverse_fold_with_key f (f a x) (MList l)"
  apply (induction l)
  by auto

lemma reverse_fold_split_list : "reverse_fold_with_key f x (MList (h @ l))
                         = (reverse_fold_with_key f (reverse_fold_with_key f x (MList l)) (MList h))"
  apply (induction l arbitrary: x rule:rev_induct)
  by auto

lemma reverse_fold_last_step : "reverse_fold_with_key f x (MList (h # l))
                         = f h (reverse_fold_with_key f x (MList l))"
proof -
  have "\<forall>a p f. f (p::'b \<times> 'c) (a::'a) = reverse_fold_with_key f a (MList [p])"
    by simp
  then show ?thesis
    by (metis append_Cons append_Nil reverse_fold_split_list)
qed

lemma deleteNonExistentPreserves : "lookup e (MList x) = None \<Longrightarrow> (delete e (MList x)) = MList x"
  apply (induction x)
  apply simp
  by auto

lemma nothingComesFromNothing : "MList.lookup y MList.empty = None"
  by (simp add:MList.empty_def)

lemma sizeDeleteNonExistent : "lookup e xa = None \<Longrightarrow> size xa = size (MList.delete e xa)"
  by (metis deleteNonExistentPreserves mlist.exhaust)

lemma sizeRemoveLast : "lookup e (MList xa) = None \<Longrightarrow> size (MList xa) + 1 = size (MList ((e, y) # xa))"
  by (simp add: failedLookupImpliesNotMember)

lemma deleteReductionMatch : "e = x \<Longrightarrow> delete e (MList ((x, a) # xa)) = delete e (MList xa)"
  by auto

lemma unrelatedDelete : "e \<noteq> aa \<Longrightarrow> member aa (MList (delete_aux e xa)) \<Longrightarrow> member aa (MList xa)"
  apply (induction xa)
  apply simp
  by (metis MList.member.simps(2) delete_aux.simps(2) prod.collapse)

lemma unrelatedDelete2 : "e \<noteq> aa \<Longrightarrow> (\<not> member aa (MList (delete_aux e xa)) \<Longrightarrow> \<not> member aa (MList xa))"
  apply (induction xa)
  apply simp
  by (metis delete_aux.simps(2) failedLookupImpliesNotMember lookup.simps(2) not_None_eq old.prod.exhaust successLookupImpliesMember)

lemma sizeDelete_aux2 : "(\<And>x. lookup e (MList xa) = Some x \<Longrightarrow> MList.size (delete e (MList xa)) + 1 = MList.size (MList xa)) \<Longrightarrow>
       lookup e (MList ((aa, b) # xa)) = Some x \<Longrightarrow> MList.size (delete e (MList ((aa, b) # xa))) + 1 = MList.size (MList ((aa, b) # xa))"
  apply (cases "e = aa")
  apply (metis deleteReductionMatch option.exhaust size.simps(2) sizeDeleteNonExistent sizeRemoveLast successLookupImpliesMember)
  apply (cases "lookup aa (MList xa)")
  using failedLookupImpliesNotMember unrelatedDelete apply fastforce
  using unrelatedDelete unrelatedDelete2 by fastforce  

lemma sizeDelete_aux3 : "(\<And>x. lookup e (MList xa) = Some x \<Longrightarrow> MList.size (delete e (MList xa)) + 1 = MList.size (MList xa)) \<Longrightarrow>
       lookup e (MList (a # xa)) = Some x \<Longrightarrow> MList.size (delete e (MList (a # xa))) + 1 = MList.size (MList (a # xa))"
  apply (cases a)
  by (meson sizeDelete_aux2)

lemma sizeDelete_aux4 :  "lookup e (MList xa) = Some x
             \<Longrightarrow> MList.size (delete e (MList xa)) + 1 = MList.size (MList xa)"
  apply (induction xa arbitrary: x y)
  apply auto[1]
  by (meson sizeDelete_aux3)

lemma sizeDelete : "MList.lookup e l = Some x \<Longrightarrow> MList.size (delete e l) + 1 = MList.size l"
  apply (induction l)
  by (meson sizeDelete_aux4)

lemma sizeDeleteOrder : "MList.lookup e l = Some x \<Longrightarrow> MList.size (delete e l) < MList.size l"
  using sizeDelete by fastforce

end