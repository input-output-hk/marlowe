theory SList
imports Main HOL.List
begin

datatype (set: 'a) slist = SList "'a list"

definition empty :: "'a slist" where
"empty = SList Nil"

fun null :: "'a slist \<Rightarrow> bool" where
"null (SList Nil) = True" |
"null (SList (Cons _ _)) = False"

fun member :: "'a \<Rightarrow> 'a slist \<Rightarrow> bool" where
"member key (SList Nil) = False" |
"member key (SList (Cons k t)) =
   (if key = k then True else member key (SList t))"

fun insert :: "'a \<Rightarrow> 'a slist \<Rightarrow> 'a slist" where
"insert key (SList l) = (if member key (SList l) then (SList l) else (SList (key#l)))"

fun remove_aux :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove_aux _ Nil = Nil" |
"remove_aux key (Cons k t) =
  (if key = k then remove_aux key t else (Cons k (remove_aux key t)))"

fun remove :: "'a \<Rightarrow> 'a slist \<Rightarrow> 'a slist" where
"remove k (SList x) = SList (remove_aux k x)"

fun size :: "'a slist \<Rightarrow> nat" where
"size (SList Nil) = 0" |
"size (SList (Cons k t)) =
  (if (member k (SList t)) then size (SList t) else 1 + (size (SList t)))"

fun fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a slist \<Rightarrow> 'b \<Rightarrow> 'b" where
"fold f (SList l) a = List.fold f l a"

lemma fold_invariant_aux : "P (List.fold f x y) \<Longrightarrow> (\<And>a b. P b \<Longrightarrow> P (f a b)) \<Longrightarrow> P y \<Longrightarrow> P (List.fold f x (f a y))"
  by (simp add: fold_invariant)

lemma fold_invariant : "(\<And> a b. P b \<Longrightarrow> P (f a b)) \<Longrightarrow> (P y \<Longrightarrow> P (List.fold f x y))"
  apply (induction x)
  apply (simp)
  by (simp add:fold_invariant_aux)

lemma slist_fold_invariant : "(\<And> a b. P b \<Longrightarrow> P (f a b)) \<Longrightarrow> (P y \<Longrightarrow> P (SList.fold f x y))"
  apply (induction x)
  by (simp add: SList.fold_invariant)

fun toList :: "'a slist \<Rightarrow> 'a list" where
"toList (SList x) = x"

end