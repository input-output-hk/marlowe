theory ListTools
imports Main
begin

fun any :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"any f Nil = False" |
"any f (Cons h t) = (f h \<or> any f t)"

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"all f Nil = True" |
"all f (Cons h t) = (f h \<and> all f t)"

end