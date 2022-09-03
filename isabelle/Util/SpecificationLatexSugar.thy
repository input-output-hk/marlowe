theory SpecificationLatexSugar 
imports "HOL-Library.LaTeXsugar"
begin 

(* By default all thm exports should use the names_short property. This can be switched on a 
thm by thm basis. *)
declare [[ names_short ]]


(* Display lists more closely to Haskell syntax *)

notation (latex)
  Cons  ("_ :/ _" [66,65] 65)

syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^latex>\<open>++\<close>" 65)

translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"
end 