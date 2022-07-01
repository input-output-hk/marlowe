(*<*)
theory Specification
  imports Main  "HOL-Library.LaTeXsugar" SemanticsTypes

begin                                                     
(*>*)
(**)


chapter \<open>Marlowe Core\<close>

text \<open>Something something Contract type\<close>
text \<open>@{datatype [display,names_short, margin=40]Contract}\<close>


text "in haskell"
text \<open>@{code_stmts Contract.case_Contract  type_constructor: Contract (Haskell)}\<close>

(*<*)
end
(*>*)