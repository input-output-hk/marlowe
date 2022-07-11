(*<*)
theory Specification
  imports Main  "HOL-Library.LaTeXsugar" Core.SemanticsTypes

begin                                                     
(*>*)

chapter \<open>Marlowe Core\<close>

text \<open>Contract type\<close>
text \<open>@{datatype [display,names_short, margin=40]Contract}\<close>

text \<open>Value\<close>
text \<open>@{datatype [display,names_short, margin=40]Value}\<close>

text \<open>Input\<close>
text \<open>@{datatype [display,names_short, margin=40]Input}\<close>

text \<open>State\<close>

(* Sadly there is no antiquote to print a record, and I wasn't able to 
make the snipet import work (described in chapter 7 of the Sugar Latex PDF).
So to show records we need to duplicate the definition
 *)
record State = accounts :: Accounts
               choices :: "(ChoiceId \<times> ChosenNum) list"
               boundValues :: "(ValueId \<times> int) list"
               minSlot :: Slot

(*<*)
end
(*>*)