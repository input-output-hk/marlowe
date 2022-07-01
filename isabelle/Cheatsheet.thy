(*<*)
theory Cheatsheet
  imports Main  "HOL-Library.LaTeXsugar" 
(* "HOL-Library.OptionalSugar" *)
begin                                                     
(*>*)
(**)


chapter \<open>Isabelle documentation cheatsheet \label{sec:cheatsheet}\<close>

text \<open>
Isabelle allows you to mix computer verified proofs with human readable text. It has quite extensive
capabilities to modify the exported documentation, and this Theory/Module can be used as a 
cheatsheet to guide a developer write maintanable documentation. It is recommended to read this
both in the JEdit editor and in the generated pdf to understand how different commands affects 
the output.
\<close>

section \<open>Text basics\<close>

subsection "Text, comments and commands"

text "This is normal text between quotes."

text 
"
Each text command creates a paragraph.
And it can be multiline.

An empty line does not create a new paragraph, it just creates a newline.
"

\<comment> \<open>This is a comment, it doesn't appear in the final document\<close>

(* This is another way to express a comment *)

text
"
Text blocks are commands to Isabelle, just like defining a datatype 
"

datatype 'a tree
  = Tip 
  | Node "'a tree" 'a "'a tree" 

text 
"
By default all commands appear in the generated documentation, unless you enclose them 
between (*<*) a particular comment block(*>*).
"

(*<*)
datatype 'a perhaps
  = Nope
  | Yeap 'a
  
(*>*)



subsection "Unicode characters"

text 
\<open>
Isabelle uses a lot of Unicode characters, for example the one used to define this "text block" is
called a cartouche, and it is used in several places to delimit a string.
\<close>

text 
\<open>
Inside the JEdit editor you can use the "Symbols" panel to insert a character, or you can use the 
autocomplete feature. To insert a cartouche start by typing a double quote ", and when the modal
appears, select cartouche template. Most unicode characters can be fuzzy searched starting with a 
backslash and with the name of the character. Searching for @{verbatim \<open>\forall\<close>} will yield the 
"\forall" character. If you are reading this from JEdit, you will note that the actual unicode 
character is not display here, in order to see it, it needs to be inside a proposition or an 
antiquote that expects it (E.g: @{prop "\<forall> x. x"}).
\<close>

subsection "Antiquotations"

text 
\<open>
Antiquotations  are a way to export constructs to the document. The basic syntax is to write the 
at symbol (@)  followed by the antiquotation body inside curly braces (\{\}). 
\<close>

text 
\<open>
For example we can use the verbatim antiquote to escape text that would otherwise be interpreted
by Isabelle: @{verbatim \<open>@verbatim{"The outer verbatim escapes the inner one. So meta"}\<close>}
\<close>

text 
\<open>
The basic syntax for an antiquote is @{verbatim \<open>@{ antiquotation_body }\<close>}.
The full syntax and a list of commands is available in chapter 4.2 
of the isar\_ref pdf available at this link 
@{url "https://isabelle.in.tum.de/doc/isar-ref.pdf#page=84"}. Note the use of the 
@{verbatim "@{url}"} antiquote.
\<close>

text
\<open>
Not all antiquotes are listed in the chapter 4.2, for example the @{verbatim "datatype"} and 
@{verbatim "code_stmts"} antiquotes are missing. To see a list of all the antiquotes available in a
context and the options you can click on the following command and inspect the output pane: 
\<close>

print_antiquotations

text 
\<open>
You can read the \<^emph>\<open>ML\<close> code to see what arguments can be passed by entering the definition
with @{verbatim "CMD+click"} on the antiquote.
\<close>

text
\<open>
Sidenote:
\<^item> To avoid adding a url in the body of the text, you can use a footnote using the
@{verbatim \<open>\footnote\<close>} unicode char \<^footnote>\<open>Url by antiquote: @{url "www.google.com"}\<close>.
\<^item> Instead of the @{verbatim "@{url}"} antiquote, you can also use the unicode char @{verbatim \<open>\url\<close>}
 \<^footnote>\<open>Url by unicode char: \<^url>\<open>http://www.google.com\<close> \<close>.
\<^item> Instead of the @{verbatim "@{verbatim}"} antiquote you can use the \<^verbatim>\<open>\verbatim\<close> char.
\<close>
  
subsection \<open>Formatting text\<close>

text 

\<open>
You can use the @{verbatim \<open>\emph\<close>} char to \<^emph>\<open>emphasize text\<close>, or the 
@{verbatim \<open>\bold\<close>} to \<^bold>\<open>bold it\<close>.
 
\begin{center}
You can also write centered text.
\end{center}

Use the @{verbatim \<open>\item\<close>} char 
\<^item> to
\<^item> create 
\<^item> bullets

\<close>
text
\<open>
Or the @{verbatim \<open>\enum\<close>} char 
\<^enum> to
\<^enum> create
\<^enum> numbered bullets

\<close>

subsection \<open>References\<close>

text 
\<open>
Inside \<^emph>\<open>root.tex\<close> there is a command definition for \<^verbatim>\<open>\secref{}\<close>, which allow us to reference 
sections labeled using \<^verbatim>\<open>\label{}\<close> (E.g: \secref{sec:cheatsheet}).
\<close>

section \<open>Definitions \label{sec:definitions}\<close> 
subsection \<open>Terms, types and values\<close>

text \<open>
You can print terms, types and values.  Note that in some cases we need to specify the type 
of a number using \<^verbatim>\<open>::\<close> as addition is polymorphic.

\<^item> Term: @{term "2 + 2"}
\<^item> Type of a polymorphic term: @{typeof "2 + 2"}
\<^item> Type of a concrete term: @{typeof "2 + 2 :: nat"}
\<^item> The evaluation of a term @{value "2 + 2 :: nat"}
\<^item> The evaluation of a term with its type @{value [show_types] "2 + 2 :: nat"}
\<close>

subsection \<open>Data types  \label{sec:definitions-datatypes}\<close>


text \<open>To print a datatype we can use the @{verbatim "@{datatype <type>}"} antiquote.\<close>

text \<open>@{datatype tree}\<close>

(*
text \<open>
Isabelle will try to print it as a one-liner, but if its too big, you can use the 
 @{verbatim "[display]"} option to span in multiple lines.\<close>

text \<open>@{datatype[display] tree}\<close>

text \<open>
By default, if the name collides Isabelle will use the full specified name. We can 
use @{verbatim "[names_short]"} option to solve that.\<close>

text \<open>@{datatype[display,names_short] tree}\<close>
*)

text  \<open>We can also use the @{verbatim "code_stmts"} antiquote to print a datatype in Haskell\<close>

text \<open>@{code_stmts tree.case_tree type_constructor: tree (Haskell)}\<close>

text \<open>By default @{verbatim "code_stmts"} will print all the code needed to export the constants. We
can control what gets printed with the
 @{verbatim "type_constructor, constant, type_class and class_instance"} modifiers.\<close>


subsection \<open>Functions \label{sec:definitions-functions}\<close>

text \<open>The following is the syntax for defining a function:\<close>

fun isNope :: "'a perhaps \<Rightarrow> bool" where 
  "isNope Nope = True" |
  "isNope (Yeap _) = False"

fun isYeap :: "'a perhaps \<Rightarrow> bool" where 
  isYeap_Nope: "isYeap Nope = False" |
  isYeap_Yeap: "isYeap (Yeap _) = True"

text \<open>Note that the second
definition gives a label to each pattern match. This enable us to reference a case using the 
\<^verbatim>\<open>@{thm isYeap_Nope}\<close> and \<^verbatim>\<open>@{thm isYeap_Yeap}\<close> antiquotes. 
\<close>

text \<open>
\begin{center}
@{thm isYeap_Nope} \\
@{thm isYeap_Yeap }
\end{center}
\<close>

text 
\<open>
If the function cases doesn't have a label we can still reference them using the 
\<^verbatim>\<open>@{thm isNope.simps(n)}\<close> constant.
Whenever we define a datatype, function or theorem, different constants are created. Use the \<^emph>\<open>Query\<close>
panel to inspect them.
\<close>


text
\<open>
\begin{center}
@{thm isNope.simps(1)} \\
@{thm isNope.simps(2)} 
\end{center}
\<close>

text 
\<open>
Using the \<^verbatim>\<open>[display]\<close> option we can print all terms at once (with a slightly smaller font, and for 
some reason the center does not work).
 \<^verbatim>\<open>@{thm [display]isNope.simps}\<close>
\<close>

text 
\<open>
\begin{center}
@{thm [display]isNope.simps} 
\end{center}
\<close>

text \<open>
We can print the type of a function using the \<^verbatim>\<open>@{typeof ...}\<close> antiquote, or a term with it's 
type using \<^verbatim>\<open>@{term_type ...}\<close>.

\<^item> Tyepof a function isNope :: @{typeof isNope}
\<^item> Term and its type: @{term_type isNope}
\<close>

text \<open> 
In the section \<^emph>\<open>Latex Sugar\<close> \secref{sec:latex-sugar} there are links to a pdf that shows how to 
align equations.
\<close>

text 
\<open>
\begin{center}
\begin{tabular}{l@ {~~@{text "="}~~}l}
@{thm (lhs) isYeap_Nope} & @{thm (rhs) isYeap_Nope}\\
@{thm (lhs) isYeap_Yeap} & @{thm (rhs) isYeap_Yeap}
\end{tabular}
\end{center}
\<close>


text \<open>And how to rename \<^verbatim>\<open>DUMMY\<close> variables\<close>

text 
\<open>
\begin{center}
\begin{tabular}{l@ {~~@{text "="}~~}l}
@{thm (lhs) isYeap_Nope} & @{thm (rhs) isYeap_Nope}\\
@{thm (dummy_pats,lhs) isYeap_Yeap} & @{thm (rhs) isYeap_Yeap}
\end{tabular}
\end{center}

\<close>


text 
\<open>
Similar to the Datatype definition \secref{sec:definitions-datatypes}, we can use the \<^verbatim>\<open>@code_stmts{...}\<close> 
antiquote to print the Haskell version of a function.
\<close>

text \<open>@{code_stmts isNope constant: isNope (Haskell)}\<close>


section \<open>Proofs\<close>

text
\<open>
For a proposition that has been already proven, and that is available in the current context, we 
can use the \<^verbatim>\<open>@{thm map_append}\<close> antiquote to print it.
\<close>

text \<open>@{thm map_append}\<close>

text 
\<open>
When we need to prove a proposition, Isabelle provide us two different ways: an imperative and a 
declarative way. When the proof is trivial, it is recommended to use the imperative way
\<close>

(*<*)
fun listsum :: "nat list \<Rightarrow> nat" where 
  "listsum [] = 0" |
  "listsum (x#xs) = x + listsum xs" 

(*>*)

lemma listsum_app: "listsum (xs @ ys) = listsum xs + listsum ys"  
  apply (induction xs)
  apply (simp_all)
  done

text "or even shorter" 

lemma listsum_app2: "listsum (xs @ ys) = listsum xs + listsum ys" 
  by (induction xs) simp_all

text 
\<open>
When the theorem is more complex, the authors of Isabelle recommend to write them as structured proofs
with Isar \<^footnote>\<open>\<^url>\<open>http://concrete-semantics.org/concrete-semantics.pdf#page=63\<close>\<close>. Those type of test
are easier to read and to maintain. 
\<close>

text "For example, given the definition for a reverse function that can be optimized with TCO" 

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "itrev [] ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"

text \<open>We would like to prove that @{prop "itrev xs ys =  rev xs @ ys" }. The lemma is easy
enough to write it in an imperative way\<close>

lemma itrev_app: "itrev xs ys =  rev xs @ ys"
  by (induction xs arbitrary: ys) simp_all


text "But we can use this as an example to showcase Isar. If you write the \<^verbatim>\<open>proof\<close> command and give
a method like induction, Isabelle will suggest you the pattern match to divide the proof by its case.
In the simplest example we could write the proof like this:" 

lemma itrev_app2: "itrev xs ys =  rev xs @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case by simp
qed

text "The \<^verbatim>\<open>?case\<close> keyword is the current goal for each case. We can also use other constructs
to refine the goal and to make the proof more explicit"

lemma itrev_app3: "itrev xs ys =  rev xs @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  hence "itrev [] ys = ys" by simp
  hence "...  = [] @ ys" by (simp only: append_Nil)
  hence "...  = rev [] @ ys"  by (simp only: rev.simps) 
  thus "itrev [] ys = rev [] @ ys" by simp
next
  case (Cons x xs)  
  hence 0: "itrev (x # xs) ys = itrev xs (x # ys) " by (simp only: itrev.simps)
  hence 1: "... = rev xs @ (x # ys)" using Cons.IH by (simp only:  Cons.IH)
  hence 2: "... = rev xs @ [x] @ ys" by simp 
  hence 3: "... = rev xs @ rev [x] @ ys" by simp
  hence 4: "... = rev ([x] @ xs) @ ys"  by (simp flip: rev_append)
  from 1 4 show "itrev (x # xs) ys = rev (x # xs) @ ys" by simp
qed


text "We can also play with \<^verbatim>\<open>(*<*) ... (*>*)\<close> and antiquotes to focus on the english version of 
the proof."

text_raw \<open>\fbox{\parbox{\textwidth}{\<close> 
(*<*)
lemma itrev_app4 [simp]: "itrev xs ys =  rev xs @ ys"
(*>*)
  text \<open>
  \<^bold>\<open>Lemma\<close> @{term ?thesis}. \\ \\
  We can use induction on @{verbatim "xs"} for an arbitrary @{verbatim "ys"}
\<close>

(*<*)
proof (induction xs arbitrary: ys)
  case Nil
(*>*)
  text_raw 
  \<open>\begin{enumerate}
  \item For the Base case: \\
  \begin{tabular}{l@ {~~@{text "="}~~}l l}
  \<close>
  (*<*)hence "itrev [] ys = ys" by simp(*>*)
  text_raw \<open>@{thm (lhs) this} & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of \<^verbatim>\<open>itrev\<close>\\\<close>

  (*<*)hence "...  = [] @ ys" by (simp only: append_Nil) (*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of \<^verbatim>\<open>append\<close>\\\<close>    

  (*<*)hence "...  = rev [] @ ys" by (simp only: rev.simps) (*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of \<^verbatim>\<open>rev\<close>\\\<close>

  text_raw
  \<open>\end{tabular} \\\<close>
  (*<*)thus "itrev [] ys = rev [] @ ys" by simp (*>*)

(*<*)
next
  case (Cons x xs)
(*>*)
  text_raw 
  \<open>\item For the Inductive case: \\ 
   We assume the \<^emph>\<open>I.H.\<close> as: \forall ys. @{thm Cons.IH}, then \\ 
   \begin{tabular}{l@ {~~@{text "="}~~}l l}
  \<close>
  
  (*<*)hence 0: "itrev (x # xs) ys = itrev xs (x # ys) " by (simp only: itrev.simps)(*>*)
  text_raw \<open>@{thm (lhs) this} & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of \<^verbatim>\<open>itrev\<close>\\\<close>

  (*<*)hence 1: "... = rev xs @ (x # ys)" using Cons.IH by (simp only: Cons.IH)(*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the induction hypotesis \\\<close>

  (*<*)hence 2: "... = rev xs @ [x] @ ys" by simp (*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of \<^verbatim>\<open>append\<close>\\\<close>    

  (*<*)hence 3: "... = rev xs @ rev [x] @ ys" by simp (*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the singleton\_rev lemma \\\<close>

  (*<*)hence 4: "... = rev ([x] @ xs) @ ys"  by (simp flip: rev_append)(*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the rev\_append lemma \\\<close>

  (*<*)from 1 4 show "itrev (x # xs) ys = rev (x # xs) @ ys" by simp(*>*)
  text_raw \<open> & @{thm (rhs) this} & \<^bold>\<open>by\<close> the definition of append \\\<close>
  
  text_raw \<open>
  \end{tabular}
  \end{enumerate}
  }}
  \<close>
(*<*)qed(*>*)


subsection "Parenthesis problem" 

text \<open>Isabelle has some translation rule that gets rid of "unnecesary parenthesis". 
This makes some theorems a little bit awkward \<^verbatim>\<open>@{thm append_assoc}\<close>:\<close>

text \<open>@{thm append_assoc}\<close>

text \<open>
This happens even if we write it manually.  

\<close>
text \<open>\<^prop>\<open>(a @ b) @ c = a @ (b @ c)\<close>\<close>

text "So far I wasn't able to solve this problem"

section \<open>Latex sugar \label{sec:latex-sugar}\<close>
text 
\<open>
The Latex sugar pdf \<^footnote>\<open>Latex sugar: \<^url>\<open>https://isabelle.in.tum.de/doc/sugar.pdf\<close> \<close> explains some 
advanced commands, like printing Inference Rules.

\begin{center}
  @{thm[mode=Rule] conjI} {\sc conjI}
\end{center}

For this to work, @{verbatim \<open>"HOL-Library.LaTeXsugar"\<close>} needs to be imported and the 
@{verbatim \<open>\usepackage{mathpartir}\<close>} used in \<^emph>\<open>root.tex\<close>
\<close>

text
\<open>In the \<^verbatim>\<open>"HOL-Library.OptionalSugar\<close> package there are some translation rules that we can copy,
paste and modify into a "formmating" package to modify the notation of some constructs. For example,
with the following code, list notation looks more closely to Haskell notation\<close>


notation (latex)
  Cons  ("_ :/ _" [66,65] 65)

syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^latex>\<open>++\<close>" 65)

translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"

text 
\<open>
@{thm [display]rev.simps}
\<close>


(*<*)
end
(*>*)
