theory StaticAnalysis
  imports Semantics MList "HOL-Library.Monad_Syntax"
begin

(* Symbolic mock definition *)

record SymbolicMonadData = numSymbolicVars :: nat
                           symbolicVarValues :: "int list"

datatype 'a Symbolic = Symbolic "SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option"

fun execute :: "'a Symbolic \<Rightarrow> SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option" where
"execute (Symbolic f) = f"

fun bind :: "'a Symbolic \<Rightarrow> ('a \<Rightarrow> 'b Symbolic) \<Rightarrow> 'b Symbolic" where
  "bind m nf =
      Symbolic (\<lambda> il. (case execute m il of
                     Some (r1, s1) \<Rightarrow> execute (nf r1) s1
                   | None \<Rightarrow> None))"

adhoc_overloading
  Monad_Syntax.bind StaticAnalysis.bind

fun maybeNth :: "'a list => nat => 'a option" (infixl "!?" 100) where
"(x # xs) !? n = (case n of 0 \<Rightarrow> Some x | Suc k \<Rightarrow> xs !? k)" |
"Nil !? n = None"

definition newVar :: "int Symbolic" where
  "newVar = Symbolic (\<lambda> st . let nsv = numSymbolicVars st in
                   case (symbolicVarValues st) !? nsv of
                     Some x \<Rightarrow> Some (x, st \<lparr> numSymbolicVars := Suc nsv \<rparr> ) )"

fun constrain :: "bool \<Rightarrow> unit Symbolic" where
  "constrain val = Symbolic (\<lambda> st . if val then Some ((), st) else None)"

fun return :: "'a \<Rightarrow> 'a Symbolic" where
  "return x = Symbolic (\<lambda> st . Some (x, st))"

lemma symbolicConstrain : "(\<exists> x. execute (do { a \<leftarrow> newVar;
                                               b \<leftarrow> newVar;
                                               constrain (c a b);
                                               return () }) x \<noteq> None) = \<exists> a b. c a b"
  apply (rule iffI)
  apply simp
  apply (smt case_prod_beta' execute.simps option.case_eq_if option.distinct(1))
  apply (auto simp del:bind.simps not_None_eq)
  subgoal for a b
    apply(rule exI[of _ "\<lparr> numSymbolicVars = 0
                         , symbolicVarValues = (Cons a (Cons b Nil)) \<rparr>"])
    by (simp add:newVar_def)
  done


(* Symbolic semantics definition *)

datatype SymInput = SymDeposit AccountId Party "int"
                  | SymChoice ChoiceId "int"
                  | SymNotify

record SymStateRecord = lowSlot :: "int"
                        highSlot :: "int"
                        trace :: "(int  \<times> int \<times> int option \<times> int) list"
                        paramTrace :: "(int \<times> int \<times> int \<times> int) list"
                        symInput :: "SymInput option"
                        whenPos :: int
                        symAccounts :: "((AccountId \<times> Token) \<times> int) list"
                        symChoices :: "(ChoiceId \<times> int) list"
                        symBoundValues :: "(ValueId \<times> int) list"

datatype SymState = SymState SymStateRecord

function (sequential) generateSymbolicInterval :: "int option \<Rightarrow> (int \<times> int) Symbolic" where
"generateSymbolicInterval None =
  do { hs \<leftarrow> newVar;
       ls \<leftarrow> newVar;
       constrain (ls < hs);
       return (ls, hs) }" |
"generateSymbolicInterval (Some ms) =
  do { (ls, hs) \<leftarrow> generateSymbolicInterval None;
       constrain (ls \<ge> ms);
       return (ls, hs) }"
  by auto
termination generateSymbolicInterval
  apply (relation "measure (\<lambda>s . if s = None then 0 else 1)")
  by simp_all

fun mkInitialSymState :: "(int \<times> int \<times> int \<times> int) list \<Rightarrow> State option \<Rightarrow> SymState Symbolic" where
"mkInitialSymState pt None = do { (ls, hs) \<leftarrow> generateSymbolicInterval None;
                                  return (SymState \<lparr> lowSlot = ls
                                                   , highSlot = hs
                                                   , trace = Nil
                                                   , paramTrace = pt
                                                   , symInput = None
                                                   , whenPos = 0
                                                   , symAccounts = Nil
                                                   , symChoices = Nil
                                                   , symBoundValues = Nil
                                                   \<rparr>) }" |
"mkInitialSymState pt (Some \<lparr> accounts = accs
                            , choices = cho
                            , boundValues = bVal
                            , minSlot = ms \<rparr>) =
  do { (ls, hs) \<leftarrow> generateSymbolicInterval (Some ms);
       return (SymState \<lparr> lowSlot = ls
                        , highSlot = hs
                        , trace = Nil
                        , paramTrace = pt
                        , symInput = None
                        , whenPos = 0
                        , symAccounts = accs
                        , symChoices = cho
                        , symBoundValues = bVal \<rparr>) }"

end
