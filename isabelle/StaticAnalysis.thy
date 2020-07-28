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
                                               return () }) x \<noteq> None) = (\<exists> a b. c a b)"
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

datatype SymInput = SymDeposit AccountId Party Token "int"
                  | SymChoice ChoiceId "int"
                  | SymNotify

record SymStateRecord = lowSlot :: "int"
                        highSlot :: "int"
                        traces :: "(int  \<times> int \<times> SymInput option \<times> int) list"
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
                                                   , traces = Nil
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
                        , traces = Nil
                        , paramTrace = pt
                        , symInput = None
                        , whenPos = 0
                        , symAccounts = accs
                        , symChoices = cho
                        , symBoundValues = bVal \<rparr>) }"

fun getSymValFrom :: "SymInput option \<Rightarrow> int" where
"getSymValFrom None = 0" |
"getSymValFrom (Some (SymDeposit _ _ _ val)) = val" |
"getSymValFrom (Some (SymChoice _ val)) = val" |
"getSymValFrom (Some SymNotify) = 0"

fun convertToSymbolicTrace :: "(int \<times> int \<times> SymInput option \<times> int) list \<Rightarrow>
                               (int \<times> int \<times> int \<times> int) list \<Rightarrow> bool " where
"convertToSymbolicTrace Nil Nil = True" |
"convertToSymbolicTrace Nil (Cons (a, b, c, d) t) =
   ((a = -1) \<and> (b = -1) \<and> (c = -1) \<and> (d = -1) \<and> convertToSymbolicTrace Nil t)" |
"convertToSymbolicTrace (Cons (lowS, highS, inp, pos) t) (Cons (a, b, c, d) t2) =
   ((lowS = a) \<and> (highS = b) \<and> (getSymValFrom inp = c) \<and> (pos = d))" |
"convertToSymbolicTrace _ _ = undefined"

fun symEvalVal :: "Value \<Rightarrow> SymState \<Rightarrow> int" and
    symEvalObs :: "Observation \<Rightarrow> SymState \<Rightarrow> bool" where
"symEvalVal (AvailableMoney accId tok) (SymState symState) =
   findWithDefault 0 (accId, tok) (symAccounts symState)" |
"symEvalVal (Constant inte) symState = inte" |
"symEvalVal (NegValue val) symState = - symEvalVal val symState" |
"symEvalVal (AddValue lhs rhs) symState = symEvalVal lhs symState +
                                          symEvalVal rhs symState" |
"symEvalVal (SubValue lhs rhs) symState = symEvalVal lhs symState -
                                          symEvalVal rhs symState" |
"symEvalVal (MulValue lhs rhs) symState = symEvalVal lhs symState *
                                          symEvalVal rhs symState" |
"symEvalVal (Scale n d rhs) symState =
  (let nn = symEvalVal rhs symState * n in
   let (q, r) = nn quotRem d in
   if (abs r * 2 < abs d) then q else (q + signum nn * signum d))" |
"symEvalVal (ChoiceValue choId) (SymState symState) =
  findWithDefault 0 choId (symChoices symState)" |
"symEvalVal SlotIntervalStart (SymState symState) = lowSlot symState" |
"symEvalVal SlotIntervalEnd (SymState symState) = highSlot symState" |
"symEvalVal (UseValue valId) (SymState symState) =
  findWithDefault 0 valId (symBoundValues symState)" |
"symEvalVal (Cond cond v1 v2) symState = (if symEvalObs cond symState
                                          then symEvalVal v1 symState
                                          else symEvalVal v2 symState)"  |
"symEvalObs (AndObs obs1 obs2) symState = (symEvalObs obs1 symState \<and>
                                           symEvalObs obs2 symState)" |
"symEvalObs (OrObs obs1 obs2) symState = (symEvalObs obs1 symState \<or>
                                          symEvalObs obs2 symState)" |
"symEvalObs (NotObs obs) symState = (\<not> symEvalObs obs symState)" |
"symEvalObs (ChoseSomething choiceId) (SymState symState) =
  member choiceId (symChoices symState)" |
"symEvalObs (ValueGE lhs rhs) symState = (symEvalVal lhs symState \<ge>
                                          symEvalVal rhs symState)" |
"symEvalObs (ValueGT lhs rhs) symState = (symEvalVal lhs symState >
                                          symEvalVal rhs symState)" |
"symEvalObs (ValueLT lhs rhs) symState = (symEvalVal lhs symState <
                                          symEvalVal rhs symState)" |
"symEvalObs (ValueLE lhs rhs) symState = (symEvalVal lhs symState \<le>
                                          symEvalVal rhs symState)" |
"symEvalObs (ValueEQ lhs rhs) symState = (symEvalVal lhs symState =
                                          symEvalVal rhs symState)" |
"symEvalObs TrueObs _ = True" |
"symEvalObs FalseObs _ = False"

fun updateSymInput :: "SymInput option \<Rightarrow> SymState \<Rightarrow> SymState Symbolic" where
"updateSymInput None symState = return symState" |
"updateSymInput (Some (SymDeposit accId _ tok val)) (SymState symState) =
  (let resultVal = findWithDefault 0 (accId, tok) (symAccounts symState)
                    + max 0 val in
   return (SymState (symState \<lparr> symAccounts :=
                                   MList.insert (accId, tok) resultVal
                                                (symAccounts symState) \<rparr>)))" |
"updateSymInput (Some (SymChoice choId val)) (SymState symState) =
  return (SymState (symState \<lparr> symChoices := MList.insert choId val (symChoices symState) \<rparr>))" |
"updateSymInput (Some SymNotify) symState =
  return symState"

fun addTransaction :: "int \<Rightarrow> int \<Rightarrow> SymInput option \<Rightarrow> int \<Rightarrow> SymState \<Rightarrow> int \<Rightarrow>
                       (bool \<times> SymState) Symbolic" where
"addTransaction newLowSlot newHighSlot None slotTim
                (SymState symState) pos =
 (let oldLowSlot = lowSlot symState in
  let oldHighSlot = highSlot symState in
  let oldTraces = traces symState in
  let prevSymInp = symInput symState in
  let oldPos = whenPos symState in
  do { let tim = slotTim;
       constrain (newLowSlot < newHighSlot);
       let conditions = (((oldHighSlot < tim) \<or>
                          ((oldLowSlot = newLowSlot) \<and> (oldHighSlot = newHighSlot))) \<and>
                         (newLowSlot \<ge> tim));
       uSymInput \<leftarrow> updateSymInput None
                      (SymState
                         (symState \<lparr> lowSlot := newLowSlot
                                   , highSlot := newHighSlot
                                   , traces := (Cons (oldLowSlot, oldHighSlot, prevSymInp, oldPos)
                                                     oldTraces)
                                   , symInput := None
                                   , whenPos := pos
                                   \<rparr>));
       return (conditions, uSymInput) })" |
"addTransaction newLowSlot newHighSlot newSymInput slotTim (SymState symState) pos =
  (let oldLowSlot = lowSlot symState in
   let oldHighSlot = highSlot symState in
   let oldTraces = traces symState in
   let prevSymInp = symInput symState in
   let oldPos = whenPos symState in
   do { let tim = slotTim;
        constrain (newLowSlot \<le> newHighSlot);
        let conditions = ((oldHighSlot < tim) \<and>
                          (newHighSlot < tim) \<and>
                          (newLowSlot \<ge> oldLowSlot));
        uSymInput \<leftarrow> updateSymInput newSymInput
                      (SymState
                         (symState \<lparr> lowSlot := newLowSlot
                                   , highSlot := newHighSlot
                                   , traces := (Cons (oldLowSlot, oldHighSlot, prevSymInp, oldPos)
                                                     oldTraces)
                                   , symInput := newSymInput
                                   , whenPos := pos
                                   \<rparr>));
        return (conditions, uSymInput) })"

end
