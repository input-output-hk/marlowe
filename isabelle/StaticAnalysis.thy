theory StaticAnalysis
  imports Semantics MList "HOL-Library.Monad_Syntax" HOL.Wellfounded SingleInputTransactions PositiveAccounts Timeout
begin

(* Symbolic mock definition *)

type_synonym SymbolicMonadData = "int list"

datatype 'a Symbolic = Symbolic "SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option"

primrec execute :: "'a Symbolic \<Rightarrow> SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option" where
  "execute (Symbolic f) = f"

definition bind :: "'a Symbolic \<Rightarrow> ('a \<Rightarrow> 'b Symbolic) \<Rightarrow> 'b Symbolic" where
  "bind m nf =
      Symbolic (\<lambda> il. (case execute m il of
                     Some (r1, s1) \<Rightarrow> execute (nf r1) s1
                   | None \<Rightarrow> None))"

adhoc_overloading
  Monad_Syntax.bind StaticAnalysis.bind

definition newVar :: "int Symbolic" where
  "newVar = Symbolic (\<lambda> st .
                   case st of
                     Cons h t \<Rightarrow> Some (h, t)
                   | Nil \<Rightarrow> None )"

definition constrain :: "bool \<Rightarrow> unit Symbolic" where
  "constrain val = Symbolic (\<lambda> st . if val then Some ((), st) else None)"

definition return :: "'a \<Rightarrow> 'a Symbolic" where
  "return x = Symbolic (\<lambda> st . Some (x, st))"

lemma symbolicConstrain : "(\<exists> x. execute (do { a \<leftarrow> newVar;
                                               b \<leftarrow> newVar;
                                               constrain (c a b);
                                               return () }) x \<noteq> None) = (\<exists> a b. c a b)"
  apply (rule iffI)
  apply (simp add:bind_def add:constrain_def)
  apply (smt case_prod_beta' execute.simps option.case_eq_if option.distinct(1))
  apply (auto simp del:bind.simps not_None_eq)
  subgoal for a b
    apply(rule exI[of _ "(Cons a (Cons b Nil))"])
    by (simp add:newVar_def bind_def constrain_def return_def)
  done


fun isCounterExample :: "(bool \<times> SymbolicMonadData) option \<Rightarrow> bool" where
"isCounterExample None = False" |
"isCounterExample (Some (b, _)) = b"

lemma abstract_newVar : "isCounterExample (execute (newVar \<bind> (\<lambda>v. m v)) (Cons h t)) = isCounterExample (execute (m h) t)"
  by (auto split:option.splits simp add:bind_def newVar_def)

lemma abstract_constrain : "isCounterExample (execute (constrain b \<bind> (\<lambda>_ . m)) x) = (b \<and> isCounterExample (execute m x))"
  by (auto split:option.splits simp add:bind_def constrain_def)

lemma newVar_failsForNil : "isCounterExample (execute (newVar \<bind> (\<lambda>v. m v)) []) = False"
  by (simp add: StaticAnalysis.bind_def newVar_def)

lemma inline_monad : "((m1 \<bind> return \<circ> f) \<bind> m2) = (m1 \<bind> m2 \<circ> f)"
  by (auto split:option.splits simp add:bind_def return_def)

lemma inline_monads_ex1 : "((newVar \<bind> (\<lambda>hs. newVar \<bind> (\<lambda>ls. constrain (ls \<le> hs) \<bind> (\<lambda>_. return (ls, hs))))) \<bind> (\<lambda>(ls, hs). constrain (lSlot \<le> ls) \<bind> (\<lambda>_. return (ls, hs)))) \<bind> f =
                            (newVar \<bind> (\<lambda>hs. newVar \<bind> (\<lambda>ls. constrain (ls \<le> hs) \<bind> (\<lambda>_. constrain (lSlot \<le> ls) \<bind> (\<lambda>_. f (ls, hs))))))"
  by (auto split:option.splits simp add:bind_def return_def execute_def)

lemma bind_left_unit : "do { x \<leftarrow> return a :: int Symbolic; k x } = k a"
  apply (auto split:option.splits simp add:bind_def return_def execute_def)
  by (metis Symbolic.exhaust Symbolic.rec)

lemma bind_right_unit : "do { x \<leftarrow> m :: int Symbolic; return x } = m"
  apply (simp only:bind_def)
  apply (cases m)
  apply simp
  subgoal for x
    apply (subst HOL.fun_eq_iff)
    apply auto
    subgoal for a
      apply (cases "x a")
      by (auto simp add:execute_def return_def)
    done
  done

lemma bind_assoc : "do {y \<leftarrow> do { x \<leftarrow> m :: int Symbolic; k x }; h y} = do { x \<leftarrow> m; do { y \<leftarrow> k x; h y} }"
  by (auto split:option.splits simp add:bind_def return_def execute_def)

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
       constrain (ls \<le> hs);
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

fun convertRestToSymbolicTrace :: "(int \<times> int \<times> SymInput option \<times> int) list \<Rightarrow>
                               (int \<times> int \<times> int \<times> int) list \<Rightarrow> bool" where
"convertRestToSymbolicTrace (Cons (lowS, highS, inp, pos) t) (Cons (a, b, c, d) t2) =
   ((lowS = a) \<and> (highS = b) \<and> (getSymValFrom inp = c) \<and> (pos = d) \<and> (convertRestToSymbolicTrace t t2))" |
"convertRestToSymbolicTrace Nil Nil = True" |
"convertRestToSymbolicTrace _ _ = undefined"

fun isPadding :: "(int \<times> int \<times> int \<times> int) list \<Rightarrow> bool" where
"isPadding Nil = True" |
"isPadding (Cons (a, b, c, d) t) = ((a = -1) \<and> (b = -1) \<and> (c = -1) \<and> (d = -1) \<and> isPadding t)"

fun convertToSymbolicTrace :: "(int \<times> int \<times> SymInput option \<times> int) list \<Rightarrow>
                               (int \<times> int \<times> int \<times> int) list \<Rightarrow> bool" where
"convertToSymbolicTrace refL symL =
   (let lenRefL = length refL;
        lenSymL = length symL in
    (if lenRefL \<le> lenSymL
     then (let lenPadding = lenSymL - lenRefL in
           isPadding (take lenPadding symL) \<and> convertRestToSymbolicTrace refL (drop lenPadding symL))
     else undefined))"

fun convertToSymbolicTrace_old :: "(int \<times> int \<times> SymInput option \<times> int) list \<Rightarrow>
                               (int \<times> int \<times> int \<times> int) list \<Rightarrow> bool" where
"convertToSymbolicTrace_old Nil Nil = True" |
"convertToSymbolicTrace_old Nil (Cons (a, b, c, d) t) =
   ((a = -1) \<and> (b = -1) \<and> (c = -1) \<and> (d = -1) \<and> convertToSymbolicTrace_old Nil t)" |
"convertToSymbolicTrace_old (Cons (lowS, highS, inp, pos) t) (Cons (a, b, c, d) t2) =
   ((lowS = a) \<and> (highS = b) \<and> (getSymValFrom inp = c) \<and> (pos = d) \<and> convertToSymbolicTrace_old t t2)" |
"convertToSymbolicTrace_old _ _ = undefined"

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
       constrain (newLowSlot \<le> newHighSlot);
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

fun const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
"const x _ = x"

fun ensureBounds :: "int \<Rightarrow> Bound list \<Rightarrow> bool" where
"ensureBounds cho Nil = False" |
"ensureBounds cho (Cons (lowBnd, hiBnd) t) =
  (((cho \<ge> lowBnd) \<and> (cho \<le> hiBnd)) \<or> ensureBounds cho t)"

fun addFreshSlotsToState :: "SymState \<Rightarrow> (int \<times> int \<times> SymState) Symbolic" where
"addFreshSlotsToState (SymState sState) =
  do { newLowSlot \<leftarrow> newVar;
       newHighSlot \<leftarrow> newVar;
       return (newLowSlot, newHighSlot, SymState (sState \<lparr> lowSlot := newLowSlot,
                                                           highSlot := newHighSlot \<rparr>))
     }"

fun newPreviousMatchDeposit :: "Value \<Rightarrow> AccountId \<Rightarrow> Party \<Rightarrow> Token \<Rightarrow>
                                (SymInput \<Rightarrow> SymState \<Rightarrow> bool) \<Rightarrow>
                                (SymInput \<Rightarrow> SymState \<Rightarrow> bool)" where
"newPreviousMatchDeposit val accId party token previousMatch otherSymInput pmSymState =
   (let pmConcVal = symEvalVal val pmSymState in
    case otherSymInput of
       SymDeposit otherAccId otherParty otherToken otherConcVal \<Rightarrow>
         if ((otherAccId = accId) \<and> (otherParty = party) \<and> (otherToken = token))
         then (otherConcVal = pmConcVal) \<or> previousMatch otherSymInput pmSymState
         else previousMatch otherSymInput pmSymState
     | _ \<Rightarrow> previousMatch otherSymInput pmSymState)"

fun newPreviousMatchChoice :: "ChoiceId \<Rightarrow> Bound list \<Rightarrow>
                               (SymInput \<Rightarrow> SymState \<Rightarrow> bool) \<Rightarrow>
                               (SymInput \<Rightarrow> SymState \<Rightarrow> bool)" where
"newPreviousMatchChoice choId bnds previousMatch otherSymInput pmSymState =
   (case otherSymInput of
       SymChoice otherChoId otherConcVal \<Rightarrow>
         if otherChoId = choId
         then (ensureBounds otherConcVal bnds \<or> previousMatch otherSymInput pmSymState)
         else previousMatch otherSymInput pmSymState
     | _ \<Rightarrow> previousMatch otherSymInput pmSymState)"

fun newPreviousMatchNotify :: "Observation \<Rightarrow>
                               (SymInput \<Rightarrow> SymState \<Rightarrow> bool) \<Rightarrow>
                               (SymInput \<Rightarrow> SymState \<Rightarrow> bool)" where
"newPreviousMatchNotify obs previousMatch otherSymInput pmSymState =
   (let pmObsRes = symEvalObs obs pmSymState in
    case otherSymInput of
       SymNotify \<Rightarrow> (pmObsRes \<or> previousMatch otherSymInput pmSymState)
     | _ \<Rightarrow> previousMatch otherSymInput pmSymState)"

function (sequential) isValidAndFailsAux :: "bool \<Rightarrow> Contract \<Rightarrow> SymState \<Rightarrow> bool Symbolic" and
     applyInputConditions :: "int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> SymInput option \<Rightarrow> int \<Rightarrow>
                             SymState \<Rightarrow> int \<Rightarrow> Contract \<Rightarrow>
                             (bool \<times> bool) Symbolic" and
    isValidAndFailsWhen :: "bool \<Rightarrow> Case list \<Rightarrow> int \<Rightarrow> Contract \<Rightarrow>
                            (SymInput \<Rightarrow> SymState \<Rightarrow> bool) \<Rightarrow> SymState \<Rightarrow>
                            int \<Rightarrow> bool Symbolic" where
"isValidAndFailsAux hasErr Close (SymState sState) =
  return (hasErr \<and> convertToSymbolicTrace (Cons (lowSlot sState, highSlot sState,
                                                 symInput sState, whenPos sState)
                                                (traces sState)) (paramTrace sState))" |
"isValidAndFailsAux hasErr (Pay accId payee tok val cont) (SymState sState) =
  do { let concVal = symEvalVal val (SymState sState);
       let originalMoney = findWithDefault 0 (accId, tok) (symAccounts sState);
       let remainingMoneyInAccount = originalMoney - max 0 concVal;
       let newAccs = MList.insert (accId, tok) (max 0 remainingMoneyInAccount)
                                  (symAccounts sState);
       let finalSState = SymState (sState \<lparr> symAccounts :=
             (case payee of
                 Account destAccId \<Rightarrow>
                  MList.insert (destAccId, tok)
                               (min originalMoney (max 0 concVal)
                                 + findWithDefault 0 (destAccId, tok) newAccs)
                               newAccs
               | _ \<Rightarrow> newAccs) \<rparr>);
       isValidAndFailsAux ((remainingMoneyInAccount < 0)
                           \<or> (concVal \<le> 0)
                           \<or> hasErr) cont finalSState
     }" |
"isValidAndFailsAux hasErr (If obs cont1 cont2) sState =
  do { let obsVal = symEvalObs obs sState;
       contVal1 \<leftarrow> isValidAndFailsAux hasErr cont1 sState;
       contVal2 \<leftarrow> isValidAndFailsAux hasErr cont2 sState;
       return (if obsVal then contVal1 else contVal2)
     }" |
"isValidAndFailsAux hasErr (When list timeout cont) sState =
  isValidAndFailsWhen hasErr list timeout cont (const (const False)) sState 1" |
"isValidAndFailsAux hasErr (Let valId val cont) (SymState sState) =
  do { let concVal = symEvalVal val (SymState sState);
       let newBVMap = MList.insert valId concVal (symBoundValues sState);
       let newSState = SymState (sState \<lparr> symBoundValues := newBVMap \<rparr>);
       isValidAndFailsAux ((member valId (symBoundValues sState)) \<or> hasErr) cont newSState }" |
"isValidAndFailsAux hasErr (Assert obs cont) sState =
  (let obsVal = symEvalObs obs sState in
   isValidAndFailsAux (hasErr \<or> (\<not> obsVal)) cont sState)" |
"applyInputConditions ls hs hasErr maybeSymInput timeout sState pos cont =
  do { (newCond, newSState) \<leftarrow> addTransaction ls hs maybeSymInput timeout sState pos;
       newTrace \<leftarrow> isValidAndFailsAux hasErr cont newSState;
       return (newCond, newTrace) }" |
"isValidAndFailsWhen hasErr Nil timeout cont previousMatch sState pos =
  do { newLowSlot \<leftarrow> newVar;
       newHighSlot \<leftarrow> newVar;
       (cond, newTrace) \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                                hasErr None timeout sState 0 cont;
       return (if cond then newTrace else False) }" |
"isValidAndFailsWhen hasErr (Cons (Case (Deposit accId party token val) cont) rest)
                     timeout timCont previousMatch sState pos =
  do { (newLowSlot, newHighSlot, sStateWithInput) \<leftarrow> addFreshSlotsToState sState;
       let concVal = symEvalVal val sStateWithInput;
       let symInput = SymDeposit accId party token concVal;
       let clashResult = previousMatch symInput sStateWithInput;
       let newPreviousMatch = newPreviousMatchDeposit val accId party token previousMatch;
       (newCond, newTrace) \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                (hasErr \<or> (concVal \<le> 0))
                                (Some symInput) timeout sState pos cont;
       contTrace \<leftarrow> isValidAndFailsWhen hasErr rest timeout timCont
                                        newPreviousMatch sState (pos + 1);
       return (if (newCond \<and> (\<not> clashResult)) then newTrace else contTrace) }" |
"isValidAndFailsWhen hasErr (Cons (Case (Choice choId bnds) cont) rest)
                     timeout timCont previousMatch sState pos =
  do { (newLowSlot, newHighSlot, sStateWithInput) \<leftarrow> addFreshSlotsToState sState;
       concVal \<leftarrow> newVar;
       let symInput = SymChoice choId concVal;
       let clashResult = previousMatch symInput sStateWithInput;
       let newPreviousMatch = newPreviousMatchChoice choId bnds previousMatch;
       (newCond, newTrace)
                 \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                         hasErr (Some symInput) timeout sState pos cont;
       contTrace \<leftarrow> isValidAndFailsWhen hasErr rest timeout timCont
                                        newPreviousMatch sState (pos + 1);
       return (if (newCond \<and> (\<not> clashResult) \<and> ensureBounds concVal bnds) then newTrace
               else contTrace) }" |
"isValidAndFailsWhen hasErr (Cons (Case (Notify obs) cont) rest)
                     timeout timCont previousMatch sState pos =
  do { (newLowSlot, newHighSlot, sStateWithInput) \<leftarrow> addFreshSlotsToState sState;
       let obsRes = symEvalObs obs sStateWithInput;
       let symInput = SymNotify;
       let clashResult = previousMatch symInput sStateWithInput;
       let newPreviousMatch = newPreviousMatchNotify obs previousMatch;
       (newCond, newTrace) \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                                   hasErr (Some symInput) timeout sState pos cont;
       contTrace \<leftarrow> isValidAndFailsWhen hasErr rest timeout timCont
                                        newPreviousMatch sState (pos + 1);
       return (if (newCond \<and> obsRes \<and> (\<not> clashResult)) then newTrace else contTrace) }"
  by pat_completeness auto
termination isValidAndFailsAux
  apply (relation "measure
                     (\<lambda> params .
                         case params of
                           Inl (_, (c, _)) \<Rightarrow> (size (c :: Contract)) * 3
                         | Inr (Inl (_, (_, (_, (_, (_, (_, (_, c)))))))) \<Rightarrow> (size (c :: Contract) * 3) + 1
                         | Inr (Inr (_, (cl, (_, (c, _))))) \<Rightarrow> (size_list size (cl :: Case list)) * 3 + size c * 3 + 2)")
  by simp_all

fun wrapper :: "Contract \<Rightarrow> (int \<times> int \<times> int \<times> int) list \<Rightarrow> State option \<Rightarrow> bool Symbolic" where
"wrapper c st maybeState = do { ess \<leftarrow> mkInitialSymState st maybeState;
                                isValidAndFailsAux False c ess }"

fun hasWarnings :: "TransactionOutput \<Rightarrow> bool" where
"hasWarnings (TransactionError _) = False" |
"hasWarnings (TransactionOutput txOutRec) = (Nil \<noteq> txOutWarnings txOutRec)"

(* Functions for calculating symbolic variables and output *)

type_synonym SymVarsOutput = "int list \<times> (int \<times> int \<times> int \<times> int) list"

fun repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"repeat 0 x = Nil" |
"repeat (Suc n) x = (Cons x (repeat n x))"

fun padWithMinusOnes :: "nat \<Rightarrow> (int \<times> int \<times> int \<times> int) list \<Rightarrow> (int \<times> int \<times> int \<times> int) list" where
"padWithMinusOnes n l = repeat (n - length l) (-1, -1, -1, -1) @ l"

fun combineOutputs :: "nat \<Rightarrow> (int \<times> int \<times> int \<times> int) list list \<Rightarrow> (int \<times> int \<times> int \<times> int) list" where
"combineOutputs execBranch l = padWithMinusOnes (fold max (map length l) 0) (l ! execBranch)"

fun combineSymVarsOutput :: "nat \<Rightarrow> SymVarsOutput list \<Rightarrow> SymVarsOutput" where
"combineSymVarsOutput executionBranch symVarsOutput =
   (concat (map fst symVarsOutput), combineOutputs executionBranch (map snd symVarsOutput))"

fun calculateSymVars_mkInitialSymState :: "int \<Rightarrow> int \<Rightarrow> State option \<Rightarrow> SymState \<times> SymVarsOutput" where
"calculateSymVars_mkInitialSymState ls hs None =
  (SymState \<lparr> lowSlot = ls
            , highSlot = hs
            , traces = Nil
            , paramTrace = Nil
            , symInput = None
            , whenPos = 0
            , symAccounts = Nil
            , symChoices = Nil
            , symBoundValues = Nil
            \<rparr>, ([hs, ls], []))" |
"calculateSymVars_mkInitialSymState ls hs (Some \<lparr> accounts = accs
                                                , choices = cho
                                                , boundValues = bVal
                                                , minSlot = ms \<rparr>) =
  (SymState \<lparr> lowSlot = max ms ls
            , highSlot = hs
            , traces = Nil
            , paramTrace = Nil
            , symInput = None
            , whenPos = 0
            , symAccounts = accs
            , symChoices = cho
            , symBoundValues = bVal \<rparr>, ([hs, ls], []))"

fun calculateSymVars_updateSymInput :: "SymInput option \<Rightarrow> SymState \<Rightarrow> SymState" where
"calculateSymVars_updateSymInput None symState = symState" |
"calculateSymVars_updateSymInput (Some (SymDeposit accId _ tok val)) (SymState symState) =
  (let resultVal = findWithDefault 0 (accId, tok) (symAccounts symState)
                    + max 0 val in
   SymState (symState \<lparr> symAccounts :=
                            MList.insert (accId, tok) resultVal
                                         (symAccounts symState) \<rparr>))" |
"calculateSymVars_updateSymInput (Some (SymChoice choId val)) (SymState symState) =
  SymState (symState \<lparr> symChoices := MList.insert choId val (symChoices symState) \<rparr>)" |
"calculateSymVars_updateSymInput (Some SymNotify) symState =
  symState"

fun calculateSymVars_addTransaction :: "int \<Rightarrow> int \<Rightarrow> SymInput option \<Rightarrow> SymState \<Rightarrow> int \<Rightarrow>
                                        SymState" where
"calculateSymVars_addTransaction newLowSlot newHighSlot None
                (SymState symState) pos =
  (let uSymInput = calculateSymVars_updateSymInput None
                      (SymState
                         (symState \<lparr> lowSlot := newLowSlot
                                   , highSlot := newHighSlot
                                   , symInput := None
                                   , whenPos := pos
                                   \<rparr>)) in
   uSymInput)" |
"calculateSymVars_addTransaction newLowSlot newHighSlot newSymInput (SymState symState) pos =
  (let uSymInput = calculateSymVars_updateSymInput newSymInput
                      (SymState
                         (symState \<lparr> lowSlot := newLowSlot
                                   , highSlot := newHighSlot
                                   , symInput := newSymInput
                                   , whenPos := pos
                                   \<rparr>)) in
   uSymInput)"

fun firstMatchesSymInput :: "SymInput \<Rightarrow> Transaction \<Rightarrow> bool" where
"firstMatchesSymInput sInput transaction =
  (case inputs transaction of
     Nil \<Rightarrow> False
   | Cons h t \<Rightarrow> (case sInput of
                     SymDeposit accId party token amount \<Rightarrow> (h = IDeposit accId party token amount)
                   | SymChoice choId cho \<Rightarrow> (h = IChoice choId cho)
                   | SymNotify \<Rightarrow> (h = INotify)))"

fun addSymVars :: "int list \<Rightarrow> SymVarsOutput \<Rightarrow> SymVarsOutput" where
"addSymVars l (vars, transactions) = (l @ vars, transactions)"

fun getFirstChoice :: "Transaction \<Rightarrow> ChosenNum option" where
"getFirstChoice tra =
   (case inputs tra of
      Cons (IChoice _ v) _ \<Rightarrow> Some v
    | _ \<Rightarrow> None)"

fun isValidChoice :: "ChoiceId \<Rightarrow> Bound list \<Rightarrow> Transaction \<Rightarrow> bool" where
"isValidChoice choId bounds tra =
  (case inputs tra of
     Cons (IChoice traChoId traCho) _ \<Rightarrow> ((traChoId = choId) \<and> (inBounds traCho bounds))
   | _ \<Rightarrow> False)"

function (sequential)
    calculateSymVars_isValidAndFailsAux :: "Transaction \<Rightarrow> Transaction list \<Rightarrow> Contract \<Rightarrow> SymState \<Rightarrow> SymVarsOutput"  and
    calculateSymVars_applyInputConditions :: "Transaction \<Rightarrow> Transaction list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> SymInput option \<Rightarrow>
                                              SymState \<Rightarrow> int \<Rightarrow> Contract \<Rightarrow>
                                              SymVarsOutput" and
    calculateSymVars_isValidAndFailsWhen :: "Transaction \<Rightarrow> Transaction list \<Rightarrow> Case list \<Rightarrow> int \<Rightarrow> Contract \<Rightarrow>
                                             SymState \<Rightarrow> int \<Rightarrow> SymVarsOutput" where
"calculateSymVars_isValidAndFailsAux tra traList Close (SymState symState) =
   ([], [(lowSlot symState, highSlot symState,
          getSymValFrom (symInput symState), whenPos symState)])" |
"calculateSymVars_isValidAndFailsAux tra traList (Pay accId payee tok val cont) (SymState symState) =
   (let concVal = symEvalVal val (SymState symState);
        originalMoney = findWithDefault 0 (accId, tok) (symAccounts symState);
        remainingMoneyInAccount = originalMoney - max 0 concVal;
        newAccs = MList.insert (accId, tok) (max 0 remainingMoneyInAccount)
                               (symAccounts symState);
        finalSState = SymState (symState \<lparr> symAccounts :=
         (case payee of
             Account destAccId \<Rightarrow>
              MList.insert (destAccId, tok)
                           (min originalMoney (max 0 concVal)
                             + findWithDefault 0 (destAccId, tok) newAccs)
                           newAccs
           | _ \<Rightarrow> newAccs) \<rparr>) in
    calculateSymVars_isValidAndFailsAux tra traList cont finalSState)" |
"calculateSymVars_isValidAndFailsAux tra traList (If obs cont1 cont2) symState =
   (let obsVal = symEvalObs obs symState;
        contVal1 = calculateSymVars_isValidAndFailsAux tra traList cont1 symState;
        contVal2 = calculateSymVars_isValidAndFailsAux tra traList cont2 symState in
    combineSymVarsOutput (if obsVal then 0 else 1) [contVal1, contVal2])" |
"calculateSymVars_isValidAndFailsAux tra traList (When list timeout cont) sState =
  calculateSymVars_isValidAndFailsWhen tra traList list timeout cont sState 1" |
"calculateSymVars_isValidAndFailsAux tra traList (Let valId val cont) (SymState symState) =
   (let concVal = symEvalVal val (SymState symState);
        newBVMap = MList.insert valId concVal (symBoundValues symState);
        newSymState = SymState (symState \<lparr> symBoundValues := newBVMap \<rparr>) in
    calculateSymVars_isValidAndFailsAux tra traList cont newSymState)" |
"calculateSymVars_isValidAndFailsAux tra traList (Assert obs cont) symState =
   calculateSymVars_isValidAndFailsAux tra traList cont symState" |
"calculateSymVars_applyInputConditions tra traList ls hs maybeSymInput (SymState symState) pos cont =
  (let newSState = calculateSymVars_addTransaction ls hs maybeSymInput (SymState symState) pos;
       oldLowSlot = lowSlot symState;
       oldHighSlot = highSlot symState;
       oldSymInp = symInput symState;
       oldPos = whenPos symState;
       (symVars, symOutput) = calculateSymVars_isValidAndFailsAux tra traList cont newSState
   in (symVars, symOutput @ [(oldLowSlot, oldHighSlot, getSymValFrom oldSymInp, oldPos)]))" |

"calculateSymVars_isValidAndFailsWhen tra traList Nil timeout cont symState pos =
   (let (low, high) = interval tra in
    if low \<ge> timeout
    then addSymVars [low, high] (calculateSymVars_applyInputConditions tra traList low high None symState 0 cont)
    else (case traList of
            Nil \<Rightarrow> addSymVars [0, 0] (calculateSymVars_applyInputConditions tra traList 0 0 None symState 0 cont)
          | Cons h t \<Rightarrow> let (newLow, newHigh) = interval h in
                        addSymVars [newLow, newHigh] (calculateSymVars_applyInputConditions h t newLow newHigh None symState 0 cont)))" |
"calculateSymVars_isValidAndFailsWhen tra traList (Cons (Case (Deposit accId party token val) cont) rest)
                     timeout timCont (SymState symState) pos =
       (let (low, high) = interval tra;
            concVal = symEvalVal val (SymState symState);
            sInput = SymDeposit accId party token concVal;
            (newTra, newTraList) = if (high < timeout \<and> firstMatchesSymInput sInput tra)
                                   then (tra, traList)
                                   else (case traList of
                                           Nil \<Rightarrow> (tra, traList)
                                         | (Cons h t) \<Rightarrow> (h, t));
            (newLowSlot, newHighSlot) = interval newTra;
            symStateWithInput = SymState (symState \<lparr> lowSlot := newLowSlot,
                                                     highSlot := newHighSlot \<rparr>);
            newConcVal = symEvalVal val symStateWithInput;
            newSInput = SymDeposit accId party token newConcVal;
            newCond = newHighSlot < timeout \<and> firstMatchesSymInput newSInput newTra;
            newTrace = calculateSymVars_applyInputConditions newTra newTraList newLowSlot newHighSlot
                                         (Some newSInput) (SymState symState) pos cont;
            contTrace = calculateSymVars_isValidAndFailsWhen tra traList rest timeout timCont
                                                             (SymState symState) (pos + 1) in
       addSymVars [newLowSlot, newHighSlot] (combineSymVarsOutput (if newCond then 0 else 1) [newTrace, contTrace]))" |
"calculateSymVars_isValidAndFailsWhen tra traList (Cons (Case (Choice choId bnds) cont) rest)
                     timeout timCont (SymState symState) pos =
       (let (low, high) = interval tra;
            (newTra, newTraList) = if (high < timeout \<and> isValidChoice choId bnds tra)
                                   then (tra, traList)
                                   else (case traList of
                                           Nil \<Rightarrow> (tra, traList)
                                         | (Cons h t) \<Rightarrow> (h, t));
            (newLowSlot, newHighSlot) = interval newTra;
            newConcVal = case getFirstChoice newTra of
                           None \<Rightarrow> 0
                         | Some x \<Rightarrow> x;
            newSInput = SymChoice choId newConcVal;
            newCond = newHighSlot < timeout \<and> isValidChoice choId bnds newTra;
            newTrace = calculateSymVars_applyInputConditions newTra newTraList newLowSlot newHighSlot
                                         (Some newSInput) (SymState symState) pos cont;
            contTrace = calculateSymVars_isValidAndFailsWhen tra traList rest timeout timCont
                                                             (SymState symState) (pos + 1) in
       addSymVars [newLowSlot, newHighSlot, newConcVal] (combineSymVarsOutput (if newCond then 0 else 1) [newTrace, contTrace]))" |
"calculateSymVars_isValidAndFailsWhen tra traList (Cons (Case (Notify obs) cont) rest)
                     timeout timCont (SymState symState) pos =
       (let (low, high) = interval tra;
            sInput = SymNotify;
            obsRes = symEvalObs obs (SymState symState);
            (newTra, newTraList) = if (high < timeout \<and> obsRes)
                                   then (tra, traList)
                                   else (case traList of
                                           Nil \<Rightarrow> (tra, traList)
                                         | (Cons h t) \<Rightarrow> (h, t));
            (newLowSlot, newHighSlot) = interval newTra;
            symStateWithInput = SymState (symState \<lparr> lowSlot := newLowSlot,
                                                     highSlot := newHighSlot \<rparr>);
            newSInput = SymNotify;
            newObsRes = symEvalObs obs symStateWithInput;
            newCond = newHighSlot < timeout \<and> firstMatchesSymInput newSInput newTra;
            newTrace = calculateSymVars_applyInputConditions newTra newTraList newLowSlot newHighSlot
                                         (Some newSInput) (SymState symState) pos cont;
            contTrace = calculateSymVars_isValidAndFailsWhen tra traList rest timeout timCont
                                                             (SymState symState) (pos + 1) in
       addSymVars [newLowSlot, newHighSlot] (combineSymVarsOutput (if newCond then 0 else 1) [newTrace, contTrace]))"
  by pat_completeness auto
termination calculateSymVars_isValidAndFailsAux
  apply (relation "measure
                     (\<lambda> params .
                         case params of
                           Inl (_, (_, (c, _))) \<Rightarrow> (size (c :: Contract)) * 3
                         | Inr (Inl (_, (_, (_, (_, (_, (_, (_, c)))))))) \<Rightarrow> (size (c :: Contract) * 3) + 1
                         | Inr (Inr (_, (_, (cl, (_, (c, _)))))) \<Rightarrow> (size_list size (cl :: Case list)) * 3 + size c * 3 + 2)")
  by simp_all

fun calculateSymVars :: "State option \<Rightarrow> Transaction list \<Rightarrow> Contract \<Rightarrow> SymVarsOutput" where
"calculateSymVars state (Cons h t) cont =
  (let (low, high) = interval h;
       (symState, symVars) = calculateSymVars_mkInitialSymState low high state in
       combineSymVarsOutput 1 [symVars, calculateSymVars_isValidAndFailsAux h t cont symState])" |
"calculateSymVars state Nil cont = ([], [])"

(* Test1 for calculateSymVars *)

definition role_alice :: PubKey where
"role_alice = 1"

definition role_bob :: PubKey where
"role_bob = 2"

definition role_carol :: PubKey where
"role_carol = 3"

definition token_ada :: Token where
"token_ada = Token 0 0"

definition choice_choice :: ChoiceName where
"choice_choice = 1"

definition badEscrow_aux :: Contract where
"badEscrow_aux = (When [
                  (Case
                     (Choice
                        (ChoiceId choice_choice
                           role_alice) [
                        (0, 1)])
                     (When [
                        (Case
                           (Choice
                              (ChoiceId choice_choice
                                 role_bob) [
                              (0, 1)])
                           (If
                              (ValueEQ
                                 (ChoiceValue
                                    (ChoiceId choice_choice
                                       role_alice))
                                 (ChoiceValue
                                    (ChoiceId choice_choice
                                       role_bob)))
                              (If
                                 (ValueEQ
                                    (ChoiceValue
                                       (ChoiceId choice_choice
                                          role_alice))
                                    (Constant 0))
                                 (Pay
                                    role_alice
                                    (Party
                                       role_bob)
                                    token_ada
                                    (Constant 450) Close) Close)
                              (When [
                                    (Case
                                       (Choice
                                          (ChoiceId choice_choice
                                             role_carol) [
                                          (1, 1)]) Close)
                                    ,
                                    (Case
                                       (Choice
                                          (ChoiceId choice_choice
                                             role_carol) [
                                          (0, 0)])
                                       (Pay
                                          role_alice
                                          (Party
                                             role_bob)
                                          token_ada
                                          (Constant 451) Close))] 100 Close)))] 60
                        (When [
                              (Case
                                 (Choice
                                    (ChoiceId choice_choice
                                       role_carol) [
                                    (1, 1)]) Close)
                              ,
                              (Case
                                 (Choice
                                    (ChoiceId choice_choice
                                       role_carol) [
                                    (0, 0)])
                                 (Pay
                                    role_alice
                                    (Party
                                       role_bob)
                                    token_ada
                                    (Constant 450) Close))] 100 Close)))] 40
                  (When [
                        (Case
                           (Choice
                              (ChoiceId choice_choice
                                 role_carol) [
                              (1, 1)]) Close)
                        ,
                        (Case
                           (Choice
                              (ChoiceId choice_choice
                                 role_carol) [
                              (0, 0)])
                           (Pay
                              role_alice
                              (Party
                                 role_bob)
                              token_ada
                              (Constant 450) Close))] 100 Close))"

definition badEscrow :: Contract where
"badEscrow = When [
            (Case
               (Deposit
                  role_alice
                  role_alice
                  token_ada
                  (Constant 450))
               badEscrow_aux)] 10 Close"

definition badEscrowOffendingTrace :: "Transaction list" where
"badEscrowOffendingTrace = [ \<lparr> interval = (2, 3)
                             , inputs = [IDeposit role_alice role_alice token_ada 450]
                             \<rparr>
                           , \<lparr> interval = (4, 5)
                             , inputs = [IChoice (ChoiceId choice_choice role_alice) 0]
                             \<rparr>
                           , \<lparr> interval = (6, 7)
                             , inputs = [IChoice (ChoiceId choice_choice role_bob) 1]
                             \<rparr>
                           , \<lparr> interval = (8, 9)
                             , inputs = [IChoice (ChoiceId choice_choice role_carol) 0]
                             \<rparr>
                           ]"

value "calculateSymVars (Some (emptyState 0)) badEscrowOffendingTrace badEscrow"

value "execute (wrapper badEscrow [(8, 9, 0, 2), (6, 7, 1, 1), (4, 5, 0, 1), (2, 3, 450, 1), (2, 3, 0, 0)]
                        (Some (emptyState 0))) [3, 2, 2, 3, 4, 5, 0, 6, 7, 1, 8, 9, 0, 8, 9, 0, 8, 9, 6, 7, 8, 9, 0, 8, 9, 0, 8, 9, 4, 5, 6, 7, 1, 6, 7, 1, 6, 7, 4, 5]"

(* Invariants of symbolic execution *)
fun symStateToState :: "SymState \<Rightarrow> State" where
"symStateToState (SymState symState) =
   \<lparr> accounts = symAccounts symState
   , choices = symChoices symState
   , boundValues = symBoundValues symState
   , minSlot = lowSlot symState \<rparr>"

fun symStateToEnv :: "SymState \<Rightarrow> Environment" where
"symStateToEnv (SymState symState) = \<lparr> slotInterval = (lowSlot symState, highSlot symState) \<rparr>"

lemma symEval_eval_equivalence : "symEvalVal val symState = evalValue (symStateToEnv symState) (symStateToState symState) val"
                                 "symEvalObs obs symState = evalObservation (symStateToEnv symState) (symStateToState symState) obs"
  apply (induction val symState and obs symState rule:symEvalVal_symEvalObs.induct)
  by auto

lemma closeContractRemains_reduceContractUntilQuiescent : "reduceContractUntilQuiescent env fixSta Close = ContractQuiescent reduceWarns pays curState cont \<Longrightarrow> cont = Close"
  by (simp add: reduceClose_is_Close)

lemma closeContractRemains_applyAllLoop : "applyAllLoop env fixSta Close inps warn pay = ApplyAllSuccess newWarn newPay newState cont \<Longrightarrow> cont = Close"
  apply (simp only:applyAllLoop.simps[of env fixSta "Close" inps warn pay])
  apply (cases "reduceContractUntilQuiescent env fixSta Close")
  subgoal for reduceWarns pays curState cont
    apply (simp only:refl ReduceResult.case)
    apply (induction inps)
    apply (simp add: reduceClose_is_Close)
    using reduceClose_is_Close by fastforce
  by simp

lemma closeContractRemains : "validAndPositive_state st \<Longrightarrow>
                       computeTransaction inps st Close = TransactionOutput \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow> newCont = Close"
  apply (simp del:validAndPositive_state.simps)
  apply (cases "fixInterval (interval inps) st")
  apply (simp only:refl IntervalResult.case)
  subgoal for env fixSta
    apply (cases "applyAllInputs env fixSta Close (inputs inps)")
    subgoal for warnings payments newState cont
      apply (simp only:refl ApplyAllResult.case)
      by (metis TransactionOutput.distinct(1) TransactionOutput.inject(1) TransactionOutputRecord.ext_inject applyAllInputs.simps closeContractRemains_applyAllLoop)
    by simp_all
  apply (simp only:refl IntervalResult.case)
  by simp

lemma noCounterExamplePropagatesComputeEmptyTransaction_Close : "\<not> isCounterExample (execute (wrapper Close t (Some sta)) x)"
  apply simp
  apply (auto split:option.splits prod.splits simp add:bind_def)
  subgoal for a b
    apply (cases a)
    by (simp add:return_def)
  done

fun isNonPositivePay :: "Environment \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> bool" where
"isNonPositivePay env state val = (evalValue env state val \<le> 0)"

fun isPartialPay :: "Environment \<Rightarrow> State \<Rightarrow> AccountId \<Rightarrow> Token \<Rightarrow> Value \<Rightarrow> bool" where
"isPartialPay env state accId tok val = (moneyInAccount accId tok (accounts state) < evalValue env state val)"

lemma reductionLoop_keepsWarnings : "reductionLoop env state contract warnings effects = ContractQuiescent reduceWarns reduceEffects reduceState reduceNewContract \<Longrightarrow> \<exists>suff. reduceWarns = (rev warnings) @ suff"
  apply (induction env state contract warnings effects arbitrary: reduceWarns reduceEffects reduceState reduceNewContract rule:reductionLoop.induct)
  subgoal for env state contract warnings payments reduceWarns reduceEffects reduceState reduceNewContract
    apply (subst (asm) (2) reductionLoop.simps)
    apply (cases "reduceContractStep env state contract")
    subgoal for stepWarns stepEffects stepState stepNewContract
      apply (simp only:refl ReduceStepResult.case Let_def)
      by fastforce
     apply auto[1]
    by simp
  done

lemma onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep : "reduceContractStep env state contract = Reduced warnings effects newState newContract \<Longrightarrow>
                                                                     reductionLoop env state contract wa ef = ContractQuiescent reduceWarns reduceEffects reduceState reduceNewContract \<Longrightarrow>
                                                                     warnings \<noteq> ReduceNoWarning \<Longrightarrow> reduceWarns \<noteq> []"
  apply (simp only: reductionLoop.simps)
  apply (cases "reduceContractStep env state contract")
  subgoal for redStepwarning redStepEffect redStepState redStepContract
    apply (simp only:Let_def refl ReduceStepResult.case)
    using reductionLoop_keepsWarnings by fastforce
   apply simp
  by simp

lemma onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus_aux : "warnings \<noteq> ReduceNoWarning \<Longrightarrow>
                                                                              reduceWarns = warnings # suff \<Longrightarrow>
                                                                              convertReduceWarnings reduceWarns \<noteq> []"
  apply (induction suff arbitrary:reduceWarns)
  apply (cases warnings)
  apply simp_all
  subgoal for a suff reduceWarns
  apply (cases warnings)
  by simp_all
  done

lemma onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus_aux2 : "warnings = i @ [l] \<Longrightarrow> l \<noteq> ReduceNoWarning \<Longrightarrow>
                                                                              reduceWarns = warnings @ suff \<Longrightarrow>
                                                                              convertReduceWarnings reduceWarns \<noteq> []"
  apply (induction i arbitrary:reduceWarns warnings l suff)
  apply (simp add: onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus_aux)
  by (metis append_Cons convertReduceWarnings.simps(2) onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus_aux)

lemma onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus : "reduceContractStep env state contract = Reduced warnings effects newState newContract \<Longrightarrow>
                                                                          reductionLoop env state contract wa ef = ContractQuiescent reduceWarns reduceEffects reduceState reduceNewContract \<Longrightarrow>
                                                                          warnings \<noteq> ReduceNoWarning \<Longrightarrow> convertReduceWarnings reduceWarns \<noteq> []"
  apply (simp only: reductionLoop.simps)
  apply (cases "reduceContractStep env state contract")
  subgoal for redStepwarning redStepEffect redStepState redStepContract
    apply (simp only:Let_def refl ReduceStepResult.case if_False)
    apply (subgoal_tac "\<exists>suff. reduceWarns = (rev ([warnings] @ wa)) @ suff")
    using onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus_aux2 apply auto[1]
    apply (rule reductionLoop_keepsWarnings)
    by simp
  by simp_all

lemma onceAWarningAlwaysAWarning_applyAllLoop_reduceContractStep : "reduceContractStep env st c = Reduced warnings effects newState newContract \<Longrightarrow>
                                                                    applyAllLoop env st c inp wa ef = ApplyAllSuccess applyWarnings applyEffects applyNewState applyNewContract \<Longrightarrow>
                                                                    warnings \<noteq> ReduceNoWarning \<Longrightarrow> applyWarnings \<noteq> []"
  apply (subst (asm) applyAllLoop.simps[of env st c inp wa ef])
  apply (subst (asm) reduceContractUntilQuiescent.simps)
  apply (cases "reductionLoop env st c [] []")
  apply (simp only:refl ReduceResult.case)
  apply (cases inp)
  using onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus apply auto[1]
  apply (simp only:refl list.case)
  subgoal for reduceWarns reduceEffects reduceState reduceNewContract h t
    apply (cases "applyInput env reduceState h reduceNewContract")
    apply (simp only:refl ApplyResult.case)
    using applyAllInputsPrefix1 onceAWarningAlwaysAWarning_reductionLoop_reduceContractStep_plus apply fastforce
    by simp
  by simp

lemma noCounterExamplePropagatesComputeEmptyTransaction_Pay_NonPositivePay : "validAndPositive_state st \<Longrightarrow>
    computeTransaction \<lparr>interval = (lo, hi), inputs = []\<rparr> st (Pay accountId payee token val subCont) = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    env = \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> \<Longrightarrow> fixedSt = (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) \<Longrightarrow> hi \<ge> lo \<Longrightarrow> hi \<ge> minSlot st \<Longrightarrow> isNonPositivePay env fixedSt val \<Longrightarrow> False"
  apply (simp only:computeTransaction.simps Let_def)
  apply (simp del:validAndPositive_state.simps applyAllLoop.simps isPartialPay.simps isNonPositivePay.simps add:Let_def)
  apply (cases "applyAllLoop \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) (Pay accountId payee token val subCont) [] [] []")
  subgoal for applyWarnings applyEffects applyNewState applyNewContract
    apply (simp only:ApplyAllResult.case refl)
    apply (auto split:"if_split" simp del:validAndPositive_state.simps evalValue.simps applyAllLoop.simps isPartialPay.simps isNonPositivePay.simps)
    apply (cases "Pay accountId payee token val subCont = applyNewContract")
     apply (simp only:refl if_True)
     apply blast
    apply (simp only:refl if_False)
    apply (cases "reduceContractStep \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) (Pay accountId payee token val subCont)")
    subgoal for reduceWarning reduceEffect reduceState reduceContract
      apply (subgoal_tac "reduceWarning \<noteq> ReduceNoWarning")
      apply (metis TransactionOutput.inject(1) TransactionOutputRecord.ext_inject onceAWarningAlwaysAWarning_applyAllLoop_reduceContractStep)
      apply (simp only:reduceContractStep.simps)
      by auto
     apply auto[1]
    by simp
   apply simp
  by simp

lemma noCounterExamplePropagatesComputeEmptyTransaction_Pay_PartialPay : "validAndPositive_state st \<Longrightarrow>
    computeTransaction \<lparr>interval = (lo, hi), inputs = []\<rparr> st (Pay accountId payee token val subCont) = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    env = \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> \<Longrightarrow> fixedSt = (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) \<Longrightarrow> hi \<ge> lo \<Longrightarrow> hi \<ge> minSlot st \<Longrightarrow> isPartialPay env fixedSt accountId token val \<Longrightarrow> \<not> isNonPositivePay env fixedSt val \<Longrightarrow> False"
  apply (simp only:computeTransaction.simps Let_def)
  apply (simp del:validAndPositive_state.simps applyAllLoop.simps isPartialPay.simps isNonPositivePay.simps add:Let_def)
  apply (cases "applyAllLoop \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) (Pay accountId payee token val subCont) [] [] []")
  subgoal for applyWarnings applyEffects applyNewState applyNewContract
    apply (simp only:ApplyAllResult.case refl)
    apply (auto split:"if_split" simp del:validAndPositive_state.simps evalValue.simps applyAllLoop.simps isPartialPay.simps isNonPositivePay.simps)
    apply (cases "Pay accountId payee token val subCont = applyNewContract")
     apply (simp only:refl if_True)
     apply blast
    apply (simp only:refl if_False)
    apply (cases "reduceContractStep \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) (Pay accountId payee token val subCont)")
    subgoal for reduceWarning reduceEffect reduceState reduceContract
      apply (subgoal_tac "reduceWarning \<noteq> ReduceNoWarning")
      apply (metis TransactionOutput.inject(1) TransactionOutputRecord.ext_inject onceAWarningAlwaysAWarning_applyAllLoop_reduceContractStep)
      apply (simp only:reduceContractStep.simps)
      apply (subgoal_tac "let moneyToPay = evalValue \<lparr>slotInterval = (max lo (minSlot st), hi)\<rparr> (st\<lparr>minSlot := max lo (minSlot st)\<rparr>) val;
                              balance = moneyInAccount accountId token (accounts (st\<lparr>minSlot := max lo (minSlot st)\<rparr>));
                              paidMoney = min balance moneyToPay;
                              moneyToPay2 = evalValue env fixedSt val;
                              balance2 = moneyInAccount accountId token (accounts fixedSt);
                              paidMoney2 = min balance2 moneyToPay2
                          in Reduced (if min balance moneyToPay < moneyToPay
                                      then ReducePartialPay accountId payee token paidMoney moneyToPay
                                      else ReduceNoWarning)
                                     (fst (giveMoney payee token paidMoney2
                                                     (updateMoneyInAccount accountId token (balance2 - paidMoney2) (accounts fixedSt))))
                                     (st\<lparr> minSlot := max lo (minSlot st),
                                          accounts := snd (giveMoney payee token paidMoney2
                                                                     (updateMoneyInAccount accountId token (balance2 - paidMoney2) (accounts fixedSt))) \<rparr>)
                                     subCont
                           = Reduced reduceWarning reduceEffect reduceState reduceContract")
      apply (smt ReduceStepResult.inject ReduceWarning.distinct(3) isPartialPay.elims(2))
      apply (simp only:Let_def)
      by (simp add:prod.case_eq_if)
     apply simp
    by simp
   apply simp
  by simp

theorem staticAnalysisComplete_aux : "validAndPositive_state st \<Longrightarrow>
                                      hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                                , txOutPayments = Nil
                                                                , txOutState = st
                                                                , txOutContract = c \<rparr> t) \<Longrightarrow>
                                      calculateSymVars (Some st) (traceListToSingleInput t) c = (x2, t2) \<Longrightarrow>
                                      isCounterExample (execute (wrapper c t2 (Some st)) x2)"
  oops

theorem staticAnalysisComplete : "validAndPositive_state st \<Longrightarrow>
                                  (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                                  , txOutPayments = Nil
                                                                  , txOutState = st
                                                                  , txOutContract = c \<rparr> t)) \<Longrightarrow>
                                  (\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x))"
 (* by (meson const.cases staticAnalysisComplete_aux) *)
  oops

(*
theorem staticAnalysisSound : "validAndPositive_state st \<Longrightarrow>
                               (\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow>
                               (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                               , txOutPayments = Nil
                                                               , txOutState = st
                                                               , txOutContract = c \<rparr> t))"
  oops

theorem staticAnalysisWorks : "validAndPositive_state st \<Longrightarrow>
                               (\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x)) =
                               (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                               , txOutPayments = Nil
                                                               , txOutState = st
                                                               , txOutContract = c \<rparr> t))"
  using staticAnalysisComplete staticAnalysisSound by blast
 *)

end
