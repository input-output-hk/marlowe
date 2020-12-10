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
       contTrace \<leftarrow> isValidAndFailsWhen hasErr rest timeout timCont
                                        newPreviousMatch sState (pos + 1);
       (newCond, newTrace)
                 \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                         hasErr (Some symInput) timeout sState pos cont;
       return (if (newCond \<and> (\<not> clashResult)) then (ensureBounds concVal bnds \<and> newTrace)
               else contTrace) }" |
"isValidAndFailsWhen hasErr (Cons (Case (Notify obs) cont) rest)
                     timeout timCont previousMatch sState pos =
  do { (newLowSlot, newHighSlot, sStateWithInput) \<leftarrow> addFreshSlotsToState sState;
       let obsRes = symEvalObs obs sStateWithInput;
       let symInput = SymNotify;
       let clashResult = previousMatch symInput sStateWithInput;
       let newPreviousMatch = newPreviousMatchNotify obs previousMatch;
       contTrace \<leftarrow> isValidAndFailsWhen hasErr rest timeout timCont
                                        newPreviousMatch sState (pos + 1);
       (newCond, newTrace) \<leftarrow> applyInputConditions newLowSlot newHighSlot
                                                   hasErr (Some symInput) timeout sState pos cont;
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

lemma giveMoneyPreserves_validState : "validAndPositive_state fixSta \<Longrightarrow> giveMoney payee token (min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val))
   (updateMoneyInAccount accountId token (moneyInAccount accountId token (accounts fixSta) - min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val)) (accounts fixSta)) =
  (givePayment, giveFinalAccs) \<Longrightarrow> validAndPositive_state (fixSta\<lparr>accounts := giveFinalAccs\<rparr>)"
  oops

lemma comp_pair_eta : "\<And>f g. f \<circ> g = (\<lambda> (a, b). f (g (a, b)))"
  by (simp add: comp_def cond_case_prod_eta)

lemma split_tuple : "(a = (b, c)) = ((fst a = b) \<and> ((snd a = c)))"
  by auto

lemma accountTransferEquivalence :
  "\<not> evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<le> 0 \<Longrightarrow>
   \<not> moneyInAccount accountId token accs < evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<Longrightarrow>
   snd (giveMoney payee token (min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val))
     (updateMoneyInAccount accountId token
       (moneyInAccount accountId token accs - min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val)) accs)) =
    (let concVal = evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val;
         originalMoney = findWithDefault 0 (accountId, token) accs;
         remainingMoneyInAccount = originalMoney - max 0 concVal;
         newAccs = MList.insert (accountId, token) (max 0 remainingMoneyInAccount)
                                (symAccounts sState) in
         (case payee of
              Account destAccId \<Rightarrow>
                  MList.insert (destAccId, token)
                               (min originalMoney (max 0 concVal)
                                + findWithDefault 0 (destAccId, token) newAccs)
                               newAccs
             | _ \<Rightarrow> newAccs))"
  oops

lemma symbolicPreservesConstraintsAfterPay_aux :
  "\<not> evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<le> 0 \<Longrightarrow>
    \<not> moneyInAccount accountId token accs < evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<Longrightarrow>
    giveMoney payee token (min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val))
     (updateMoneyInAccount accountId token
       (moneyInAccount accountId token accs - min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val)) accs) =
    (givePayment, giveFinalAccs) \<Longrightarrow>
    fixSta = \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> \<Longrightarrow>
  lSlot \<le> hSlot \<Longrightarrow>
  mSlot \<le> lSlot \<Longrightarrow>
  isCounterExample
    (execute (isValidAndFailsAux False subCont (SymState \<lparr>lowSlot = lSlot, highSlot = hSlot, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = giveFinalAccs, symChoices = chos, symBoundValues = boundVals\<rparr>))
      x) \<Longrightarrow> 
      isCounterExample
            (execute (isValidAndFailsAux False (Pay accountId payee token val subCont)
                    (SymState \<lparr>lowSlot = lSlot, highSlot = hSlot, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = accs, symChoices = chos, symBoundValues = boundVals\<rparr>))
              x)"
  apply (simp only:isValidAndFailsAux.simps)
  apply (simp only:symEval_eval_equivalence symStateToEnv.simps symStateToState.simps SymStateRecord.simps)
  oops

lemma symbolicPreservesConstraintsAfterPay_aux2 :
  "\<not> evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<le> 0 \<Longrightarrow>
    \<not> moneyInAccount accountId token accs < evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val \<Longrightarrow>
    giveMoney payee token (min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val))
     (updateMoneyInAccount accountId token
       (moneyInAccount accountId token accs - min (moneyInAccount accountId token accs) (evalValue fixEnv \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> val)) accs) =
    (givePayment, giveFinalAccs) \<Longrightarrow>
    fixSta = \<lparr>accounts = accs, choices = chos, boundValues = boundVals, minSlot = mSlot\<rparr> \<Longrightarrow>
   isCounterExample
     (execute
       (generateSymbolicInterval (Some mSlot) \<bind>
        (\<lambda>(a, b).
            isValidAndFailsAux False subCont (SymState \<lparr>lowSlot = a, highSlot = b, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = giveFinalAccs, symChoices = chos, symBoundValues = boundVals\<rparr>)))
       x) \<Longrightarrow> 
       isCounterExample
             (execute
               (generateSymbolicInterval (Some mSlot) \<bind>
                (\<lambda>(a, b).
                    isValidAndFailsAux False (Pay accountId payee token val subCont)
                     (SymState \<lparr>lowSlot = a, highSlot = b, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = accs, symChoices = chos, symBoundValues = boundVals\<rparr>)))
               x)"
  apply (simp only:generateSymbolicInterval.simps)
  apply (simp only:inline_monads_ex1)
  apply (cases x)
  using newVar_failsForNil apply blast
  apply (simp only:abstract_newVar)
  subgoal for hSlot x2
    apply (cases x2)
    using newVar_failsForNil apply blast
    apply (simp only:abstract_newVar)
    subgoal for lSlot x3
    apply (auto simp only:abstract_constrain)
(* using symbolicPreservesConstraintsAfterPay_aux by blast *)
  oops
    
lemma symbolicPreservesConstraintsAfterPay : "\<not> evalValue fixEnv fixSta val \<le> 0 \<Longrightarrow>
                                             \<not> isPartialPay fixEnv fixSta accountId token val \<Longrightarrow>
                                             giveMoney payee token (min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val))
                                              (updateMoneyInAccount accountId token (moneyInAccount accountId token (accounts fixSta) - min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val)) (accounts fixSta)) =
                                             (givePayment, giveFinalAccs) \<Longrightarrow>
                                              (\<And>t x. \<not> isCounterExample (execute (wrapper (Pay accountId payee token val subCont) t (Some fixSta)) x)) \<Longrightarrow>
                                              (isCounterExample (execute (wrapper subCont t (Some (fixSta\<lparr>accounts := giveFinalAccs\<rparr>))) x)) \<Longrightarrow> False"
  apply (auto simp del:updateMoneyInAccount.simps moneyInAccount.simps)
  apply (cases fixSta)
  subgoal for accounts choices boundValues minSlot
    apply (simp only:mkInitialSymState.simps State.simps)
    (* Reorder to use composition instead of lambda expression *)
    apply (subgoal_tac "(\<And>t x. isCounterExample
                (execute
                  ((generateSymbolicInterval (Some minSlot) \<bind>
                    (return \<circ> (\<lambda>(ls, hs). SymState \<lparr>lowSlot = ls, highSlot = hs, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = accounts, symChoices = choices, symBoundValues = boundValues\<rparr>))) \<bind>
                   isValidAndFailsAux False (Pay accountId payee token val subCont))
                  x) \<Longrightarrow> False)")
    (* Remove original hypothesis *)
      apply (thin_tac "(\<And>t x. \<not> isCounterExample
                (execute
                  ((generateSymbolicInterval (Some minSlot) \<bind>
                    (\<lambda>(ls, hs). return (SymState \<lparr>lowSlot = ls, highSlot = hs, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = accounts, symChoices = choices, symBoundValues = boundValues\<rparr>))) \<bind>
                   isValidAndFailsAux False (Pay accountId payee token val subCont))
                  x))")
    (* Reorder to use composition instead of lambda expression *)
    apply (subgoal_tac "isCounterExample
      (execute
        ((generateSymbolicInterval (Some minSlot) \<bind>
          (return \<circ> (\<lambda>(ls, hs). SymState \<lparr>lowSlot = ls, highSlot = hs, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = giveFinalAccs, symChoices = choices, symBoundValues = boundValues\<rparr>))) \<bind>
         isValidAndFailsAux False subCont)
        x)")
    apply (thin_tac "(isCounterExample
      (execute
        ((generateSymbolicInterval (Some minSlot) \<bind>
          (\<lambda>(ls, hs). return (SymState \<lparr>lowSlot = ls, highSlot = hs, traces = [], paramTrace = t, symInput = None, whenPos = 0, symAccounts = giveFinalAccs, symChoices = choices, symBoundValues = boundValues\<rparr>))) \<bind>
         isValidAndFailsAux False subCont)
        x))")
      apply (simp only:inline_monad comp_pair_eta[symmetric])
      apply (simp only:comp_pair_eta prod.case)
    (* using symbolicPreservesConstraintsAfterPay_aux apply blast
       by (simp_all only: comp_pair_eta prod.case)
  done *)
oops

lemma noCounterExamplePropagatesComputeEmptyTransaction_Pay : "(\<And>st lo hi newPays newSta newCont t2 x2.
        validAndPositive_state st \<Longrightarrow>
        computeTransaction \<lparr>interval = (lo, hi), inputs = []\<rparr> st subCont = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
        (\<And>t x. \<not> isCounterExample (execute (wrapper subCont t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False) \<Longrightarrow>
    validAndPositive_state st \<Longrightarrow>
    computeTransaction \<lparr>interval = (lo, hi), inputs = []\<rparr> st (Pay accountId payee token val subCont) = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    (\<And>t x. \<not> isCounterExample (execute (wrapper (Pay accountId payee token val subCont) t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False"
  apply (cases "fixInterval (lo, hi) st")
  subgoal for env fixedSt
    apply (simp only:fixInterval.simps)
    apply (cases "hi < lo")
    apply simp
    apply (simp only:if_False Let_def)
    apply (cases "hi < minSlot st")
    apply simp
    apply (simp only:if_False Let_def)
    apply (cases "isNonPositivePay env fixedSt val")
    apply (metis IntervalResult.inject(1) noCounterExamplePropagatesComputeEmptyTransaction_Pay_NonPositivePay not_le)
    apply (cases "isPartialPay env fixedSt accountId token val")
    apply (metis IntervalResult.inject(1) noCounterExamplePropagatesComputeEmptyTransaction_Pay_PartialPay not_le)
    apply (simp only:computeTransaction.simps [of "\<lparr>interval = (lo, hi), inputs = []\<rparr>" st "Pay accountId payee token val subCont"] Let_def)
    apply (cases "fixInterval (interval \<lparr>interval = (lo, hi), inputs = []\<rparr>) st")
    subgoal for fixEnv fixSta
      apply (simp only:refl IntervalResult.case)
      apply (subgoal_tac "env = fixEnv")
      apply (simp only:applyAllInputs.simps applyAllLoop.simps[of fixEnv fixSta "Pay accountId payee token val subCont" "inputs \<lparr>interval = (lo, hi), inputs = []\<rparr>" "[]" "[]"])
      apply (simp only:reduceContractUntilQuiescent.simps reductionLoop.simps reduceContractStep.simps)
      apply (simp only:Let_def isNonPositivePay.simps refl)
      apply (subgoal_tac "evalValue fixEnv fixSta val \<le> 0 = False")
      apply (simp only:refl if_False)
      apply (cases "giveMoney payee token (min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val))
                          (updateMoneyInAccount accountId token (moneyInAccount accountId token (accounts fixSta) - min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val)) (accounts fixSta))")
      subgoal for givePayment giveFinalAccs
        apply (simp only:prod.case ReduceStepResult.case)
        apply (subgoal_tac "min (moneyInAccount accountId token (accounts fixSta)) (evalValue fixEnv fixSta val) < evalValue fixEnv fixSta val = False")
        apply (simp only:if_False if_True refl)
        subgoal premises fact
          apply (rule fact(1))
          apply (subgoal_tac "validAndPositive_state (fixSta\<lparr>accounts := giveFinalAccs\<rparr>)")
          apply blast
(*
          using fact(11) fact(14) fact(2) fixInterval_preserves_preserves_validAndPositive_state giveMoneyPreserves_validState apply blast
          (* ToDo *)
          using symbolicPreservesConstraintsAfterPay apply blast
          apply (rule fact(5))
        by simp
      apply simp
      by simp
    by simp
  by simp
*)
  oops

theorem noCounterExamplePropagatesComputeEmptyTransaction :
   "validAndPositive_state st \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    (\<And>t x. \<not> isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False"
  apply (induction c arbitrary: st lo hi newPays newSta newCont t2 x2)
  (* Case *)
  apply simp
  (* Close *)
  using closeContractRemains noCounterExamplePropagatesComputeEmptyTransaction_Close apply blast
  (* Pay *)
  subgoal for accountId payee token val subCont st lo hi newPays newSta newCont t2 x2
(*  apply (rule noCounterExamplePropagatesComputeEmptyTransaction_Pay)
    by blast*)
    oops


theorem noCounterExamplePropagatesComputeSingleInputTransaction :
   "validAndPositive_state st \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [inp] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
     (\<And>t x. \<not> isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False"
  oops

theorem computeEmptyTransactionWarningIsCounterExample :
   "validAndPositive_state st \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = newWarn, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newWarn = []"
  oops

theorem computeSingleInputTransactionWarningIsCounterExample :
   "validAndPositive_state st \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [inp] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = newWarn, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newWarn = []"
  oops

lemma staticAnalysisComplete_emptyTransaction : "(\<And>c st p.
        validAndPositive_state st \<Longrightarrow>
        (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
        hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False) \<Longrightarrow>
    validAndPositive_state st \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    hasWarnings (playTraceAux \<lparr>txOutWarnings = newWarns, txOutPayments = p @ newPays, txOutState = newSta, txOutContract = newCont\<rparr> t) \<Longrightarrow>
    computeTransaction \<lparr>interval = inte, inputs = []\<rparr> st c =
    TransactionOutput \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newTxOut = \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow> False"
  (* by (metis TransactionOutputRecord.select_convs(3) computeEmptyTransactionWarningIsCounterExample computeTransaction_preserves_validAndPositive_state noCounterExamplePropagatesComputeEmptyTransaction small_lazy'.cases) *)
  oops

lemma staticAnalysisComplete_singleInputTransaction : "(\<And>c st p.
        validAndPositive_state st \<Longrightarrow>
        (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
        hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False) \<Longrightarrow>
    validAndPositive_state st \<Longrightarrow>
    traceListToSingleInput t2 = \<lparr>interval = inte, inputs = [inp]\<rparr> # t \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    hasWarnings (playTraceAux \<lparr>txOutWarnings = newWarns, txOutPayments = p @ newPays, txOutState = newSta, txOutContract = newCont\<rparr> t) \<Longrightarrow>
    computeTransaction \<lparr>interval = inte, inputs = [inp]\<rparr> st c =
    TransactionOutput \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newTxOut = \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow> False"
  (* apply (cases newWarns)
  apply (simp only:refl)
  apply (metis TransactionOutputRecord.select_convs(3) computeTransaction_preserves_validAndPositive_state noCounterExamplePropagatesComputeSingleInputTransaction prod.exhaust)
  apply (simp only:refl)
  by (metis computeSingleInputTransactionWarningIsCounterExample list.distinct(1) prod.exhaust) *)
  oops

lemma staticAnalysisComplete_aux : "validAndPositive_state st \<Longrightarrow>
                                    (\<And> t2 x. \<not> ( isCounterExample (execute (wrapper c t2 (Some st)) x))) \<Longrightarrow> hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False"
  (* apply (simp only:playTraceAuxToSingleInputIsEquivalent[of _ t])
  apply (induction "traceListToSingleInput t" arbitrary: c st p t)
  apply simp
  subgoal for h t t2 c st p
    apply (cases h)
    subgoal for inte inp
      apply (cases inp)
      apply (subst (asm) eq_commute[of "h # t" "traceListToSingleInput t2"])
      apply (simp only:playTraceAux.simps refl)
      apply (cases "computeTransaction h st c")
      subgoal for newTxOut
        apply (cases "newTxOut")
        subgoal for newWarns newPays newSta newCont
          apply (simp del:computeTransaction.simps execute.simps wrapper.simps validAndPositive_state.simps)
          by (metis staticAnalysisComplete_emptyTransaction transactionPrefixForSingleInput)
        done
      apply simp
      subgoal for inp_h inp_t
        apply (cases "inp_t = []")
        apply (subst (asm) eq_commute[of "h # t" "traceListToSingleInput t2"])
        apply (simp only:playTraceAux.simps refl)
        apply (cases "computeTransaction h st c")
        subgoal for newTxOut
          apply (cases "newTxOut")
          subgoal for newWarns newPays newSta newCont
            apply (simp del:computeTransaction.simps execute.simps wrapper.simps validAndPositive_state.simps)
            by (metis staticAnalysisComplete_singleInputTransaction transactionPrefixForSingleInput)
          done
          apply simp
        apply (simp only:refl)
        using traceListToSingleInput_isSingleInput by blast
      done
    done
  done *)
  oops

theorem staticAnalysisComplete : "validAndPositive_state st \<Longrightarrow>
                                  (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                                  , txOutPayments = Nil
                                                                  , txOutState = st
                                                                  , txOutContract = c \<rparr> t)) \<Longrightarrow>
                                  (\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x))"
  (* using staticAnalysisComplete_aux by blast *)
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
