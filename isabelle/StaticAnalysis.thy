theory StaticAnalysis
  imports Semantics MList "HOL-Library.Monad_Syntax" HOL.Wellfounded SingleInputTransactions
begin

(* Symbolic mock definition *)

record SymbolicMonadData = numSymbolicVars :: nat
                           symbolicVarValues :: "int list"

datatype 'a Symbolic = Symbolic "SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option"

primrec execute :: "'a Symbolic \<Rightarrow> SymbolicMonadData \<Rightarrow> ('a \<times> SymbolicMonadData) option" where
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
                     Some x \<Rightarrow> Some (x, st \<lparr> numSymbolicVars := Suc nsv \<rparr> )
                   | None \<Rightarrow> None )"

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

fun isCounterExample :: "(bool \<times> SymbolicMonadData) option \<Rightarrow> bool" where
"isCounterExample None = False" |
"isCounterExample (Some (b, _)) = b"

theorem noCounterExamplePropagatesComputeEmptyTransaction :
   "computeTransaction \<lparr> interval = (lo, hi), inputs = [] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
     (\<And>t x. \<not> isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False"
  oops

theorem noCounterExamplePropagatesComputeSingleInputTransaction :
   "computeTransaction \<lparr> interval = (lo, hi), inputs = [inp] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = [], txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
     (\<And>t x. \<not> isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow> isCounterExample (execute (wrapper newCont t2 (Some newSta)) x2) \<Longrightarrow> False"
  oops

theorem computeEmptyTransactionWarningIsCounterExample :
   "(\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = newWarn, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newWarn = []"
  oops

theorem computeSingleInputTransactionWarningIsCounterExample :
   "(\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    computeTransaction \<lparr> interval = (lo, hi), inputs = [inp] \<rparr> st c = TransactionOutput \<lparr>txOutWarnings = newWarn, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newWarn = []"
  oops

lemma staticAnalysisComplete_emptyTransaction : "(\<And>c st p.
        (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
        hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False) \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    hasWarnings (playTraceAux \<lparr>txOutWarnings = newWarns, txOutPayments = p @ newPays, txOutState = newSta, txOutContract = newCont\<rparr> t) \<Longrightarrow>
    computeTransaction \<lparr>interval = inte, inputs = []\<rparr> st c =
    TransactionOutput \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newTxOut = \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow> False"
  (*
  by (metis computeEmptyTransactionWarningIsCounterExample const.cases noCounterExamplePropagatesComputeEmptyTransaction)
  *)
  oops

lemma staticAnalysisComplete_singleInputTransaction : "(\<And>c st p.
        (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
        hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False) \<Longrightarrow>
    traceListToSingleInput t2 = \<lparr>interval = inte, inputs = [inp]\<rparr> # t \<Longrightarrow>
    (\<And>t2 x. \<not> isCounterExample (execute (wrapper c t2 (Some st)) x)) \<Longrightarrow>
    hasWarnings (playTraceAux \<lparr>txOutWarnings = newWarns, txOutPayments = p @ newPays, txOutState = newSta, txOutContract = newCont\<rparr> t) \<Longrightarrow>
    computeTransaction \<lparr>interval = inte, inputs = [inp]\<rparr> st c =
    TransactionOutput \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow>
    newTxOut = \<lparr>txOutWarnings = newWarns, txOutPayments = newPays, txOutState = newSta, txOutContract = newCont\<rparr> \<Longrightarrow> False"
  (*
  apply (cases newWarns)
  apply (simp only:refl)
  apply (metis noCounterExamplePropagatesComputeSingleInputTransaction small_lazy'.cases)
  apply (simp only:refl)
  by (metis computeSingleInputTransactionWarningIsCounterExample list.distinct(1) prod.exhaust)
  *)
  oops

lemma staticAnalysisComplete_aux : "(\<And> t2 x. \<not> ( isCounterExample (execute (wrapper c t2 (Some st)) x))) \<Longrightarrow> hasWarnings (playTraceAux \<lparr>txOutWarnings = [], txOutPayments = p, txOutState = st, txOutContract = c\<rparr> t) \<Longrightarrow> False"
  (*
  apply (simp only:playTraceAuxToSingleInputIsEquivalent[of _ t])
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
          apply (simp del:computeTransaction.simps execute.simps wrapper.simps)
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
            apply (simp del:computeTransaction.simps execute.simps wrapper.simps)
            by (metis staticAnalysisComplete_singleInputTransaction transactionPrefixForSingleInput)
          done
          apply simp
        apply (simp only:refl)
        using traceListToSingleInput_isSingleInput by blast
      done
    done
  done
  *)
  oops

theorem staticAnalysisComplete : "(\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                                  , txOutPayments = Nil
                                                                  , txOutState = st
                                                                  , txOutContract = c \<rparr> t)) \<Longrightarrow>
                                  (\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x))"
  (* using staticAnalysisComplete_aux by blast *)
  oops

theorem staticAnalysisSound : "(\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x)) \<Longrightarrow>
                               (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                               , txOutPayments = Nil
                                                               , txOutState = st
                                                               , txOutContract = c \<rparr> t))"
  oops

theorem staticAnalysisWorks : "(\<exists> t x. isCounterExample (execute (wrapper c t (Some st)) x)) =
                               (\<exists> t. hasWarnings (playTraceAux \<lparr> txOutWarnings = Nil
                                                               , txOutPayments = Nil
                                                               , txOutState = st
                                                               , txOutContract = c \<rparr> t))"
  (* using staticAnalysisComplete staticAnalysisSound by blast *)
  oops

end
