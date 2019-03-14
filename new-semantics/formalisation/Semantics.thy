theory Semantics
imports Main MList SList "~~/src/HOL/Library/Code_Target_Int"
begin

type_synonym BlockNumber = integer
type_synonym Timeout = BlockNumber
type_synonym Person = integer
type_synonym Choice = integer

type_synonym IdAction = integer
type_synonym IdCommit = integer
type_synonym IdChoice = "integer \<times> Person"
type_synonym IdOracle = integer

type_synonym LetLabel = integer

datatype Value =
    CurrentBlock
  | Committed IdCommit
  | Constant integer
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | DivValue Value Value Value
  | RemValue Value Value Value
  | ValueFromChoice IdChoice Value
  | ValueFromOracle IdOracle Value

datatype Observation =
    BelowTimeout Timeout
  | AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseThis IdChoice Choice
  | ChoseSomething IdChoice
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

datatype Contract =
   Null
 | Commit IdAction IdCommit Person Value Timeout Timeout Contract Contract
 | Pay IdAction IdCommit Person Value Timeout Contract Contract
 | Both Contract Contract
 | Choice Observation Contract Contract
 | When Observation Timeout Contract Contract
 | While Observation Timeout Contract Contract
 | Scale Value Value Value Contract
 | Let LetLabel Contract Contract
 | Use LetLabel

datatype Input =
   IChoice IdChoice Choice
 | IOracle IdOracle BlockNumber integer

datatype AnyInput =
   Action IdAction
 | Input Input

datatype IdInput =
   IdChoice IdChoice
 | IdOracle IdOracle

type_synonym TimeoutData = "(Timeout, (IdCommit slist)) mlist"

record CommitInfo = redeemedPerPerson :: "(Person, integer) mlist"
                    currentCommitsById :: "(IdCommit, (Person \<times> integer \<times> Timeout)) mlist"
                    expiredCommitIds :: "IdCommit slist"
                    timeoutData :: TimeoutData

record State = commits :: CommitInfo
               choices :: "(IdChoice, Choice) mlist"
               oracles :: "(IdOracle, (BlockNumber \<times> integer)) mlist"
               usedIds :: "IdAction slist"

(* Adds a commit identifier to a list of pairs sorted by timeout (ascending) *)
fun addToCommByTim :: "Timeout \<Rightarrow> IdCommit \<Rightarrow> TimeoutData \<Rightarrow> TimeoutData" where
"addToCommByTim timeout idCommit timData =
   (case MList.lookup timeout timData of
     Some commSet \<Rightarrow> MList.update timeout (SList.insert idCommit commSet) timData
   | None \<Rightarrow> timData)"

(* Remove a commit identifier from the timeout data map *)
fun removeFromCommByTim :: "Timeout \<Rightarrow> IdCommit \<Rightarrow> TimeoutData \<Rightarrow> TimeoutData" where
"removeFromCommByTim timeout idCommit timData =
   (case MList.lookup timeout timData of
      Some commSet \<Rightarrow> (let newCommSet = SList.remove idCommit commSet in
                      (if SList.null newCommSet
                       then MList.delete timeout timData
                       else MList.update timeout newCommSet timData))
    | Nothing \<Rightarrow> timData)"

(* Add a commit to CommitInfo *)
fun addCommit :: "IdCommit \<Rightarrow> Person \<Rightarrow> integer \<Rightarrow> Timeout \<Rightarrow> State \<Rightarrow> State" where
"addCommit idCommit person value timeout state =
   (let oldCommits = commits state in
    let commById = currentCommitsById oldCommits in
    let timData = timeoutData oldCommits in
    state\<lparr> commits :=
        oldCommits\<lparr> currentCommitsById := MList.update idCommit (person, value, timeout) commById
                  , timeoutData := addToCommByTim timeout idCommit timData  \<rparr> \<rparr>)"

(* Return the person corresponding to a commit *)
fun personForCurrentCommit :: "IdCommit \<Rightarrow> State \<Rightarrow> Person option" where
"personForCurrentCommit idCommit state =
   (case MList.lookup idCommit (currentCommitsById (commits state)) of
      Some (person, _, _) \<Rightarrow> Some person
    | None \<Rightarrow> None)"

(* Check whether the commit is current (committed not expired) *)
fun isCurrentCommit :: "IdCommit \<Rightarrow> State \<Rightarrow> bool" where
"isCurrentCommit idCommit state =
   (case MList.lookup idCommit (currentCommitsById (commits state)) of
      Some _ \<Rightarrow> True
    | None \<Rightarrow> False)"

(* Check whether the commit is expired *)
fun isExpiredCommit :: "IdCommit \<Rightarrow> State \<Rightarrow> bool" where
"isExpiredCommit idCommit state = SList.member idCommit (expiredCommitIds (commits state))"

(* Remove a current commit from CommitInfo *)
fun removeCurrentCommit :: "IdCommit \<Rightarrow> State \<Rightarrow> State" where
"removeCurrentCommit idCommit state =
   (let oldCommits = commits state in
    let commById = currentCommitsById oldCommits in
    let timData = timeoutData oldCommits in
    case MList.lookup idCommit commById of
       Some (_, _, timeout) \<Rightarrow>
        state\<lparr> commits :=
          oldCommits\<lparr> currentCommitsById := MList.delete idCommit commById
                    , timeoutData := removeFromCommByTim timeout idCommit timData \<rparr>\<rparr>
      | None \<Rightarrow> state)"

fun getRedeemedForPersonCI :: "Person \<Rightarrow> CommitInfo \<Rightarrow> integer" where
"getRedeemedForPersonCI person ci =
   (case MList.lookup person (redeemedPerPerson ci) of
     None \<Rightarrow> 0
   | Some value \<Rightarrow> value)"

fun getRedeemedForPerson :: "Person \<Rightarrow> State \<Rightarrow> integer" where
"getRedeemedForPerson person state = getRedeemedForPersonCI person (commits state)"

(* Set the amount in expiredNotCollected to zero *)
fun resetRedeemedForPerson :: "Person \<Rightarrow> State \<Rightarrow> State" where
"resetRedeemedForPerson person state =
   (let oldCommits = commits state in
    let redeemedPerPersonMap = redeemedPerPerson oldCommits in
    state\<lparr> commits :=
      oldCommits\<lparr> redeemedPerPerson := MList.delete person redeemedPerPersonMap \<rparr> \<rparr>)"

fun discountAvailableMoneyFromCommit :: "IdCommit \<Rightarrow> integer \<Rightarrow> State \<Rightarrow> State option" where
"discountAvailableMoneyFromCommit idCommit discount state =
   (let oldCommits = commits state in
    let commById = currentCommitsById oldCommits in
    case MList.lookup idCommit commById of
      Some (person, value, timeout) \<Rightarrow>
        Some (state\<lparr>commits :=
                oldCommits\<lparr>
                  currentCommitsById := MList.update idCommit (person, value - discount, timeout) commById \<rparr>\<rparr>))"

fun getAvailableAmountInCommit :: "IdCommit \<Rightarrow> State \<Rightarrow> integer" where
"getAvailableAmountInCommit idCommit state =
   (case MList.lookup idCommit (currentCommitsById (commits state)) of
      Some (_, value, _) \<Rightarrow> value
    | None \<Rightarrow> 0)"

definition slist_union :: "'a slist \<Rightarrow> 'a slist \<Rightarrow> 'a slist" where
"slist_union = SList.fold SList.insert"

definition slist_unions :: "('a slist) list \<Rightarrow> 'a slist" where
"slist_unions slistlist = List.fold slist_union slistlist SList.empty"

(* Collect inputs needed by a contract *)
fun collectNeededInputsFromValue :: "Value \<Rightarrow> IdInput slist" where
"collectNeededInputsFromValue CurrentBlock = SList.empty" |
"collectNeededInputsFromValue (Committed _) = SList.empty" |
"collectNeededInputsFromValue (Constant _) = SList.empty" |
"collectNeededInputsFromValue (NegValue value) = collectNeededInputsFromValue value" |
"collectNeededInputsFromValue (AddValue value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromValue (SubValue value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromValue (MulValue value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromValue (DivValue value1 value2 value3) =
  slist_unions [collectNeededInputsFromValue value1
               ,collectNeededInputsFromValue value2
               ,collectNeededInputsFromValue value3]" |
"collectNeededInputsFromValue (RemValue value1 value2 value3) =
  slist_unions [collectNeededInputsFromValue value1
               ,collectNeededInputsFromValue value2
               ,collectNeededInputsFromValue value3]" |
"collectNeededInputsFromValue (ValueFromChoice idChoice value) =
  SList.insert (IdChoice idChoice) (collectNeededInputsFromValue value)" |
"collectNeededInputsFromValue (ValueFromOracle idOracle value) =
  SList.insert (IdOracle idOracle) (collectNeededInputsFromValue value)"

fun collectNeededInputsFromObservation :: "Observation \<Rightarrow> IdInput slist" where
"collectNeededInputsFromObservation (BelowTimeout _) = SList.empty" |
"collectNeededInputsFromObservation (AndObs obs1 obs2) =
  slist_union (collectNeededInputsFromObservation obs1)
              (collectNeededInputsFromObservation obs2)" |
"collectNeededInputsFromObservation (OrObs obs1 obs2) =
  slist_union (collectNeededInputsFromObservation obs1)
              (collectNeededInputsFromObservation obs2)" |
"collectNeededInputsFromObservation (NotObs obs) =
  collectNeededInputsFromObservation obs" |
"collectNeededInputsFromObservation (ChoseThis idChoice _) =
  SList.insert (IdChoice idChoice)  SList.empty" |
"collectNeededInputsFromObservation (ChoseSomething idChoice) =
  SList.insert (IdChoice idChoice)  SList.empty" |
"collectNeededInputsFromObservation (ValueGE value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromObservation (ValueGT value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromObservation (ValueLT value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromObservation (ValueLE value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromObservation (ValueEQ value1 value2) =
  slist_union (collectNeededInputsFromValue value1)
              (collectNeededInputsFromValue value2)" |
"collectNeededInputsFromObservation TrueObs = SList.empty" |
"collectNeededInputsFromObservation FalseObs = SList.empty"

fun collectNeededInputsFromContract :: "Contract \<Rightarrow> IdInput slist" where
"collectNeededInputsFromContract Null = SList.empty" |
"collectNeededInputsFromContract (Commit _ _ _ value _ _ contract1 contract2) =
  slist_unions [collectNeededInputsFromValue value
               ,collectNeededInputsFromContract contract1
               ,collectNeededInputsFromContract contract2]" |
"collectNeededInputsFromContract (Pay _ _ _ value _ contract1 contract2) =
  slist_unions [collectNeededInputsFromValue value
               ,collectNeededInputsFromContract contract1
               ,collectNeededInputsFromContract contract2]" |
"collectNeededInputsFromContract (Both contract1 contract2) =
  slist_union (collectNeededInputsFromContract contract1)
              (collectNeededInputsFromContract contract2)" |
"collectNeededInputsFromContract (Choice observation contract1 contract2) =
  slist_unions [collectNeededInputsFromObservation observation
               ,collectNeededInputsFromContract contract1
               ,collectNeededInputsFromContract contract2]" |
"collectNeededInputsFromContract (When observation _ contract1 contract2) =
  slist_unions [collectNeededInputsFromObservation observation
               ,collectNeededInputsFromContract contract1
               ,collectNeededInputsFromContract contract2]" |
"collectNeededInputsFromContract (While observation _ contract1 contract2) =
  slist_unions [collectNeededInputsFromObservation observation
               ,collectNeededInputsFromContract contract1
               ,collectNeededInputsFromContract contract2]" |
"collectNeededInputsFromContract (Scale value1 value2 value3 contract) =
  slist_unions [collectNeededInputsFromValue value1
               ,collectNeededInputsFromValue value2
               ,collectNeededInputsFromValue value3
               ,collectNeededInputsFromContract contract]" |
"collectNeededInputsFromContract (Contract.Let _ contract1 contract2) =
  slist_union (collectNeededInputsFromContract contract1)
              (collectNeededInputsFromContract contract2)" |
"collectNeededInputsFromContract (Use _) = SList.empty"

(* Add inputs and action ids to state *)
(* Return None on redundant or irrelevant inputs *)
fun addAnyInput :: "BlockNumber \<Rightarrow> AnyInput \<Rightarrow> IdInput slist \<Rightarrow> State \<Rightarrow> State option" where
"addAnyInput _ (Action idInput) _ state =
  (let usedIdsSet = usedIds state in
   if SList.member idInput usedIdsSet
   then None
   else Some (state\<lparr> usedIds := SList.insert idInput usedIdsSet \<rparr>))" |
"addAnyInput _ (Input (IChoice idChoice choiceVal)) neededInputs state =
  (let choiceMap = choices state in
   case MList.lookup idChoice choiceMap of
     None \<Rightarrow> None
   | Some _ \<Rightarrow> if SList.member (IdChoice idChoice) neededInputs
               then Some (state\<lparr> choices := MList.update idChoice choiceVal choiceMap \<rparr>)
               else None)" |
"addAnyInput blockNumber (Input (IOracle idOracle timestamp value)) neededInputs state =
  (let oracleMap = oracles state in
   let newState = state\<lparr> oracles := MList.update idOracle (timestamp, value) oracleMap \<rparr> in
   case MList.lookup idOracle oracleMap of
     Some (lastTimestamp, _) \<Rightarrow>
      (if ((timestamp > lastTimestamp) \<and> (timestamp \<le> blockNumber) \<and>
           (SList.member (IdOracle idOracle) neededInputs))
       then Some newState
       else None)
   | None \<Rightarrow> Some newState)"

(* Decide whether something has expired *)
fun isExpired :: "BlockNumber \<Rightarrow> BlockNumber \<Rightarrow> bool" where
"isExpired currBlockNum expirationBlockNum = (currBlockNum \<ge> expirationBlockNum)"

definition timeoutDataMeasure :: "CommitInfo \<Rightarrow> nat" where
"timeoutDataMeasure ci = MList.size (timeoutData ci)"

(* Expire commits *)
fun expireOneCommit :: "IdCommit \<Rightarrow> CommitInfo \<Rightarrow> CommitInfo" where
"expireOneCommit idCommit commitInfo =
  (let redPerPer = redeemedPerPerson commitInfo in
   let currentCommits = currentCommitsById commitInfo in
   case MList.lookup idCommit currentCommits of
     Some (person, value, _) \<Rightarrow>
       let redeemedBefore = MList.lookup_default 0 person redPerPer in
        commitInfo\<lparr> redeemedPerPerson := MList.update person (redeemedBefore + value) MList.empty
                  , currentCommitsById := MList.delete idCommit currentCommits \<rparr>
   | None \<Rightarrow> commitInfo)"

lemma expireOneCommitDoesntAffectTimeoutData :
   "expireOneCommit x y = z \<Longrightarrow> timeoutData y = timeoutData z"
  apply (cases "lookup x (currentCommitsById y)")
  by auto

lemma expireOneCommitDoesntAffectTimeoutDataMeasure :
   "expireOneCommit x y = z \<Longrightarrow> timeoutDataMeasure y = timeoutDataMeasure z"
  using expireOneCommitDoesntAffectTimeoutData timeoutDataMeasure_def by fastforce

fun expireManyCommits :: "IdCommit slist \<Rightarrow> CommitInfo \<Rightarrow> CommitInfo" where
"expireManyCommits commitIds commitInfo =
   (let expiComms = expiredCommitIds commitInfo in
    let semiUpdatedCI = commitInfo\<lparr> expiredCommitIds := slist_union expiComms commitIds \<rparr> in
    SList.fold expireOneCommit commitIds semiUpdatedCI)"

lemma foldExpireOneCommitDoesntAffectTimeoutDataMeasure_aux :
 "z = SList.fold expireOneCommit x y \<Longrightarrow> timeoutDataMeasure y = timeoutDataMeasure b
   \<Longrightarrow> timeoutDataMeasure y = timeoutDataMeasure (expireOneCommit a b)"
  using expireOneCommitDoesntAffectTimeoutDataMeasure by presburger

lemma foldExpireOneCommitDoesntAffectTimeoutDataMeasure :
   "SList.fold expireOneCommit x y = z \<Longrightarrow> timeoutDataMeasure y = timeoutDataMeasure z"
  apply auto
  apply (rule SList.slist_fold_invariant [of "\<lambda> x. timeoutDataMeasure y = timeoutDataMeasure x" "expireOneCommit"])
  using expireOneCommitDoesntAffectTimeoutDataMeasure apply presburger
  by blast

lemma expireManyCommitsDoesntAffectTimeoutDataMeasure :
   "expireManyCommits x y = z \<Longrightarrow> timeoutDataMeasure y = timeoutDataMeasure z"
  using foldExpireOneCommitDoesntAffectTimeoutDataMeasure timeoutDataMeasure_def by fastforce  

lemma expireCommitsCI_progress:
"x = timeoutData commitInfo \<Longrightarrow>
 lookup x2 x = Some x2a \<Longrightarrow>
 xa = delete x2 x \<Longrightarrow>
 xb = commitInfo\<lparr>timeoutData := xa\<rparr> \<Longrightarrow>
 xc = expireManyCommits x2a xb \<Longrightarrow>
 timeoutDataMeasure xc < timeoutDataMeasure commitInfo"
 by (metis CommitInfo.select_convs(4) CommitInfo.surjective CommitInfo.update_convs(4)
     expireManyCommitsDoesntAffectTimeoutDataMeasure MList.sizeDeleteOrder timeoutDataMeasure_def)

function expireCommitsCI :: "BlockNumber \<Rightarrow> CommitInfo \<Rightarrow> CommitInfo" where
"expireCommitsCI blockNumber commitInfo =
   (let timData = timeoutData commitInfo in
    (case MList.get_min_key timData of
      Some minBlock \<Rightarrow>
        (case MList.lookup minBlock timData of
           Some commIds \<Rightarrow> let remTimData = MList.delete minBlock timData in
             if (isExpired blockNumber minBlock)
             then (let partUpdatedCommitInfo = commitInfo\<lparr>timeoutData := remTimData\<rparr> in
                   let updateCommitInfo = expireManyCommits commIds partUpdatedCommitInfo in
                   expireCommitsCI blockNumber updateCommitInfo)
             else commitInfo
         | None \<Rightarrow> commitInfo
        )
     | None \<Rightarrow> commitInfo))"
  by auto
termination expireCommitsCI
  apply (relation "measure (\<lambda>(_,ci). timeoutDataMeasure ci)")
  apply blast
  by (simp add: expireCommitsCI_progress)

fun expireCommits :: "BlockNumber \<Rightarrow> State \<Rightarrow> State" where
"expireCommits blockNumber state =
  (let commitInfo = commits state in
   state\<lparr> commits := expireCommitsCI blockNumber commitInfo \<rparr>)"

(* Evaluate a value *)
fun evalValue :: "BlockNumber \<Rightarrow> State \<Rightarrow> Value \<Rightarrow> integer" where
"evalValue blockNumber _ CurrentBlock = blockNumber" |
"evalValue _ state (Committed idCommit) = getAvailableAmountInCommit idCommit state" |
"evalValue _ _ (Constant value) = value" |
"evalValue blockNumber state (NegValue value) =
  - (evalValue blockNumber state value)" |
"evalValue blockNumber state (AddValue lhs rhs) =
  (evalValue blockNumber state lhs) + (evalValue blockNumber state rhs)" |
"evalValue blockNumber state (SubValue lhs rhs) =
  (evalValue blockNumber state lhs) - (evalValue blockNumber state rhs)" |
"evalValue blockNumber state (MulValue lhs rhs) =
  (evalValue blockNumber state lhs) * (evalValue blockNumber state rhs)" |
"evalValue blockNumber state (DivValue dividend divisor defaultVal) =
  (let actualDivisor = evalValue blockNumber state divisor in
   if (actualDivisor = 0)
   then evalValue blockNumber state defaultVal
   else (evalValue blockNumber state dividend) div (evalValue blockNumber state divisor))" |
"evalValue blockNumber state (RemValue dividend divisor defaultVal) =
  (let actualDivisor = evalValue blockNumber state divisor in
   if (actualDivisor = 0)
   then evalValue blockNumber state defaultVal
   else (evalValue blockNumber state dividend) mod (evalValue blockNumber state divisor))" |
"evalValue blockNumber state (ValueFromChoice idChoice val) =
  (case MList.lookup idChoice (choices state) of
     Some choiceValue \<Rightarrow> choiceValue
   | None \<Rightarrow> evalValue blockNumber state val)" |
"evalValue blockNumber state (ValueFromOracle idOracle val) =
  (case MList.lookup idOracle (oracles state) of
     Some (_, oracleValue) \<Rightarrow> oracleValue
   | None \<Rightarrow> evalValue blockNumber state val)"

fun evalObservation :: "BlockNumber \<Rightarrow> State \<Rightarrow> Observation \<Rightarrow> bool" where
"evalObservation blockNumber _ (BelowTimeout timeout) =
   (\<not> isExpired blockNumber timeout)" |
"evalObservation blockNumber state (AndObs obs1 obs2) =
   ((evalObservation blockNumber state obs1) \<and>
    (evalObservation blockNumber state obs2))" |
"evalObservation blockNumber state (OrObs obs1 obs2) =
   ((evalObservation blockNumber state obs1) \<and>
    (evalObservation blockNumber state obs2))" |
"evalObservation blockNumber state (NotObs obs) =
   evalObservation blockNumber state obs" |
"evalObservation _ state (ChoseThis idChoice choice) = undefined" |
"evalObservation _ state (ChoseSomething idChoice) = undefined" |
"evalObservation blockNumber state (ValueGE val1 val2) =
   ((evalValue blockNumber state val1) \<ge> (evalValue blockNumber state val2))" |
"evalObservation blockNumber state (ValueGT val1 val2) =
   ((evalValue blockNumber state val1) > (evalValue blockNumber state val2))" |
"evalObservation blockNumber state (ValueLT val1 val2) =
   ((evalValue blockNumber state val1) < (evalValue blockNumber state val2))" |
"evalObservation blockNumber state (ValueLE val1 val2) =
   ((evalValue blockNumber state val1) \<le> (evalValue blockNumber state val2))" |
"evalObservation blockNumber state (ValueEQ val1 val2) =
   ((evalValue blockNumber state val1) = (evalValue blockNumber state val2))" |
"evalObservation _ _ TrueObs = True" |
"evalObservation _ _ FalseObs = False"

(* Check whether a fraction equals 1 *)
fun isNormalised :: "integer \<Rightarrow> integer \<Rightarrow> bool" where
"isNormalised divid divis = (divid = divis \<and> divid \<noteq> 0)"

type_synonym Environment = "(LetLabel, Contract) mlist"

definition emptyEnvironment :: Environment where
"emptyEnvironment = MList.empty"

definition addToEnvironment :: "LetLabel \<Rightarrow> Contract \<Rightarrow> Environment \<Rightarrow> Environment" where
"addToEnvironment = MList.update"

definition lookupEnvironment :: "LetLabel \<Rightarrow> Environment \<Rightarrow> Contract option" where
"lookupEnvironment = MList.lookup"

definition deleteFromEnvironment :: "LetLabel \<Rightarrow> Environment \<Rightarrow> Environment" where
"deleteFromEnvironment = MList.delete_until"

fun maxIdFromContract :: "Contract \<Rightarrow> integer" where
"maxIdFromContract Null = 0"|
"maxIdFromContract (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (Pay idAction idCommit person value timeout contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (Both contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (Choice observation contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (When observation timeout contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (While observation timeout contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (Scale value1 value2 value3 contract) =
  (maxIdFromContract contract)" |
"maxIdFromContract (Let letLabel contract1 contract2) =
  max letLabel (max (maxIdFromContract contract1) (maxIdFromContract contract2))" |
"maxIdFromContract (Use letLabel) =
  letLabel"

fun getFreshLabel :: "(LetLabel, Contract) mlist \<Rightarrow> Contract \<Rightarrow> LetLabel" where
"getFreshLabel env c =
  1 + max (max (MList.fold_with_key (\<lambda> (_, v) acc . max (maxIdFromContract v) acc) 0 env)
               (case MList.get_max_key env of
                    None \<Rightarrow> 0
                  | Some mkey \<Rightarrow> max 0 mkey))
          (maxIdFromContract c)"

fun nullifyInvalidUses :: "Environment \<Rightarrow> Contract \<Rightarrow> Contract" where
"nullifyInvalidUses _ Null = Null" |
"nullifyInvalidUses env (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  Commit idAction idCommit person value timeout1 timeout2 (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (Pay idAction idCommit person value timeout contract1 contract2) =
  Pay idAction idCommit person value timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (Both contract1 contract2) =
  Both (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (Choice observation contract1 contract2) =
  Choice observation (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (When observation timeout contract1 contract2) =
  When observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (While observation timeout contract1 contract2) =
  While observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)" |
"nullifyInvalidUses env (Scale value1 value2 value3 contract) =
  Scale value1 value2 value3 (nullifyInvalidUses env contract)" |
"nullifyInvalidUses env (Let letLabel contract1 contract2) =
  (let newEnv = addToEnvironment letLabel Null env in
   Let letLabel (nullifyInvalidUses env contract1) (nullifyInvalidUses newEnv contract2))" |
"nullifyInvalidUses env (Use letLabel) =
  (case lookupEnvironment letLabel env of
     None \<Rightarrow> Null
   | Some _ \<Rightarrow> Use letLabel)"

fun relabel :: "LetLabel \<Rightarrow> LetLabel \<Rightarrow> Contract \<Rightarrow> Contract" where
"relabel _ _ Null = Null" |
"relabel startLabel endLabel (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  Commit idAction idCommit person value timeout1 timeout2 (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (Pay idAction idCommit person value timeout contract1 contract2) =
  Pay idAction idCommit person value timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (Both contract1 contract2) =
  Both (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (Choice observation contract1 contract2) =
  Choice observation (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (When observation timeout contract1 contract2) =
  When observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (While observation timeout contract1 contract2) =
  While observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (Scale value1 value2 value3 contract) =
  Scale value1 value2 value3 (relabel startLabel endLabel contract)" |
"relabel startLabel endLabel (Let letLabel contract1 contract2) =
  Let letLabel (relabel startLabel endLabel contract1)
      (if letLabel = startLabel
       then contract2
       else relabel startLabel endLabel contract2)" |
"relabel startLabel endLabel (Use letLabel) =
   (if letLabel = startLabel then Use endLabel else Use letLabel)"

function reduceRec :: "BlockNumber \<Rightarrow> State \<Rightarrow> Environment \<Rightarrow> Contract \<Rightarrow> Contract" where
"reduceRec _ _ _ Null = Null" |
"reduceRec blockNum state env (Commit id1 id2 per val timeout_start timeout_end nc continuation) =
  (if (isExpired blockNum timeout_start) \<or> (isExpired blockNum timeout_end)
   then reduceRec blockNum state env continuation
   else (Commit id1 id2 per val timeout_start timeout_end nc continuation))" |
"reduceRec blockNum state env (Pay id1 id2 per val timeout nc continuation) =
  (if isExpired blockNum timeout
   then reduceRec blockNum state env continuation
   else (Pay id1 id2 per val timeout nc continuation))" |
"reduceRec blockNum state env (Both cont1 cont2) =
  Both (reduceRec blockNum state env cont1) (reduceRec blockNum state env cont2)" |
"reduceRec blockNum state env (Choice obs cont1 cont2) =
  reduceRec blockNum state env (if (evalObservation blockNum state obs)
                                then cont1
                                else cont2)" |
"reduceRec blockNum state env (When obs timeout cont1 cont2) =
  (if isExpired timeout blockNum
   then reduceRec blockNum state env cont2
   else (if evalObservation blockNum state obs
         then reduceRec blockNum state env cont1
         else (When obs timeout cont1 cont2)))" |
"reduceRec blockNum state env (Scale divid divis def contract) =
  Scale (Constant (evalValue blockNum state divid))
        (Constant (evalValue blockNum state divis))
        (Constant (evalValue blockNum state def))
        (reduceRec blockNum state env contract)" |
"reduceRec blockNum state env (While obs timeout contractWhile contractAfter) =
  (if isExpired timeout blockNum
   then reduceRec blockNum state env contractAfter
   else (if evalObservation blockNum state obs
         then (While obs timeout (reduceRec blockNum state env contractWhile) contractAfter)
         else reduceRec blockNum state env contractAfter))" |
"reduceRec blockNum state env (Let label boundContract contract) =
 (let checkedBoundContract = nullifyInvalidUses env boundContract in
  case lookupEnvironment label env of
    None \<Rightarrow> let newEnv = addToEnvironment label checkedBoundContract env in
            Let label checkedBoundContract (reduceRec blockNum state newEnv contract) 
  | Some _ \<Rightarrow> let freshLabel = getFreshLabel env contract in
              let newEnv = addToEnvironment freshLabel checkedBoundContract env in
              let fixedContract = relabel label freshLabel contract in
              Let freshLabel checkedBoundContract (reduceRec blockNum state newEnv fixedContract))" |
"reduceRec blockNum state env (Use label) =
  (case lookupEnvironment label env of
     Some contract \<Rightarrow> reduceRec blockNum state (deleteFromEnvironment label env) contract
   | None \<Rightarrow> Null)"
  apply auto
  by (metis Contract.exhaust)

fun contractDepth :: "(LetLabel, nat) mlist \<Rightarrow> Contract \<Rightarrow> nat" where
"contractDepth _ Null = 1" |
"contractDepth env (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (Pay idAction idCommit person value timeout contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (Both contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (Choice observation contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (When observation timeout contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (While observation timeout contract1 contract2) =
  1 + (max (contractDepth env contract1) (contractDepth env contract2))" |
"contractDepth env (Scale value1 value2 value3 contract) =
  1 + (contractDepth env contract)" |
"contractDepth env (Let letLabel contract1 contract2) =
  (let boundContractDepth = contractDepth env contract1 in
  1 + (contractDepth (MList.update letLabel boundContractDepth env) contract2))" |
"contractDepth env (Use letLabel) =
  1 + (case MList.lookup letLabel env of
         None \<Rightarrow> 0
       | Some x \<Rightarrow> x)"

fun envToContractDepthEnv :: "Environment \<Rightarrow> (LetLabel, nat) mlist" where
"envToContractDepthEnv env =
   MList.reverse_fold_with_key
       (\<lambda> (l, c) e . MList.update l (contractDepth e c) e)
       MList.empty
       env"

lemma smallEnvironmentUpdate : "x1 \<le> x2 \<Longrightarrow>
    (\<And> x . MList.lookup_default 0 x env1 \<le> MList.lookup_default 0 x env2) \<Longrightarrow>
      MList.lookup_default 0 x (update y x1 env1)
    \<le> MList.lookup_default 0 x (update y x2 env2)"
  apply (cases "x = y")
  apply (simp add: lookup_default_after_update)
  by (simp add: lookup_default_after_update2)

lemma smallerEnvironment_aux : "(\<And>x. lookup_default 0 x env1 \<le> lookup_default 0 x env2) \<Longrightarrow>
       (case lookup x env1 of None \<Rightarrow> 0 | Some x \<Rightarrow> x) \<le> (case lookup x env2 of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"
  apply (cases "lookup x env1")
  apply (cases "lookup x env2")
  apply simp
  apply (metis lookup_and_default_None)
  apply (metis lookup_and_default_None lookup_and_default_Some option.simps(4) option.simps(5))
  apply (cases "lookup x env2")
  apply simp
  apply (metis lookup_and_default_None lookup_and_default_Some)
  by (metis lookup_and_default_Some option.simps(5))

lemma smallerEnvironment : "(\<And> x . MList.lookup_default 0 x env1 \<le> MList.lookup_default 0 x env2)
                            \<Longrightarrow> contractDepth env1 contract \<le> contractDepth env2 contract"
  apply (induction contract arbitrary:env1 env2)
  apply (auto simp: max.coboundedI1 max.coboundedI2)
  apply (simp add: smallEnvironmentUpdate)
  by (simp add: smallerEnvironment_aux)

lemma envToContractDepthEnvKeepsLastUpdate : "lookup_default z x (envToContractDepthEnv (MList ((x, contract)#xa)))
                                              = contractDepth (envToContractDepthEnv (MList xa)) contract"
  by (simp del:reverse_fold_with_key.simps add:reverse_fold_last_step add:lookup_default_after_update)

fun isDepthSmallerOrEqual :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"isDepthSmallerOrEqual None None = True" |
"isDepthSmallerOrEqual None (Some _) = True" |
"isDepthSmallerOrEqual (Some _) None = False" |
"isDepthSmallerOrEqual (Some a) (Some b) = (a \<le> b)"

lemma stillSubMapAfterUpdate : "(\<And>x. isDepthSmallerOrEqual (MList.lookup x e) (MList.lookup x g)) \<Longrightarrow>
        isDepthSmallerOrEqual (MList.lookup x (update x1 z e)) (MList.lookup x (update x1 z g))"
  by (metis isDepthSmallerOrEqual.simps(1) isDepthSmallerOrEqual.simps(4) lookup_after_update lookup_after_update2 not_None_eq order_refl)

lemma etcdeSmallerWithMissingElements :  "(\<And> x. isDepthSmallerOrEqual (MList.lookup x e) (MList.lookup x g)) \<Longrightarrow> contractDepth e c \<le> contractDepth g c"
  apply (induction c arbitrary: e g)
  apply (auto simp: max.coboundedI1 max.coboundedI2)
  apply (metis isDepthSmallerOrEqual.simps(4) lookup_after_update2 lookup_after_update3)
  by (metis isDepthSmallerOrEqual.elims(2) le0 option.case_eq_if option.distinct(1) option.sel)

lemma etcdeSmallerWithMissingElement2_aux : "(\<And>x. isDepthSmallerOrEqual (lookup x (MList (delete_aux y xa))) (lookup x (MList xa))) \<Longrightarrow>
                                                  isDepthSmallerOrEqual (lookup x (MList (delete_aux y ((aa, ab) # xa)))) (lookup x (MList ((aa, ab) # xa)))"
  apply (cases "x = aa")
  apply (metis delete_aux.simps(2) eq_iff isDepthSmallerOrEqual.elims(3) lookup.simps(2) not_member_of_delete_aux option.distinct(1) option.inject successLookupImpliesMember)
  by auto

lemma etcdeSmallerWithMissingElements2 : "(\<And> x. isDepthSmallerOrEqual (MList.lookup x (MList (delete_aux y xa))) (MList.lookup x (MList xa)))"
  apply (induction xa)
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (metis etcdeSmallerWithMissingElement2_aux surj_pair)

lemma depthSOEWhenEqual : "(\<And> x. isDepthSmallerOrEqual (MList.lookup x e) (MList.lookup x e))"
  by (metis (full_types) isDepthSmallerOrEqual.simps(1) isDepthSmallerOrEqual.simps(4) option.exhaust order_refl)

lemma lookupDeleteNone_aux : "lookup y (envToContractDepthEnv (MList (delete_aux y xa))) = None \<Longrightarrow>
                              lookup y (envToContractDepthEnv (MList (delete_aux y ((aa, ab) # xa)))) = None"
  apply (cases "y = aa")
  apply auto[1]
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (simp add: lookup_after_update2)

lemma lookupDeleteNone : "MList.lookup y (envToContractDepthEnv (MList (delete_aux y xa))) = None"
  apply (induction xa)
  apply (simp add: nothingComesFromNothing)
  using lookupDeleteNone_aux by auto

lemma contractDepthWithSmallerEnv : "(\<And> a . isDepthSmallerOrEqual (lookup a x) (lookup a y)) \<Longrightarrow> (contractDepth x ab) \<le> (contractDepth y ab)"
  by (simp add: etcdeSmallerWithMissingElements)

lemma isDepthSmallerOrEqualSmallerUpdate : "(\<And> x . isDepthSmallerOrEqual (lookup x h) (lookup x i)) \<Longrightarrow>
                                            y \<le> z \<Longrightarrow>
                                            isDepthSmallerOrEqual (lookup x (update aa y h)) (lookup x (update aa z i))"
  apply (cases "x = aa")
  apply (simp add: lookup_after_update3)
  by (simp add: lookup_after_update2)

lemma deleteSmallerEnvironment2_aux : "isDepthSmallerOrEqual (lookup x (envToContractDepthEnv (MList (delete_aux y xa))))
                                                             (lookup x (envToContractDepthEnv (MList xa))) \<Longrightarrow>
                                       isDepthSmallerOrEqual (MList.lookup x (envToContractDepthEnv (MList (delete_aux y xa))))
                                                             (MList.lookup x (envToContractDepthEnv (MList ((y, ab) # xa))))"
  apply (cases "x = y")
  using isDepthSmallerOrEqual.elims(3) lookupDeleteNone apply auto[1]
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (simp add: lookup_after_update2)

lemma deleteSmallerEnvironment2_aux2 :
      " (\<And>x. isDepthSmallerOrEqual (lookup x (envToContractDepthEnv (MList (delete_aux y xa)))) (lookup x (envToContractDepthEnv (MList xa)))) \<Longrightarrow>
       isDepthSmallerOrEqual (lookup x (envToContractDepthEnv (MList (delete_aux y ((aa, ab) # xa))))) (lookup x (envToContractDepthEnv (MList ((aa, ab) # xa))))"
  apply (cases "y = aa")
  using deleteSmallerEnvironment2_aux apply auto[1]
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (simp add: etcdeSmallerWithMissingElements isDepthSmallerOrEqualSmallerUpdate)

lemma deleteSmallerEnvironment2 : "isDepthSmallerOrEqual (MList.lookup x (envToContractDepthEnv (MList (delete_aux y xa))))
                                                        (MList.lookup x (envToContractDepthEnv (MList xa)))"
  apply (induction xa arbitrary: x)
  apply (simp add: depthSOEWhenEqual)
  using deleteSmallerEnvironment2_aux2 by auto

lemma deleteSmallerEnvironment : "MList.lookup_default 0 x (envToContractDepthEnv (MList (delete_aux y xa)))
                                \<le> MList.lookup_default 0 x (envToContractDepthEnv (MList xa))"
  by (smt deleteSmallerEnvironment2 isDepthSmallerOrEqual.simps(3) isDepthSmallerOrEqual.simps(4) le0 lookup_and_default_None lookup_and_default_Some option.exhaust)

lemma addSameToEnvLE_aux : "lookup_default 0 x (envToContractDepthEnv (update x contract (MList xa))) \<le> contractDepth (envToContractDepthEnv (MList xa)) contract"
  using deleteSmallerEnvironment envToContractDepthEnvKeepsLastUpdate smallerEnvironment by auto

lemma addSameToEnvLE_aux2 : "lookup_default 0 x (envToContractDepthEnv (update x contract env)) \<le> contractDepth (envToContractDepthEnv env) contract"
  apply (cases env)
  by (metis addSameToEnvLE_aux)

lemma addSameToEnvLE_aux3 : "lookupEnvironment label (MList xa) = None \<Longrightarrow> label \<noteq> x \<Longrightarrow>
          lookup_default 0 x (envToContractDepthEnv (addToEnvironment label contract (MList xa)))
        \<le> lookup_default 0 x (update label (contractDepth (envToContractDepthEnv env) contract) (envToContractDepthEnv (MList xa)))"
  apply (induction xa)
  apply (simp add:addToEnvironment_def)
  apply (simp add:lookup_default_after_update2)
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (smt deleteSmallerEnvironment envToContractDepthEnv.simps lookup_default_after_update2 reverse_fold_last_step)

lemma addSameToEnvLE_aux4 : "lookupEnvironment label env = None \<Longrightarrow>
         lookup_default 0 x (envToContractDepthEnv (addToEnvironment label contract env))
         \<le> lookup_default 0 x (update label (contractDepth (envToContractDepthEnv env) contract) (envToContractDepthEnv env))"
  apply (cases "label = x")
  apply (metis addSameToEnvLE_aux2 addToEnvironment_def lookup_default_after_update)
  by (metis (full_types) addSameToEnvLE_aux3 mlist.exhaust)

lemma smallEnvironmentUpdate2 : "y1 \<le> (y2 :: nat) \<Longrightarrow> MList.lookup_default 0 z (update x y1 env) \<le> MList.lookup_default 0 z (update x y2 env)"
  by (simp add: smallEnvironmentUpdate)

lemma nullifySmallerEnv : "contractDepth env1 (nullifyInvalidUses env2 contract) \<le> contractDepth env1 contract"
  apply (induction contract arbitrary:env1 env2)
  apply simp
  using max.mono apply fastforce
  using max.mono apply fastforce
  using max.mono apply fastforce
  using max.mono apply fastforce
  using max.mono apply fastforce
  using max.mono apply fastforce
  using max.mono apply fastforce
  apply (simp add:dual_order.trans plus_1_eq_Suc smallEnvironmentUpdate smallerEnvironment)
  apply (metis max.strict_coboundedI2 max_absorb1 not_less smallEnvironmentUpdate2 smallerEnvironment)
  by (simp add: option.case_eq_if)

lemma smallerEnvLookupDef_aux : "lookupEnvironment label (MList xa) = None \<Longrightarrow>
          contractDepth (envToContractDepthEnv (MList xa)) x \<le> contractDepth (envToContractDepthEnv (MList xa)) y \<Longrightarrow>
          lookup_default 0 z (envToContractDepthEnv (addToEnvironment label x (MList xa)))
          \<le> lookup_default 0 z (envToContractDepthEnv (addToEnvironment label y (MList xa)))"
  apply (induction xa)
  apply (simp add:addToEnvironment_def)
  apply (simp add:smallEnvironmentUpdate2)
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  by (smt delete.simps deleteNonExistentPreserves lookupEnvironment_def reverse_fold_last_step smallEnvironmentUpdate2)

lemma smallerEnvLookupDef : "lookupEnvironment label env = None \<Longrightarrow>
                             contractDepth (envToContractDepthEnv env) x
                           \<le> contractDepth (envToContractDepthEnv env) y \<Longrightarrow>
                             lookup_default 0 z (envToContractDepthEnv (addToEnvironment label x env))
                           \<le> lookup_default 0 z (envToContractDepthEnv (addToEnvironment label y env))"
  by (metis mlist.exhaust smallerEnvLookupDef_aux)

lemma nullifyLE : "lookupEnvironment label env = None \<Longrightarrow>
                   lookup_default 0 x (envToContractDepthEnv (addToEnvironment label (nullifyInvalidUses env contract) env))
                 \<le> lookup_default 0 x (envToContractDepthEnv (addToEnvironment label contract env))"
  using nullifySmallerEnv smallerEnvLookupDef by auto

lemma addSameToEnvLE : "lookupEnvironment label env = None \<Longrightarrow>
(\<And>x. lookup_default 0 x (envToContractDepthEnv (addToEnvironment label (nullifyInvalidUses env boundContract) env))
   \<le> lookup_default 0 x (update label (contractDepth (envToContractDepthEnv env) boundContract) (envToContractDepthEnv env)))"
  by (meson addSameToEnvLE_aux4 dual_order.trans nullifyLE)

lemma addToEnvEqUpdate : "lookupEnvironment label env = None \<Longrightarrow>
   contractDepth (envToContractDepthEnv (addToEnvironment label (nullifyInvalidUses env boundContract) env)) contract
 \<le> contractDepth (update label (contractDepth (envToContractDepthEnv env) boundContract) (envToContractDepthEnv env)) contract"
  by (meson addSameToEnvLE_aux4 dual_order.trans nullifyLE smallerEnvironment)

lemma maxDistinguishability1 : "(1 + max x y) > (x :: integer)"
  by auto

lemma maxDistinguishability2 : "(1 + max x y) > (y :: integer)"
  by auto

lemma maxCobounded1 : "(max x y) \<ge> (x :: integer)"
  by auto

lemma maxCobounded2 : "(max x y) \<ge> (y :: integer)"
  by auto

lemma maxSimp : "x \<le> x2 \<Longrightarrow> y \<le> y2 \<Longrightarrow> (1 + max x y) \<le> (1 + max x2 (y2 :: integer)) "
  by auto

lemma freshLabelIsGreaterThanFirstElem_aux : "getFreshLabel (MList ((k, v) # xa)) contract > (get_max_key_aux k xa)"
  by simp

lemma get_max_key_aux_ge : "get_max_key_aux k list \<ge> k"
  apply (induction k list rule:get_max_key_aux.induct)
  by auto

lemma freshLabelIsGreaterThanFirstElem_aux2 : "k < 1 + (case get_max_key (MList ((k, v) # xa)) of None \<Rightarrow> 0 :: integer | Some x \<Rightarrow> max 0 x)"
  apply (simp only: get_max_key.simps)
  apply simp
  by (simp add: add_strict_increasing get_max_key_aux_ge max.coboundedI2)

lemma freshLabelIsGreaterThanFirstElem : "(getFreshLabel (MList ((k, v) # xa)) contract) > (k :: integer)"
  by (simp add: add_strict_increasing get_max_key_aux_ge le_max_iff_disj)

lemma fold_max_inv : "fold_with_key (\<lambda>(uu, v). max (maxIdFromContract v)) z (MList xa) \<ge> z"
  apply (induction xa arbitrary:z)
  apply auto
  using max.bounded_iff by blast

lemma fold_max_acc : "x \<ge> y \<Longrightarrow>
                      fold_with_key (\<lambda>(uu, v). max (maxIdFromContract v)) x (MList xa) \<ge>
                      fold_with_key (\<lambda>(uu, v). max (maxIdFromContract v)) y (MList xa)"
  apply (induction xa arbitrary:x y)
  apply simp
  by auto

lemma freshLabelIsGreaterThanRest_aux3 : "(fold_with_key (\<lambda>(uu, v). max (maxIdFromContract v)) 0 (MList xa))
                                     \<le> (fold_with_key (\<lambda>(uu, v). max (maxIdFromContract v)) 0 (MList ((k, v) # xa)))"
  by (simp add: fold_max_acc)

lemma freshLabelIsGreaterThanRest_aux4 : "k \<le> x \<longrightarrow> get_max_key_aux k xa \<le> get_max_key_aux x xa"
  apply (induction xa arbitrary: k x)
  by auto

lemma freshLabelIsGreaterThanRest_aux5 : "get_max_key_aux k xa \<le> max 0 (get_max_key_aux x ((k, v) # xa))"
  apply simp
  by (simp add: freshLabelIsGreaterThanRest_aux4 max.coboundedI2)

lemma freshLabelIsGreaterThanRest_aux6 : "get_max_key (MList ((k, v) # xa)) = Some a \<Longrightarrow> a \<le> max 0 (get_max_key_aux x ((k, v) # xa))"
  using freshLabelIsGreaterThanRest_aux5 option.inject by fastforce

lemma freshLabelIsGreaterThanRest_aux7 : "(case get_max_key (MList xa) of None \<Rightarrow> 0 | Some x \<Rightarrow> max 0 x)
                                      \<le> (case get_max_key (MList ((k, v) # xa)) of None \<Rightarrow> 0 | Some x \<Rightarrow> max 0 x)"
  apply (cases "get_max_key (MList xa)")
  apply simp
  apply simp
  apply (cases xa)
  apply simp
  using freshLabelIsGreaterThanRest_aux6 by fastforce

lemma freshLabelIsGreaterThanRest : "(getFreshLabel (MList ((k, v) # xa)) contract) \<ge> ((getFreshLabel (MList xa) contract) :: LetLabel)"
  apply (simp only:getFreshLabel.simps)
  apply (rule maxSimp)
  using freshLabelIsGreaterThanRest_aux3 freshLabelIsGreaterThanRest_aux7 max.mono apply fastforce
  by simp

lemma freshLabelIsNotInEnv_aux : "(getFreshLabel (MList xa) contract \<le> l \<Longrightarrow> lookupEnvironment l (MList xa) = None) \<Longrightarrow>
                                 getFreshLabel (MList ((k, v) # xa)) contract \<le> l \<Longrightarrow> lookupEnvironment l (MList ((k, v) # xa)) = None"
  by (metis freshLabelIsGreaterThanFirstElem freshLabelIsGreaterThanRest leD lookup.simps(2) lookupEnvironment_def order.trans)

lemma freshLabelIsNotInEnv_aux2 : "getFreshLabel (MList xa) contract \<le> l \<Longrightarrow> lookupEnvironment l (MList xa) = None"
  apply (induction xa)
  apply (simp add: lookupEnvironment_def)
  using freshLabelIsNotInEnv_aux by fastforce

lemma freshLabelIsNotInEnv : "lookupEnvironment (getFreshLabel env contract) env = None"
  by (metis freshLabelIsNotInEnv_aux2 mlist.exhaust order_refl)

lemma letNormalCase : "lookupEnvironment label env = None \<Longrightarrow>
                            contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty
                                          (addToEnvironment label (nullifyInvalidUses env boundContract) env))
                                          contract
                         \<le> (contractDepth (update label (contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env) boundContract)
                                              (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env))
                                              contract)"
  using addToEnvEqUpdate by auto

lemma updateRewrite : "(\<And> a . lookup a y = lookup a z) \<Longrightarrow>
                       contractDepth y c =
                       contractDepth z c"
  by (simp add: depthSOEWhenEqual eq_iff etcdeSmallerWithMissingElements)

lemma updateCommutative : "label1 \<noteq> label2 \<Longrightarrow> contractDepth (update label1 y (update label2 x z)) c =
                           contractDepth (update label2 x (update label1 y z)) c"
  by (metis updateRewrite update_comm)  

lemma updateUnused : "maxIdFromContract c < label1 \<Longrightarrow> contractDepth (update label1 y z) c
                                                     = contractDepth z c"
  apply (induction c arbitrary: label1 y z)
  apply auto
  apply (metis updateCommutative)
  by (simp add: lookup_after_update2)

lemma updateUnused2 : "maxIdFromContract c < label2 \<Longrightarrow> contractDepth (update label1 y (update label1 x z)) c
                                                     = contractDepth (update label1 y (update label2 x z)) c"
  apply (simp add:double_update)
  apply (induction c arbitrary: label1 label2 x y z)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (metis updateCommutative updateUnused)
  by (metis updateCommutative updateUnused)

lemma rewritingLetRewrite : "x1 < label2 \<Longrightarrow> x1 \<noteq> label1 \<Longrightarrow>
       contractDepth (update label1 x (update x1 (contractDepth (update label2 x (p env)) (relabel label1 label2 contract1)) (p env))) contract2 =
       contractDepth (update label2 x (update x1 (contractDepth (update label2 x (p env)) (relabel label1 label2 contract1)) (p env))) (relabel label1 label2 contract2) \<Longrightarrow>
       contractDepth (update x1 (contractDepth (update label2 x (p env)) (relabel label1 label2 contract1)) (update label1 x (p env))) contract2 =
       contractDepth (update x1 (contractDepth (update label2 x (p env)) (relabel label1 label2 contract1)) (update label2 x (p env))) (relabel label1 label2 contract2)"
  using updateCommutative by auto

lemma rewriteLabelInRHS : "lookupEnvironment label2 env = None \<Longrightarrow>
                           label2 > maxIdFromContract contract \<Longrightarrow>
                            (contractDepth (update label1 x
                                              (p env))
                                              contract)
                          = (contractDepth (update label2 x
                                              (p env))
                                              (relabel label1 label2 contract))"
  apply (induction contract arbitrary:label1 label2 p env)
  apply (auto simp: updateUnused2)
  apply (rule rewritingLetRewrite)
  apply blast
  apply auto[1]
  apply meson
  apply (simp add:lookup_after_update3)
  by (simp add:lookup_after_update2)

lemma letRewriteCase : "contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty
                                      (addToEnvironment (getFreshLabel env contract) (nullifyInvalidUses env boundContract) env))
                                      (relabel label (getFreshLabel env contract) contract)
                         \<le> (contractDepth (update label (contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env) boundContract)
                                              (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env))
                                              contract)"
  by (smt freshLabelIsNotInEnv getFreshLabel.simps le_less_trans letNormalCase maxCobounded1 maxDistinguishability2 rewriteLabelInRHS)

lemma notDeletingInETCDE_aux : "lookup a x \<noteq> None \<Longrightarrow> lookup a ((\<lambda> e. update l (contractDepth e c) e) x) \<noteq> None"
  by (metis lookup_after_update2 lookup_after_update3 option.distinct(1))

lemma notDeletingInETCDE_aux2 : " (lookupEnvironment label (MList xa) = Some x2 \<Longrightarrow>
        \<exists>y. lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa)) = Some y) \<Longrightarrow>
       lookupEnvironment label (MList ((l, c) # xa)) = Some x2 \<Longrightarrow>
       \<exists>y. lookup label
            ((\<lambda> e. update l (contractDepth e c) e) (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa))) =
           Some y"
  by (smt lookup.simps(2) lookupEnvironment_def lookup_after_update3 notDeletingInETCDE_aux not_Some_eq)

lemma notDeletingInETCDE_aux3 : "lookupEnvironment label (MList xa) = Some x2 \<Longrightarrow> lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa)) \<noteq> None"
  apply (induction xa)
  apply (simp add:lookupEnvironment_def)
  apply (simp add:addToEnvironment_def del:reverse_fold_with_key.simps add:reverse_fold_last_step)
  using notDeletingInETCDE_aux2 by fastforce

lemma notDeletingInETCDE : "lookupEnvironment label env = Some x2 \<Longrightarrow> lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env) \<noteq> None"
  by (smt mlist.exhaust notDeletingInETCDE_aux3)

lemma useCase_aux : "(lookup label (MList xa) = Some x2 \<Longrightarrow>
        lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa)) = Some x3 \<Longrightarrow>
        contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (delete_until label (MList xa))) x2 < Suc x3) \<Longrightarrow>
       lookup label (MList ((k, v) # xa)) = Some x2 \<Longrightarrow>
       lookup label
        ((\<lambda>e. update k (contractDepth e v) e) (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa))) =
       Some x3 \<Longrightarrow>
       contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (delete_until label (MList ((k, v) # xa)))) x2 < Suc x3"
  apply (cases "label = k")
  apply auto
  apply (metis (no_types, lifting) etcdeSmallerWithMissingElements isDepthSmallerOrEqual.simps(1) isDepthSmallerOrEqual.simps(2) le_imp_less_Suc lookup_after_update3 nothingComesFromNothing option.sel split_option_all)
  apply (simp add: lookup_after_update3)
  by (simp add: lookup_after_update2)

lemma useCase_aux2 : "lookupEnvironment label (MList xa) = Some x2 \<Longrightarrow>
          lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (MList xa)) = Some x3 \<Longrightarrow>
          contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (deleteFromEnvironment label (MList xa))) x2 < Suc x3"
  apply (induction xa)
  apply (simp add:deleteFromEnvironment_def lookupEnvironment_def)
  apply (simp add:deleteFromEnvironment_def lookupEnvironment_def reverse_fold_last_step del:reverse_fold_with_key.simps)
  using useCase_aux by auto

lemma useCase : "lookupEnvironment label env = Some x2 \<Longrightarrow>
                 lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env) = Some x3 \<Longrightarrow>
       contractDepth (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty (deleteFromEnvironment label env)) x2
       < Suc (case lookup label (reverse_fold_with_key (\<lambda>(l, c) e. update l (contractDepth e c) e) MList.empty env) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"
  apply simp
  by (smt mlist.exhaust useCase_aux2)

termination reduceRec
  apply (relation "measure (\<lambda>(_,(_,(env,ci))). contractDepth (envToContractDepthEnv env) ci)")
  apply auto
  apply (simp add: less_Suc_eq_le letNormalCase)
  using getFreshLabel.simps le_imp_less_Suc letRewriteCase apply presburger
  using notDeletingInETCDE useCase by fastforce

fun reduce :: "BlockNumber \<Rightarrow> State \<Rightarrow> Contract \<Rightarrow> Contract" where
"reduce blockNum state contract =
   reduceRec blockNum state emptyEnvironment contract"

(* ToDo: reduce useless primitives to Null *)
fun simplify :: "Contract \<Rightarrow> Contract" where
"simplify contract = contract"

(* How much everybody pays or receives in a transaction *)
type_synonym TransactionOutcomes = "(Person, integer) mlist"

definition emptyOutcome :: "TransactionOutcomes" where
"emptyOutcome = MList.empty"

fun isEmptyOutcome :: "TransactionOutcomes \<Rightarrow> bool" where
"isEmptyOutcome trOut = MList.fold_with_key (\<lambda> (_, v) acc. acc \<and> (v = 0)) True trOut"

(* Adds a value to the map of outcomes *)
fun addOutcome :: "Person \<Rightarrow> integer \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"addOutcome person diffValue trOut =
   (let newValue = case MList.lookup person trOut of
                     Some value \<Rightarrow> value + diffValue
                   | None \<Rightarrow> diffValue in
    MList.update person newValue trOut)"

(* Get effect of outcomes on the bank of the contract *)
fun outcomeEffect :: "TransactionOutcomes \<Rightarrow> integer" where
"outcomeEffect trOut = MList.fold_with_key (\<lambda> (_, v) acc . acc - v) 0 trOut"

(* Add two transaction outcomes together *)
fun combineOutcomes :: "TransactionOutcomes \<Rightarrow> TransactionOutcomes \<Rightarrow> TransactionOutcomes" where
"combineOutcomes to1 to2 =
   MList.fold_with_key (\<lambda> (k, v) acc . addOutcome k v acc) to1 to2"

datatype (set: 'a) fetchResult =
    Picked 'a
  | NoMatch
  | MultipleMatches

datatype DetachedPrimitive =
   DCommit IdCommit Person integer Timeout
 | DPay IdCommit Person integer

(* Semantics of Scale *)
fun scaleValue :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer" where
"scaleValue divid divis def val = (if (divis = 0) then def else ((val * divid) div divis))"

fun scaleResult :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> DetachedPrimitive \<Rightarrow> DetachedPrimitive" where
"scaleResult divid divis def (DCommit idCommit person val tim) =
   DCommit idCommit person (scaleValue divid divis def val) tim" |
"scaleResult divid divis def (DPay idCommit person val) =
   DPay idCommit person (scaleValue divid divis def val)"

(* Find out whether the Action is allowed given the current state
   and contract, and, if so, pick the corresponding primitive in the contract.
   Also return the contract without the selected primitive. *)
fun fetchPrimitive :: "IdAction \<Rightarrow> BlockNumber \<Rightarrow> State \<Rightarrow> Contract
                    \<Rightarrow> (DetachedPrimitive \<times> Contract) fetchResult" where
"fetchPrimitive idAction blockNum state (Commit idActionC idCommit person value _ timeout continuation _) =
  (let notCurrentCommit = \<not> (isCurrentCommit idCommit state) in
   let notExpiredCommit = \<not> (isExpiredCommit idCommit state) in
   let actualValue = evalValue blockNum state value in
   if ((idAction = idActionC) \<and> notCurrentCommit \<and> notExpiredCommit)
   then Picked ((DCommit idCommit person actualValue timeout),
                continuation)
   else NoMatch)" |
"fetchPrimitive idAction blockNum state (Pay idActionC idCommit person value _ continuation _) =
  (let actualValue = evalValue blockNum state value in
   if (idAction = idActionC)
   then Picked ((DPay idCommit person actualValue), continuation)
   else NoMatch)" |
"fetchPrimitive idAction blockNum state (Both leftContract rightContract) =
  (case (fetchPrimitive idAction blockNum state leftContract,
         fetchPrimitive idAction blockNum state rightContract) of
      (Picked (result, cont), NoMatch) \<Rightarrow> Picked (result, (Both cont rightContract))
    | (NoMatch, Picked (result, cont)) \<Rightarrow> Picked (result, (Both leftContract cont))
    | (NoMatch, NoMatch) \<Rightarrow> NoMatch
    | _                  \<Rightarrow> MultipleMatches)" |
"fetchPrimitive idAction blockNum state (While obs timeout contract1 contract2) =
  (case fetchPrimitive idAction blockNum state contract1 of
      Picked (result, cont) \<Rightarrow> Picked (result, While obs timeout cont contract2)
    | NoMatch \<Rightarrow> NoMatch
    | MultipleMatches \<Rightarrow> MultipleMatches)" |
"fetchPrimitive idAction blockNum state (Let label boundContract subContract) =
  (case fetchPrimitive idAction blockNum state subContract of
      Picked (result, cont) \<Rightarrow> Picked (result, Let label boundContract cont)
    | NoMatch \<Rightarrow> NoMatch
    | MultipleMatches \<Rightarrow> MultipleMatches)" |
"fetchPrimitive idAction blockNum state (Scale divid divis def subContract) =
  (let sDivid = evalValue blockNum state divid in
   let sDivis = evalValue blockNum state divis in
   let sDef = evalValue blockNum state def in
   case fetchPrimitive idAction blockNum state subContract of
      Picked (result, cont) \<Rightarrow> Picked (scaleResult sDivid sDivis sDef result,
                                       Scale divid divis def cont)
   |  NoMatch \<Rightarrow> NoMatch
   |  MultipleMatches \<Rightarrow> MultipleMatches)" |
"fetchPrimitive a b c Null = NoMatch" |
"fetchPrimitive a b c (Choice v va vb) = NoMatch" |
"fetchPrimitive a b c (When v va vb vc) = NoMatch" |
"fetchPrimitive a b c (Use v) = NoMatch"

datatype DynamicProblem =
   NoProblem
 | CommitNotMade
 | NotEnoughMoneyLeftInCommit
 | CommitIsExpired

datatype (set: 'a) evaluationResult =
    Result 'a DynamicProblem
  | InconsistentState (* This should not happen when using fetchPrimitive result *)

(* Evaluation of actionable input *)
fun eval :: "DetachedPrimitive \<Rightarrow> State \<Rightarrow> (TransactionOutcomes \<times> State) evaluationResult" where
"eval (DCommit idCommit person value timeout) state =
  (if (isCurrentCommit idCommit state) \<or> (isExpiredCommit idCommit state)
   then InconsistentState
   else Result ( addOutcome person (- value) emptyOutcome
               , addCommit idCommit person value timeout state )
               NoProblem)" |
"eval (DPay idCommit person value) state =
  (let maxValue = getAvailableAmountInCommit idCommit state in
   if (\<not> isCurrentCommit idCommit state)
   then (if (\<not> isExpiredCommit idCommit state)
         then Result (emptyOutcome, state) CommitNotMade
         else Result (emptyOutcome, state) CommitIsExpired)
   else (if value > maxValue
         then (case (discountAvailableMoneyFromCommit idCommit maxValue state) of
                 Some x \<Rightarrow> Result (addOutcome person maxValue emptyOutcome, x)
                                  NotEnoughMoneyLeftInCommit
               | None \<Rightarrow> InconsistentState)
         else (case (discountAvailableMoneyFromCommit idCommit value state) of
                 Some x \<Rightarrow> Result (addOutcome person value emptyOutcome, x)
                                  NoProblem
               | None \<Rightarrow> InconsistentState)))"

(* Check whether the person who must sign has signed *)
fun areActionPermissionsValid :: "DetachedPrimitive \<Rightarrow> Person slist \<Rightarrow> bool" where
"areActionPermissionsValid (DCommit _ person _ _) sigs = SList.member person sigs" |
"areActionPermissionsValid (DPay _ person _) sigs = SList.member person sigs"

fun areInputPermissionsValid :: "Input \<Rightarrow> Person slist \<Rightarrow> bool" where
"areInputPermissionsValid (IChoice (_, person) _) sigs = SList.member person sigs" |
"areInputPermissionsValid (IOracle _ _ _) _ = True"
  (* Implementation ToDo: need to check oracle signature *)

(* Check whether a commit or payment has negative value *)
fun isTransactionNegative :: "DetachedPrimitive \<Rightarrow> bool" where
"isTransactionNegative (DCommit _ _ val _) = (val < 0)" |
"isTransactionNegative (DPay _ _ val) = (val < 0)"

datatype ErrorResult =
    InvalidInput
  | NoValidSignature
  | NegativeTransaction
  | AmbiguousId
  | InternalError (* This should not happen *)

datatype (set: 'a) applicationResult =
   SuccessfullyApplied 'a DynamicProblem
 | CouldNotApply ErrorResult

(* High level wrapper that calls the appropriate update function on contract and state.
   Assumes contract has been reduced. That must be done before and after applyAnyInput. *)
fun applyAnyInput :: "AnyInput \<Rightarrow> Person slist \<Rightarrow> IdInput slist \<Rightarrow> BlockNumber \<Rightarrow> State \<Rightarrow> Contract
                    \<Rightarrow> (TransactionOutcomes \<times> State \<times> Contract) applicationResult" where
"applyAnyInput anyInput sigs neededInputs blockNum state contract =
  (case addAnyInput blockNum anyInput neededInputs state of
     Some updatedState \<Rightarrow>
      (case anyInput of
         Input input \<Rightarrow>
           if areInputPermissionsValid input sigs
           then SuccessfullyApplied ( emptyOutcome
                                    , updatedState
                                    , contract )
                                    NoProblem
           else CouldNotApply NoValidSignature
       | Action idAction \<Rightarrow>
          (case fetchPrimitive idAction blockNum updatedState contract of
             Picked (primitive, newContract) \<Rightarrow>
              (case eval primitive updatedState of
                 Result (transactionOutcomes, newState) dynamicProblem =>
                   if isTransactionNegative primitive
                   then CouldNotApply NegativeTransaction
                   else if areActionPermissionsValid primitive sigs
                        then SuccessfullyApplied (transactionOutcomes,
                                                  newState,
                                                  newContract) dynamicProblem
                        else CouldNotApply NoValidSignature
               | InconsistentState \<Rightarrow> CouldNotApply InternalError)
           | NoMatch \<Rightarrow> CouldNotApply InvalidInput
           | MultipleMatches \<Rightarrow> CouldNotApply AmbiguousId))
   | None \<Rightarrow> CouldNotApply InvalidInput)"

(* Give redeemed money to owners *)
fun redeemMoneyLoop :: "Person list \<Rightarrow> TransactionOutcomes \<Rightarrow> State
                     \<Rightarrow> (TransactionOutcomes \<times> State)" where
"redeemMoneyLoop [] trOut state = (trOut, state)" |
"redeemMoneyLoop (h # t) trOut state =
  (let redeemed = getRedeemedForPerson h state in
   let newState = resetRedeemedForPerson h state in
   redeemMoneyLoop t (addOutcome h redeemed trOut) newState)"

fun redeemMoney :: "Person slist \<Rightarrow> State \<Rightarrow> (TransactionOutcomes \<times> State)" where
"redeemMoney sigs state = redeemMoneyLoop (SList.toList sigs) emptyOutcome state"

datatype (set: 'a) mApplicationResult =
   MSuccessfullyApplied 'a "DynamicProblem list"
 | MCouldNotApply ErrorResult

(* Fold applyAnyInput through a list of AnyInputs.
   Check that balance is positive at every step
   In the last step: simplify *)
fun applyAnyInputs :: "AnyInput list \<Rightarrow> Person slist \<Rightarrow> IdInput slist \<Rightarrow> BlockNumber \<Rightarrow> State \<Rightarrow> Contract
                    \<Rightarrow> integer
                    \<Rightarrow> TransactionOutcomes
                    \<Rightarrow> DynamicProblem list
                    \<Rightarrow> (integer \<times> TransactionOutcomes \<times> State \<times> Contract) mApplicationResult" where
"applyAnyInputs [] sigs _ _ state contract value trOut dynProbList =
  (let (currTrOut, newState) = redeemMoney sigs state in
   let newValue = value + outcomeEffect currTrOut in
   if newValue < 0
   then MCouldNotApply InternalError
   else let newTrOut = combineOutcomes currTrOut trOut in
        let simplifiedContract = simplify contract in
        MSuccessfullyApplied (newValue, newTrOut, newState, simplifiedContract) dynProbList)" |
"applyAnyInputs (h#t) sigs neededInputs blockNum state contract value trOut dynProbList =
  (case applyAnyInput h sigs neededInputs blockNum state contract of
     SuccessfullyApplied (currTrOut, newState, newContract) newDynProb \<Rightarrow>
       let newValue = value + outcomeEffect currTrOut in
       if newValue < 0
       then MCouldNotApply InternalError
       else let newTrOut = combineOutcomes currTrOut trOut in
            let reducedNewContract = reduce blockNum newState newContract in
            applyAnyInputs t sigs neededInputs blockNum newState reducedNewContract newValue newTrOut
                           (dynProbList @ [newDynProb])
  | CouldNotApply currError \<Rightarrow> MCouldNotApply currError)"

(* Expire commits and apply applyAnyInputs *)
fun applyTransaction :: "AnyInput list \<Rightarrow> Person slist \<Rightarrow> BlockNumber \<Rightarrow> State \<Rightarrow> Contract
                      \<Rightarrow> integer 
                      \<Rightarrow> (integer \<times> TransactionOutcomes \<times> State \<times> Contract) mApplicationResult" where
"applyTransaction inputs sigs blockNum state contract value =
 (let neededInputs = collectNeededInputsFromContract contract in
  let expiredState = expireCommits blockNum state in
  let reducedContract = reduce blockNum expiredState contract in
  let appResult = applyAnyInputs inputs sigs neededInputs blockNum expiredState
                                   reducedContract value emptyOutcome [] in
  case appResult of
     MSuccessfullyApplied (_, tranOut, _, _) _ \<Rightarrow>
        if (inputs = []) \<and> (reducedContract = contract) \<and> (isEmptyOutcome tranOut)
        then MCouldNotApply InvalidInput
        else appResult
  |  _ \<Rightarrow> appResult)"

(* NOTE: in implementation it must be checked that oracle values are signed by the oracle *)


