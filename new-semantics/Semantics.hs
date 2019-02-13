module Semantics where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Foldable as F
import Data.Maybe (fromJust, fromMaybe)

type BlockNumber = Integer
type Timeout = BlockNumber
type Person = Integer
type Choice = Integer

type IdAction = Integer
type IdCommit = Integer
type IdChoice = (Integer, Person)
type IdOracle = Integer

type LetLabel = Integer

data Value = CurrentBlock |
             Committed IdCommit |
             Constant Integer |
             NegValue Value |
             AddValue Value Value |
             SubValue Value Value |
             MulValue Value Value |
             DivValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ModValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ValueFromChoice IdChoice Value |
 --    default value if not available --^
             ValueFromOracle IdOracle Value
 --    default value if not available --^
               deriving (Eq,Ord,Show,Read)

data Observation = BelowTimeout Timeout |
                   AndObs Observation Observation |
                   OrObs Observation Observation |
                   NotObs Observation |
                   ChoseThis IdChoice Choice |
                   ChoseSomething IdChoice |
                   ValueGE Value Value |
                   ValueGT Value Value |
                   ValueLT Value Value |
                   ValueLE Value Value |
                   ValueEQ Value Value |
                   TrueObs |
                   FalseObs
               deriving (Eq,Ord,Show,Read)

data Contract =
    Null |
    Commit !IdAction !IdCommit !Person !Value !Timeout !Timeout !Contract !Contract |
    Pay !IdAction !IdCommit !Person !Value !Timeout !Contract !Contract |
    Both !Contract !Contract |
    Choice !Observation !Contract !Contract |
    When !Observation !Timeout !Contract !Contract |
    While !Observation !Timeout !Contract !Contract |
    Scale !Value !Value !Value !Contract |
    Let !LetLabel !Contract !Contract |
    Use !LetLabel
               deriving (Eq,Ord,Show,Read)

-- Data type for Inputs with their information 
data Input = IChoice IdChoice Choice
           | IOracle IdOracle BlockNumber Integer
               deriving (Eq,Ord,Show,Read)
data AnyInput = Action IdAction
              | Input Input
               deriving (Eq,Ord,Show,Read)

data IdInput = IdChoice IdChoice
             | IdOracle IdOracle
               deriving (Eq,Ord,Show,Read)


type TimeoutData = M.Map Timeout (S.Set IdCommit)

data CommitInfo = CommitInfo { redeemedPerPerson :: M.Map Person Integer
                             , currentCommitsById :: M.Map IdCommit (Person, Integer, Timeout)
                             , expiredCommitIds :: S.Set IdCommit
                             , timeoutData :: TimeoutData }
               deriving (Eq,Ord,Show,Read)

data State = State { commits :: CommitInfo
                   , choices :: M.Map IdChoice Choice
                   , oracles :: M.Map IdOracle (BlockNumber, Integer)
                   , usedIds :: S.Set IdAction}
               deriving (Eq,Ord,Show,Read)

-- Adds a commit identifier to the timeout data map 
addToCommByTim :: Timeout -> IdCommit -> TimeoutData -> TimeoutData 
addToCommByTim timeout idCommit timData =
  case M.lookup timeout timData of
    Just commSet -> M.insert timeout (S.insert idCommit commSet) timData
    Nothing -> M.insert timeout (S.singleton idCommit) timData

-- Remove a commit identifier from the timeout data map 
removeFromCommByTim :: Timeout -> IdCommit -> TimeoutData -> TimeoutData
removeFromCommByTim timeout idCommit timData =
  case M.lookup timeout timData of
    Just commSet -> let newCommSet = S.delete idCommit commSet in
                    if null newCommSet
                    then M.delete timeout timData
                    else M.insert timeout newCommSet timData
    Nothing -> timData 

-- Add a commit to CommitInfo
addCommit :: IdCommit -> Person -> Integer -> Timeout -> State -> State
addCommit idCommit person value timeout
   state@(State { commits = commitInfo@(CommitInfo { currentCommitsById = commById
                                                   , timeoutData = timData }) }) =
 state { commits = commitInfo { currentCommitsById = M.insert idCommit (person, value, timeout) commById
                              , timeoutData = addToCommByTim timeout idCommit timData } }

-- Return the person corresponding to a commit
personForCurrentCommit :: IdCommit -> State -> Maybe Person
personForCurrentCommit idCommit state =
  case M.lookup idCommit (currentCommitsById (commits state)) of
    Just (person, _, _) -> Just person
    Nothing -> Nothing

-- Check whether the commit is current (committed not expired)
isCurrentCommit :: IdCommit -> State -> Bool
isCurrentCommit idCommit state =
  case M.lookup idCommit (currentCommitsById (commits state)) of
    Just _ -> True 
    Nothing -> False

-- Check whether the commit is expired
isExpiredCommit :: IdCommit -> State -> Bool
isExpiredCommit idCommit state = idCommit `S.member` (expiredCommitIds (commits state))

-- Remove a current commit from CommitInfo
removeCurrentCommit :: IdCommit -> State -> State
removeCurrentCommit idCommit
   state@(State { commits = commitInfo@(CommitInfo { currentCommitsById = commById
                                                   , timeoutData = timData }) }) =
  case M.lookup idCommit commById of
    Just (_, _, timeout) ->
         state { commits = commitInfo { currentCommitsById = M.delete idCommit commById
                                      , timeoutData = removeFromCommByTim timeout idCommit timData } }
    Nothing -> state

-- Get expired not collected for person
getRedeemedForPersonCI :: Person -> CommitInfo -> Integer
getRedeemedForPersonCI person ci =
  case M.lookup person (redeemedPerPerson ci) of
    Nothing -> 0
    Just value -> value

getRedeemedForPerson :: Person -> State -> Integer
getRedeemedForPerson person state = getRedeemedForPersonCI person $ commits state

-- Set the amount in redeemedPerPerson to zero
resetRedeemedForPerson :: Person -> State -> State
resetRedeemedForPerson person
   state@(State { commits = commitInfo@(CommitInfo { redeemedPerPerson = redeemedPerPersonMap}) }) =
 state { commits = commitInfo { redeemedPerPerson = M.delete person redeemedPerPersonMap } }

discountAvailableMoneyFromCommit :: IdCommit -> Integer -> State -> Maybe State
discountAvailableMoneyFromCommit idCommit discount
   state@(State { commits = commitInfo@(CommitInfo { currentCommitsById = commById }) }) =
  case M.lookup idCommit commById of
    Just (person, value, timeout) -> Just $ state {
                commits = commitInfo {
                     currentCommitsById = M.insert idCommit (person, value - discount, timeout) commById }
       }
    Nothing -> Nothing

getAvailableAmountInCommit :: IdCommit -> State -> Integer
getAvailableAmountInCommit idCommit state =
  case M.lookup idCommit (currentCommitsById (commits state)) of
    Just (_, value, _) -> value
    Nothing -> 0

-- Collect inputs needed by a contract
collectNeededInputsFromValue :: Value -> S.Set IdInput
collectNeededInputsFromValue (CurrentBlock) = S.empty
collectNeededInputsFromValue (Committed _)= S.empty
collectNeededInputsFromValue (Constant _) = S.empty
collectNeededInputsFromValue (NegValue value) =
  collectNeededInputsFromValue value
collectNeededInputsFromValue (AddValue value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromValue (SubValue value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromValue (MulValue value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromValue (DivValue value1 value2 value3) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2
           , collectNeededInputsFromValue value3 ]
collectNeededInputsFromValue (ModValue value1 value2 value3) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2
           , collectNeededInputsFromValue value3 ]
collectNeededInputsFromValue (ValueFromChoice idChoice value) =
  S.unions [ S.singleton (IdChoice idChoice)
           , collectNeededInputsFromValue value ]
collectNeededInputsFromValue (ValueFromOracle idOracle value) =
  S.unions [ S.singleton (IdOracle idOracle)
           , collectNeededInputsFromValue value ]

collectNeededInputsFromObservation :: Observation -> S.Set IdInput
collectNeededInputsFromObservation (BelowTimeout _) = S.empty
collectNeededInputsFromObservation (AndObs observation1 observation2) =
  S.unions [ collectNeededInputsFromObservation observation1
           , collectNeededInputsFromObservation observation2 ]
collectNeededInputsFromObservation (OrObs observation1 observation2) =
  S.unions [ collectNeededInputsFromObservation observation1
           , collectNeededInputsFromObservation observation2 ]
collectNeededInputsFromObservation (NotObs observation) =
  collectNeededInputsFromObservation observation
collectNeededInputsFromObservation (ChoseThis idChoice _) = S.singleton (IdChoice idChoice)
collectNeededInputsFromObservation (ChoseSomething idChoice) = S.singleton (IdChoice idChoice)
collectNeededInputsFromObservation (ValueGE value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromObservation (ValueGT value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromObservation (ValueLT value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromObservation (ValueLE value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromObservation (ValueEQ value1 value2) =
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2 ]
collectNeededInputsFromObservation (TrueObs) = S.empty
collectNeededInputsFromObservation (FalseObs) = S.empty

collectNeededInputsFromContract :: Contract -> S.Set IdInput
collectNeededInputsFromContract Null = S.empty
collectNeededInputsFromContract (Commit _ _ _ value _ _ contract1 contract2) =
  S.unions [ collectNeededInputsFromValue value
           , collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (Pay _ _ _ value _ contract1 contract2) =
  S.unions [ collectNeededInputsFromValue value
           , collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (Both contract1 contract2) =
  S.unions [ collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (Choice observation contract1 contract2) =
  S.unions [ collectNeededInputsFromObservation observation
           , collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (When observation _ contract1 contract2) =
  S.unions [ collectNeededInputsFromObservation observation
           , collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (While observation _ contract1 contract2) =
  S.unions [ collectNeededInputsFromObservation observation
           , collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (Scale value1 value2 value3 contract) = 
  S.unions [ collectNeededInputsFromValue value1
           , collectNeededInputsFromValue value2
           , collectNeededInputsFromValue value3
           , collectNeededInputsFromContract contract ]
collectNeededInputsFromContract (Let _ contract1 contract2) =
  S.unions [ collectNeededInputsFromContract contract1
           , collectNeededInputsFromContract contract2 ]
collectNeededInputsFromContract (Use _) = S.empty

-- Add inputs and action ids to state.
-- Return Nothing on redundant or irrelevant inputs
addAnyInput :: BlockNumber -> AnyInput -> S.Set IdInput -> State -> Maybe State
--  current block ---^
addAnyInput _ (Action idInput) _ state@(State { usedIds = usedIdsSet })
  | idInput `S.member` usedIdsSet = Nothing
  | otherwise = Just $ state { usedIds = S.insert idInput usedIdsSet }
addAnyInput _ (Input (IChoice idChoice choice)) neededInputs state@(State { choices = choiceMap })
  | idChoice `M.member` choiceMap = Nothing
  | (IdChoice idChoice) `S.member` neededInputs = Just $ state { choices = M.insert idChoice choice choiceMap }
  | otherwise = Nothing
addAnyInput blockNumber (Input (IOracle idOracle timestamp value)) neededInputs
            state@(State { oracles = oracleMap }) =
  case M.lookup idOracle oracleMap of
    Just (lastTimestamp, _) ->
        if (timestamp > lastTimestamp) && (timestamp <= blockNumber) && ((IdOracle idOracle) `S.member` neededInputs)
        then Just newState
        else Nothing
    Nothing -> Just newState
  where newState = state { oracles = M.insert idOracle (timestamp, value) oracleMap }

-- Decides whether something has expired
isExpired :: BlockNumber -> BlockNumber -> Bool
isExpired currBlockNum expirationBlockNum = currBlockNum >= expirationBlockNum

-- Expire commits
expireOneCommit :: IdCommit -> CommitInfo -> CommitInfo
expireOneCommit idCommit commitInfo@(CommitInfo { redeemedPerPerson = redPerPer
                                                , currentCommitsById = currentCommits }) =
  case M.lookup idCommit currentCommits of
    Just (person, value, _) ->
          let redeemedBefore = M.findWithDefault 0 person redPerPer in
          commitInfo { redeemedPerPerson = M.insert person (redeemedBefore + value) redPerPer
                     , currentCommitsById = M.delete idCommit currentCommits }
    Nothing -> commitInfo

expireManyCommits :: S.Set IdCommit -> CommitInfo -> CommitInfo
expireManyCommits commitIds commitInfo@(CommitInfo { expiredCommitIds = expiComms }) =
      S.foldr' expireOneCommit semiUpdatedCI commitIds
  where semiUpdatedCI = (commitInfo { expiredCommitIds = S.union expiComms commitIds })

expireCommitsCI :: BlockNumber -> CommitInfo -> CommitInfo 
expireCommitsCI blockNumber commitInfo =
  case M.minViewWithKey timData of
    Just ((minBlock, commIds), remTimData) ->
       if isExpired blockNumber minBlock
       then let partUpdatedCommitInfo = commitInfo { timeoutData = remTimData } in
            let updatedCommitInfo = expireManyCommits commIds partUpdatedCommitInfo in
            expireCommitsCI blockNumber updatedCommitInfo 
       else commitInfo
    Nothing -> commitInfo
  where timData = timeoutData commitInfo

expireCommits :: BlockNumber -> State -> State
expireCommits blockNumber state@(State { commits = commitInfo }) =
  state { commits = expireCommitsCI blockNumber commitInfo }
 
-- Evaluate a value
evalValue :: BlockNumber -> State -> Value -> Integer
evalValue blockNumber _ CurrentBlock = blockNumber
evalValue _ state (Committed idCommit) = getAvailableAmountInCommit idCommit state
evalValue _ _ (Constant value) = value
evalValue blockNumber state (NegValue value) = - (evalValue blockNumber state value)
evalValue blockNumber state (AddValue lhs rhs) = (go lhs) + (go rhs)
  where go = evalValue blockNumber state
evalValue blockNumber state (SubValue lhs rhs) = (go lhs) - (go rhs)
  where go = evalValue blockNumber state
evalValue blockNumber state (MulValue lhs rhs) = (go lhs) * (go rhs)
  where go = evalValue blockNumber state
evalValue blockNumber state (DivValue dividend divisor defaultVal) =
  if actualDivisor == 0 then go defaultVal else div (go dividend) actualDivisor
  where go = evalValue blockNumber state
        actualDivisor = go divisor
evalValue blockNumber state (ModValue dividend divisor defaultVal) =
  if actualDivisor == 0 then go defaultVal else mod (go dividend) actualDivisor
  where go = evalValue blockNumber state
        actualDivisor = go divisor
evalValue blockNumber state (ValueFromChoice idChoice val) =
  fromMaybe (evalValue blockNumber state val) $ M.lookup idChoice (choices state) 
evalValue blockNumber state (ValueFromOracle idOracle val) =
  case M.lookup idOracle (oracles state) of
    Just (_, oracleValue) -> oracleValue
    Nothing -> evalValue blockNumber state val


-- Evaluate an observation
evalObservation :: BlockNumber -> State -> Observation -> Bool
evalObservation blockNumber _ (BelowTimeout timeout) = not $ isExpired blockNumber timeout 
evalObservation blockNumber state (AndObs obs1 obs2) = (go obs1) && (go obs2)
  where go = evalObservation blockNumber state
evalObservation blockNumber state (OrObs obs1 obs2) = (go obs1) && (go obs2) 
  where go = evalObservation blockNumber state
evalObservation blockNumber state (NotObs obs) = not $ evalObservation blockNumber state obs 
evalObservation _ state (ChoseThis idChoice choice) = 
  case M.lookup idChoice (choices state) of
    Just actualChoice -> actualChoice == choice
    Nothing -> False
evalObservation _ state (ChoseSomething idChoice) = 
  idChoice `M.member` (choices state)
evalObservation blockNumber state (ValueGE val1 val2) = (go val1) >= (go val2)
  where go = evalValue blockNumber state
evalObservation blockNumber state (ValueGT val1 val2) = (go val1) > (go val2) 
  where go = evalValue blockNumber state
evalObservation blockNumber state (ValueLT val1 val2) = (go val1) < (go val2) 
  where go = evalValue blockNumber state
evalObservation blockNumber state (ValueLE val1 val2) = (go val1) <= (go val2) 
  where go = evalValue blockNumber state
evalObservation blockNumber state (ValueEQ val1 val2) = (go val1) == (go val2) 
  where go = evalValue blockNumber state
evalObservation _ _ TrueObs = True 
evalObservation _ _ FalseObs = False

isNormalised :: Integer -> Integer -> Bool
isNormalised divid divis = divid == divis && divid /= 0

type Environment = M.Map Integer Contract
emptyEnvironment :: Environment
emptyEnvironment = M.empty

addToEnvironment :: LetLabel -> Contract -> Environment -> Environment
addToEnvironment = M.insert

lookupEnvironment :: LetLabel -> Environment -> Maybe Contract
lookupEnvironment = M.lookup

maxIdFromContract :: Contract -> LetLabel 
maxIdFromContract Null = 0
maxIdFromContract (Commit _ _ _ _ _ _ contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (Pay _ _ _ _ _ contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (Both contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (Choice _ contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (When _ _ contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (While _ _ contract1 contract2) =
  (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (Scale _ _ _ contract) =
  (maxIdFromContract contract)
maxIdFromContract (Let letLabel contract1 contract2) =
  max letLabel (max (maxIdFromContract contract1) (maxIdFromContract contract2))
maxIdFromContract (Use letLabel) =
  letLabel

getFreshKey :: Environment -> Contract -> LetLabel
getFreshKey env c =
  1 + max (case M.lookupMax env of
             Nothing -> 0
             Just (k, _) -> max k 0) (maxIdFromContract c)

nullifyInvalidUses :: Environment -> Contract -> Contract
nullifyInvalidUses _ Null = Null
nullifyInvalidUses env (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  Commit idAction idCommit person value timeout1 timeout2 (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (Pay idAction idCommit person value timeout contract1 contract2) =
  Pay idAction idCommit person value timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (Both contract1 contract2) =
  Both (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (Choice observation contract1 contract2) =
  Choice observation (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (When observation timeout contract1 contract2) =
  When observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (While observation timeout contract1 contract2) =
  While observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)
nullifyInvalidUses env (Scale value1 value2 value3 contract) =
  Scale value1 value2 value3 (nullifyInvalidUses env contract)
nullifyInvalidUses env (Let letLabel contract1 contract2) =
  Let letLabel (nullifyInvalidUses env contract1) (nullifyInvalidUses newEnv contract2)
  where newEnv = addToEnvironment letLabel Null env -- We just need to mark it as available for this function 
nullifyInvalidUses env (Use letLabel) =
  case lookupEnvironment letLabel env of
    Nothing -> Null
    Just _ -> Use letLabel

relabel :: LetLabel -> LetLabel -> Contract -> Contract
relabel _ _ Null = Null
relabel startLabel endLabel (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) =
  Commit idAction idCommit person value timeout1 timeout2 (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (Pay idAction idCommit person value timeout contract1 contract2) =
  Pay idAction idCommit person value timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (Both contract1 contract2) =
  Both (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (Choice observation contract1 contract2) =
  Choice observation (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (When observation timeout contract1 contract2) =
  When observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (While observation timeout contract1 contract2) =
  While observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)
relabel startLabel endLabel (Scale value1 value2 value3 contract) =
  Scale value1 value2 value3 (relabel startLabel endLabel contract)
relabel startLabel endLabel (Let letLabel contract1 contract2) =
  Let letLabel (relabel startLabel endLabel contract1)
      (if (letLabel == startLabel)
       then contract2
       else relabel startLabel endLabel contract2)
relabel startLabel endLabel (Use letLabel) =
  if (letLabel == startLabel) then Use endLabel else Use letLabel

-- Reduce non actionable primitives and remove expired
reduceRec :: BlockNumber -> State -> Environment -> Contract -> Contract
reduceRec _ _ _ Null = Null
reduceRec blockNum state env c@(Commit _ _ _ _ timeout_start timeout_end _ continuation) =
  if (isExpired blockNum timeout_start) || (isExpired blockNum timeout_end)
  then reduceRec blockNum state env continuation
  else c
reduceRec blockNum state env c@(Pay _ _ _ _ timeout _ continuation) =
  if isExpired blockNum timeout
  then reduceRec blockNum state env continuation
  else c
reduceRec blockNum state env (Both cont1 cont2) = Both (go cont1) (go cont2)
  where go = reduceRec blockNum state env 
reduceRec blockNum state env (Choice obs cont1 cont2) =
  reduceRec blockNum state env (if (evalObservation blockNum state obs)
                                then cont1
                                else cont2)
reduceRec blockNum state env c@(When obs timeout cont1 cont2) =
  if isExpired timeout blockNum
  then go cont2
  else if evalObservation blockNum state obs
       then go cont1
       else c
  where go = reduceRec blockNum state env 
reduceRec blockNum state env (Scale divid divis def contract) =
  Scale (Constant vsDivid) (Constant vsDivis) (Constant vsDef) (go contract)
  where go = reduceRec blockNum state env 
        vsDivid = evalValue blockNum state divid
        vsDivis = evalValue blockNum state divis
        vsDef = evalValue blockNum state def
reduceRec blockNum state env (While obs timeout contractWhile contractAfter) =
  if isExpired timeout blockNum
  then go contractAfter
  else if evalObservation blockNum state obs
       then (While obs timeout (go contractWhile) contractAfter)
       else go contractAfter
  where go = reduceRec blockNum state env 
reduceRec blockNum state env (Let label boundContract contract) =
  case lookupEnvironment label env of
    Nothing -> let newEnv = addToEnvironment label checkedBoundContract env in
               Let label checkedBoundContract $ reduceRec blockNum state newEnv contract
    Just _ -> let freshKey = getFreshKey env contract in
              let newEnv = addToEnvironment freshKey checkedBoundContract env in
              let fixedContract = relabel label freshKey contract in
              Let freshKey checkedBoundContract $ reduceRec blockNum state newEnv fixedContract
  where checkedBoundContract = nullifyInvalidUses env boundContract
reduceRec blockNum state env (Use label) =
  case lookupEnvironment label env of
    Just contract -> reduceRec blockNum state env contract
    Nothing -> Null

reduce :: BlockNumber -> State -> Contract -> Contract
reduce blockNum state contract =
   reduceRec blockNum state emptyEnvironment contract

-- ToDo: reduce useless primitives to Null
simplify :: Contract -> Contract
simplify contract = contract 

-- How much everybody pays or receives in transaction
type TransactionOutcomes = M.Map Person Integer

emptyOutcome :: TransactionOutcomes
emptyOutcome = M.empty

isEmptyOutcome :: TransactionOutcomes -> Bool
isEmptyOutcome trOut = F.all (== 0) trOut

-- Adds a value to the map of outcomes
addOutcome :: Person -> Integer -> TransactionOutcomes -> TransactionOutcomes
addOutcome person diffValue trOut = M.insert person newValue trOut
  where newValue = case M.lookup person trOut of
                     Just value -> value + diffValue
                     Nothing -> diffValue 

-- Get effect of outcomes on the bank of the contract
outcomeEffect :: TransactionOutcomes -> Integer
outcomeEffect trOut = M.foldl' (-) 0 trOut

-- Add two transaction outcomes together
combineOutcomes :: TransactionOutcomes -> TransactionOutcomes -> TransactionOutcomes
combineOutcomes = M.unionWith (+)

data FetchResult a = Picked a 
                   | NoMatch
                   | MultipleMatches

data DetachedPrimitive = DCommit IdCommit Person Integer Timeout
                       | DPay IdCommit Person Integer

-- Semantics of Scale
scaleValue :: Integer -> Integer -> Integer -> Integer -> Integer 
scaleValue divid divis def val = if (divis == 0) then def else ((val * divid) `div` divis)

scaleResult :: Integer -> Integer -> Integer -> DetachedPrimitive -> DetachedPrimitive
scaleResult divid divis def (DCommit idCommit person val tim) =
  DCommit idCommit person (scaleValue divid divis def val) tim
scaleResult divid divis def (DPay idCommit person val) =
  DPay idCommit person (scaleValue divid divis def val)

-- Find out whether the Action is allowed given the current state
-- and contract, and, if so, pick the corresponding primitive in the contract.
-- Also return the contract without the selected primitive.
fetchPrimitive :: IdAction -> BlockNumber -> State -> Contract
               -> FetchResult (DetachedPrimitive, Contract)
--                                 Remaining contract --^
fetchPrimitive idAction blockNum state (Commit idActionC idCommit person value _ timeout continuation _) =
  if (idAction == idActionC && notCurrentCommit && notExpiredCommit)
  then Picked ((DCommit idCommit person actualValue timeout),
               continuation)
  else NoMatch
  where notCurrentCommit = isCurrentCommit idCommit state
        notExpiredCommit = isExpiredCommit idCommit state
        actualValue = evalValue blockNum state value
fetchPrimitive idAction blockNum state (Pay idActionC idCommit person value _ continuation _) =
  if (idAction == idActionC)
  then Picked ((DPay idCommit person actualValue), continuation)
  else NoMatch
  where actualValue = evalValue blockNum state value
fetchPrimitive idAction blockNum state (Both leftContract rightContract) =
  case (go leftContract, go rightContract) of
     (Picked (result, cont), NoMatch) -> Picked (result, (Both cont rightContract))
     (NoMatch, Picked (result, cont)) -> Picked (result, (Both leftContract cont))
     (NoMatch, NoMatch) -> NoMatch
     _                  -> MultipleMatches
  where go = fetchPrimitive idAction blockNum state 
fetchPrimitive idAction blockNum state (While obs timeout contract1 contract2) =
  case fetchPrimitive idAction blockNum state contract1 of
     Picked (result, cont) -> Picked (result, While obs timeout cont contract2)
     NoMatch -> NoMatch
     MultipleMatches -> MultipleMatches
fetchPrimitive idAction blockNum state (Let label boundContract subContract) =
  case fetchPrimitive idAction blockNum state subContract of
     Picked (result, cont) -> Picked (result, Let label boundContract cont)
     NoMatch -> NoMatch
     MultipleMatches -> MultipleMatches
fetchPrimitive idAction blockNum state (Scale divid divis def subContract) =
  case fetchPrimitive idAction blockNum state subContract of
     Picked (result, cont) -> Picked (scaleResult sDivid sDivis sDef result,
                                      Scale divid divis def cont)
     NoMatch -> NoMatch
     MultipleMatches -> MultipleMatches
  where sDivid = evalValue blockNum state divid
        sDivis = evalValue blockNum state divis
        sDef = evalValue blockNum state def
fetchPrimitive _ _ _ _ = NoMatch

data DynamicProblem = NoProblem
                    | CommitNotMade
                    | NotEnoughMoneyLeftInCommit
                    | CommitIsExpired

data EvaluationResult a = Result a DynamicProblem
                        | InconsistentState -- This should not happen when using fetchPrimitive result

-- Evaluation of actionable input
eval :: DetachedPrimitive -> State -> EvaluationResult (TransactionOutcomes, State)
eval (DCommit idCommit person value timeout) state =
  if (isCurrentCommit idCommit state) || (isExpiredCommit idCommit state)
  then InconsistentState
  else Result ( addOutcome person (- value) emptyOutcome
              , addCommit idCommit person value timeout state )
              NoProblem
eval (DPay idCommit person value) state = 
  if (not $ isCurrentCommit idCommit state)
  then (if (not $ isExpiredCommit idCommit state)
        then Result (emptyOutcome, state) CommitNotMade
        else Result (emptyOutcome, state) CommitIsExpired)
  else (if value > maxValue
        then Result ( addOutcome person maxValue emptyOutcome
                    , fromJust $ discountAvailableMoneyFromCommit idCommit maxValue state )
                    NotEnoughMoneyLeftInCommit
        else Result ( addOutcome person value emptyOutcome
                    , fromJust $ discountAvailableMoneyFromCommit idCommit value state )
                    NoProblem)
  where maxValue = getAvailableAmountInCommit idCommit state

-- Check whether the person who must sign has signed
areActionPermissionsValid :: DetachedPrimitive -> S.Set Person -> Bool
areActionPermissionsValid (DCommit _ person _ _) sigs = person `S.member` sigs
areActionPermissionsValid (DPay _ person _) sigs = person `S.member` sigs

areInputPermissionsValid :: Input -> S.Set Person -> Bool
areInputPermissionsValid (IChoice (_, person) _) sigs = person `S.member` sigs
areInputPermissionsValid (IOracle _ _ _) _ = True -- Implementation ToDo: need to check signature 

-- Check whether a commit or payment has negative value
isTransactionNegative :: DetachedPrimitive -> Bool
isTransactionNegative (DCommit _ _ val _) = val < 0
isTransactionNegative (DPay _ _ val) = val < 0

data ErrorResult = InvalidInput
                 | NoValidSignature
                 | NegativeTransaction
                 | AmbiguousId
                 | InternalError -- This should not happen

data ApplicationResult a = SuccessfullyApplied a DynamicProblem
                         | CouldNotApply ErrorResult

-- High level wrapper that calls the appropriate update function on contract and state.
-- Does not take care of reducing, that must be done before and after applyAnyInput.
applyAnyInput :: AnyInput -> S.Set Person -> S.Set IdInput -> BlockNumber -> State -> Contract -> ApplicationResult (TransactionOutcomes, State, Contract)
applyAnyInput anyInput sigs neededInputs blockNum state contract = 
  case addAnyInput blockNum anyInput neededInputs state of
    Just updatedState ->
      case anyInput of
        Input input ->
          if areInputPermissionsValid input sigs
          then SuccessfullyApplied ( emptyOutcome
                                   , updatedState
                                   , contract )
                                   NoProblem
          else CouldNotApply NoValidSignature 
        Action idAction ->
          case fetchPrimitive idAction blockNum updatedState contract of
            Picked (primitive, newContract) ->
              case eval primitive updatedState of
                Result (transactionOutcomes, newState) dynamicProblem ->
                  if isTransactionNegative primitive
                  then CouldNotApply NegativeTransaction
                  else if areActionPermissionsValid primitive sigs
                       then SuccessfullyApplied (transactionOutcomes,
                                                 newState,
                                                 newContract) dynamicProblem
                       else CouldNotApply NoValidSignature 

                InconsistentState -> CouldNotApply InternalError 
            NoMatch -> CouldNotApply InvalidInput
            MultipleMatches -> CouldNotApply AmbiguousId
    Nothing -> CouldNotApply InvalidInput

-- Give redeemed money to owners
redeemMoneyLoop :: [Person] -> TransactionOutcomes -> State
                -> Maybe (TransactionOutcomes, State)
redeemMoneyLoop [] trOut state = Just (trOut, state)
redeemMoneyLoop (h:t) trOut state =
  redeemMoneyLoop t (addOutcome h redeemed trOut) newState
   where redeemed = getRedeemedForPerson h state
         newState = resetRedeemedForPerson h state

redeemMoney :: S.Set Person -> State -> Maybe (TransactionOutcomes, State)
redeemMoney sigs state = redeemMoneyLoop (S.toList sigs) emptyOutcome state

data MApplicationResult a = MSuccessfullyApplied a [DynamicProblem]
                          | MCouldNotApply ErrorResult

-- Fold applyAnyInput through a list of AnyInputs.
-- Check that balance is positive at every step
-- In the last step: simplify 
applyAnyInputs :: [AnyInput] -> S.Set Person -> S.Set IdInput -> BlockNumber -> State -> Contract
                  -> Integer -- Available funds in the contract
                  -> TransactionOutcomes
                  -> [DynamicProblem]
                  -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
applyAnyInputs [] sigs _ _ state contract value trOut dynProbList =
  case redeemMoney sigs state of
    Just (currTrOut, newState) ->
      let newValue = value + outcomeEffect currTrOut in
      if newValue < 0
      then MCouldNotApply InternalError
      else let newTrOut = combineOutcomes currTrOut trOut in
           let simplifiedContract = simplify contract in
           MSuccessfullyApplied (newValue, newTrOut, newState, simplifiedContract) dynProbList
    Nothing -> MCouldNotApply InternalError
applyAnyInputs (h:t) sigs neededInputs blockNum state contract value trOut dynProbList =
  case applyAnyInput h sigs neededInputs blockNum state contract of
    SuccessfullyApplied (currTrOut, newState, newContract) newDynProb ->
      let newValue = value + outcomeEffect currTrOut in
      if newValue < 0
      then MCouldNotApply InternalError
      else let newTrOut = combineOutcomes currTrOut trOut in
           let reducedNewContract = reduce blockNum newState newContract in
           applyAnyInputs t sigs neededInputs blockNum newState reducedNewContract newValue newTrOut
                          (dynProbList ++ [newDynProb])
    CouldNotApply currError -> MCouldNotApply currError

-- Expire commits and apply applyAnyInputs
applyTransaction :: [AnyInput] -> S.Set Person -> BlockNumber -> State -> Contract
                    -> Integer -- Available funds in the contract 
                    -> MApplicationResult (Integer, TransactionOutcomes, State, Contract)
applyTransaction inputs sigs blockNum state contract value =
  case appResult of
    MSuccessfullyApplied (_, tranOut, _, _) _ ->
        if (inputs == []) && (reducedContract == contract) && (isEmptyOutcome tranOut)
        then MCouldNotApply InvalidInput
        else appResult
    _ -> appResult
  where neededInputs = collectNeededInputsFromContract contract
        expiredState = expireCommits blockNum state
        reducedContract = reduce blockNum expiredState contract
        appResult = applyAnyInputs inputs sigs neededInputs blockNum expiredState
                                   reducedContract value emptyOutcome []


-- NOTE: in implementation it must be checked that oracle values are signed by the oracle

