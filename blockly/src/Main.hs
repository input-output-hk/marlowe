module Main where

import qualified Haste.Foreign as F
import qualified Haste.JSString as J
import qualified Haste.Prim as P
import qualified Haste.DOM as D
import qualified DepositIncentive as DI
import qualified CrowFunding as CF
import qualified Escrow as E
import Semantics
import ContractFormatter
import SmartInputs
import qualified Data.Maybe as M
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Control.Monad as Monad

data Block = Block P.JSAny
data BInput = BInput P.JSAny
data FieldRow = FieldRow P.JSAny

render :: IO ()
render = (F.ffi (J.pack "(function() { demoWorkspace.render(); onresize(); })"))

get_root :: IO Block
get_root = do x <- (F.ffi (J.pack "(function() {return (demoWorkspace.getAllBlocks()[0]);})"))
              return $ Block x

create_block :: String -> IO Block
create_block str = do x <- (F.ffi (J.pack "(function (x) {var c = demoWorkspace.newBlock(x); c.initSvg(); return c;})")) (P.toJSStr str)
                      return $ Block x

-- get name

get_name :: P.JSAny -> IO String
get_name x = F.ffi (J.pack "(function (x) { return x.name; })") x

get_input_name :: BInput -> IO String
get_input_name (BInput x) = get_name x

get_fieldrow_name :: FieldRow -> IO String
get_fieldrow_name (FieldRow x) = get_name x 

-- get input list

get_input_list_length :: Block -> IO Int
get_input_list_length (Block b) = F.ffi (J.pack "(function (b) { return (b.inputList.length); })") b

get_input_list_element :: Block -> Int -> IO BInput
get_input_list_element (Block b) x = do r <- F.ffi (J.pack "(function (b, x) { return (b.inputList[x]); })") b x
                                        return $ BInput r

get_input_list_aux :: Block -> [Int] -> IO [BInput]
get_input_list_aux b [] = return []
get_input_list_aux b (h:t) = do el <- get_input_list_element b h
                                rest <- get_input_list_aux b t
                                return (el:rest)

get_input_list :: Block -> IO [BInput]
get_input_list b = do len <- get_input_list_length b
                      il <- get_input_list_aux b [0..(len - 1)]
                      return il
-- get input with name

get_input_with_name :: String -> [BInput] -> IO BInput
get_input_with_name str [] = error ("No input matches \"" ++ str ++ "\"")
get_input_with_name str (h:t) =
  do x <- get_input_name h
     if (x == str) then return h else get_input_with_name str t

-- connect as input

connect_to_previous :: Block -> BInput -> IO ()
connect_to_previous (Block y) (BInput ip) =
  F.ffi (J.pack "(function (y, ip) {y.previousConnection.connect(ip.connection);})") y ip

connect_to_output :: Block -> BInput -> IO ()
connect_to_output (Block y) (BInput ip) =
  F.ffi (J.pack "(function (y, ip) {y.outputConnection.connect(ip.connection);})") y ip

connect_as_input :: String -> Block -> Block -> IO ()
connect_as_input str p y =
  do il <- get_input_list p
     ip <- get_input_with_name str il
     connect_to_previous y ip

connect_obs_as_input :: String -> Block -> Block -> IO ()
connect_obs_as_input str p y =
  do il <- get_input_list p
     ip <- get_input_with_name str il
     connect_to_output y ip

connect_value_as_input :: String -> Block -> Block -> IO ()
connect_value_as_input str p y =
  do il <- get_input_list p
     ip <- get_input_with_name str il
     connect_to_output y ip



-- get fieldrow list

get_fieldrow_list_length :: BInput -> IO Int
get_fieldrow_list_length (BInput b) = F.ffi (J.pack "(function (b) { return (b.fieldRow.length); })") b

get_fieldrow_list_element :: BInput -> Int -> IO FieldRow
get_fieldrow_list_element (BInput b) x = do r <- F.ffi (J.pack "(function (b, x) { return (b.fieldRow[x]); })") b x
                                            return $ FieldRow r

get_fieldrow_list_aux :: BInput -> [Int] -> IO [FieldRow]
get_fieldrow_list_aux b [] = return []
get_fieldrow_list_aux b (h:t) = do el <- get_fieldrow_list_element b h
                                   rest <- get_fieldrow_list_aux b t
                                   return (el:rest)

get_fieldrow_list :: BInput -> IO [FieldRow]
get_fieldrow_list b = do len <- get_fieldrow_list_length b
                         il <- get_fieldrow_list_aux b [0..(len - 1)]
                         return il

-- get fieldrow with name

get_fieldrow_with_name :: String -> [FieldRow] -> IO FieldRow
get_fieldrow_with_name str [] = error ("No fieldrow matches \"" ++ str ++ "\"")
get_fieldrow_with_name str (h:t) =
  do x <- get_fieldrow_name h
     if (x == str) then return h else get_fieldrow_with_name str t

get_fieldrow_with_name_from_block :: String -> Block -> IO FieldRow
get_fieldrow_with_name_from_block str b =
  do il <- (get_input_list b :: IO [BInput])
     frl <- ((mapM (get_fieldrow_list) il) :: IO [[FieldRow]])
     get_fieldrow_with_name str (concat frl)

-- setText

set_fieldrow_text :: FieldRow -> String -> IO ()
set_fieldrow_text (FieldRow b) s = F.ffi (J.pack "(function (b, s) { return (b.setText(s)); })") b s

set_field_value :: Block -> String -> Int -> IO ()
set_field_value b n v =
  do fr <- get_fieldrow_with_name_from_block n b
     set_fieldrow_text fr (show v)


-- money to Blockly
money_to_blockly :: Money -> IO Block
money_to_blockly (AvailableMoney (IdentCC id)) =
  do tb <- create_block "value_available_money"
     set_field_value tb "commit_id" id
     return tb
money_to_blockly (AddMoney v1 v2) =
  do vb1 <- money_to_blockly v1
     vb2 <- money_to_blockly v2
     tb <- create_block "value_add_money"
     connect_value_as_input "value1" tb vb1
     connect_value_as_input "value2" tb vb2
     return tb
money_to_blockly (ConstMoney cv) =
  do tb <- create_block "value_const_money"
     set_field_value tb "money" cv
     return tb
money_to_blockly (MoneyFromChoice (IdentChoice ic) per mon) =
  do monb <- money_to_blockly mon
     tb <- create_block "money_from_choice"
     set_field_value tb "choice_id" ic
     set_field_value tb "person_id" per
     connect_value_as_input "default" tb monb
     return tb

-- block to blockly

obs_to_blockly :: Observation -> IO Block
obs_to_blockly (ValueGE v1 v2) =
  do vb1 <- money_to_blockly v1
     vb2 <- money_to_blockly v2
     tb <- create_block "observation_value_ge"
     connect_value_as_input "value1" tb vb1
     connect_value_as_input "value2" tb vb2
     return tb
obs_to_blockly (AndObs obs1 obs2) =
  do ob1 <- obs_to_blockly obs1
     ob2 <- obs_to_blockly obs2
     tb <- create_block "observation_andobs"
     connect_obs_as_input "observation1" tb ob1
     connect_obs_as_input "observation2" tb ob2
     return tb
obs_to_blockly (BelowTimeout b) =
  do tb <- create_block "observation_belowtimeout"
     set_field_value tb "block_number" b
     return tb
obs_to_blockly FalseObs =
  do tb <- create_block "observation_falseobs"
     return tb
obs_to_blockly (NotObs obs) =
  do ob <- obs_to_blockly obs
     tb <- create_block "observation_notobs"
     connect_obs_as_input "observation" tb ob
     return tb
obs_to_blockly (OrObs obs1 obs2) =
  do ob1 <- obs_to_blockly obs1
     ob2 <- obs_to_blockly obs2
     tb <- create_block "observation_orobs"
     connect_obs_as_input "observation1" tb ob1
     connect_obs_as_input "observation2" tb ob2
     return tb
obs_to_blockly (PersonChoseSomething (IdentChoice id) p) =
  do tb <- create_block "observation_personchosesomething"
     set_field_value tb "choice_id" id
     set_field_value tb "person" p
     return tb
obs_to_blockly (PersonChoseThis (IdentChoice id) p cv) =
  do tb <- create_block "observation_personchosethis"
     set_field_value tb "choice_id" id
     set_field_value tb "person" p
     set_field_value tb "choice_value" cv
     return tb
obs_to_blockly TrueObs =
  do tb <- create_block "observation_trueobs"
     return tb

block_to_blockly :: Contract -> IO Block
block_to_blockly (Null) = create_block "contract_null"
block_to_blockly (RedeemCC (IdentCC id) c) =
  do cb <- block_to_blockly c
     tb <- create_block "contract_redeemcc"
     set_field_value tb "ccommit_id" id
     connect_as_input "contract" tb cb
     return tb
block_to_blockly (Pay (IdentPay ip) p1 p2 cash expi c) =
  do cb <- block_to_blockly c
     tb <- create_block "contract_pay"
     cashb <- money_to_blockly cash
     set_field_value tb "pay_id" ip
     set_field_value tb "payer_id" p1
     set_field_value tb "payee_id" p2
     connect_value_as_input "ammount" tb cashb
     set_field_value tb "expiration" expi
     connect_as_input "contract" tb cb
     return tb
block_to_blockly (Both c1 c2) =
  do cb1 <- block_to_blockly c1
     cb2 <- block_to_blockly c2
     tb <- create_block "contract_both"
     connect_as_input "contract1" tb cb1
     connect_as_input "contract2" tb cb2
     return tb
block_to_blockly (Choice obs c1 c2) =
  do obb <- obs_to_blockly obs
     cb1 <- block_to_blockly c1
     cb2 <- block_to_blockly c2
     tb <- create_block "contract_choice"
     connect_obs_as_input "observation" tb obb
     connect_as_input "contract1" tb cb1
     connect_as_input "contract2" tb cb2
     return tb
block_to_blockly (CommitCash (IdentCC id) p cash b1 b2 c1 c2) =
  do cb1 <- block_to_blockly c1
     cb2 <- block_to_blockly c2
     cashb <- money_to_blockly cash
     tb <- create_block "contract_commitcash"
     set_field_value tb "ccommit_id" id
     set_field_value tb "person_id" p
     connect_value_as_input "ammount" tb cashb
     set_field_value tb "start_expiration" b1
     set_field_value tb "end_expiration" b2
     connect_as_input "contract1" tb cb1
     connect_as_input "contract2" tb cb2
     return tb
block_to_blockly (When obs b c1 c2) =
  do obb <- obs_to_blockly obs
     cb1 <- block_to_blockly c1
     cb2 <- block_to_blockly c2
     tb <- create_block "contract_when"
     set_field_value tb "timeout" b
     connect_obs_as_input "observation" tb obb
     connect_as_input "contract1" tb cb1
     connect_as_input "contract2" tb cb2
     return tb

-- clearWorkspace
clear_workspace :: IO ()
clear_workspace = F.ffi (J.pack "(function () {var i; var b = demoWorkspace.getAllBlocks(); for (i = b.length - 1; i > 0; --i) { if (b[i] !== undefined) { b[i].dispose() } };})") 

set_text :: String -> String -> IO ()
set_text t str = F.ffi (J.pack "(function (t, s) {document.getElementById(t).value = s})") t str 

get_text :: String -> IO (String)
get_text t = F.ffi (J.pack "(function (t) {return document.getElementById(t).value})") t

set_code :: String -> IO ()
set_code = set_text "codeArea" 

get_code :: IO String
get_code = get_text "codeArea" 

-- block num

set_blocknum :: Int -> IO ()
set_blocknum = (set_text "currBlock") . show

get_blocknum :: IO Int
get_blocknum = do txt <- (get_text "currBlock")
                  return $ read txt

-- state

state_serial :: State -> ([(IdentCC, CCStatus)], [((IdentChoice, Person), ConcreteChoice)])
state_serial (State {sc = scv, sch = schv}) = (Map.toList scv, Map.toList schv)

state_unserial :: ([(IdentCC, CCStatus)], [((IdentChoice, Person), ConcreteChoice)]) -> State
state_unserial (scv, schv) = State {sc = Map.fromList scv, sch = Map.fromList schv}

get_state_text :: IO (String)
get_state_text = get_text "contractState"

set_state_text :: String -> IO ()
set_state_text = set_text "contractState"

get_state :: IO State
get_state = Monad.liftM (state_unserial . read) get_state_text

set_state :: State -> IO () 
set_state = set_state_text . show . state_serial

-- input

input_serial :: Input -> ([CC], [RC], [((IdentPay, Person), Cash)], [((IdentChoice, Person), ConcreteChoice)])
input_serial (Input {cc = ccv, rc = rcv, rp = rpv, ic = icv})
   = (Set.toList ccv, Set.toList rcv, Map.toList rpv, Map.toList icv)

input_unserial :: ([CC], [RC], [((IdentPay, Person), Cash)], [((IdentChoice, Person), ConcreteChoice)]) -> Input
input_unserial (ccv, rcv, rpv, icv) = Input {cc = Set.fromList ccv, rc = Set.fromList rcv, rp = Map.fromList rpv, ic = Map.fromList icv}

get_input_text :: IO (String)
get_input_text = get_text "contractInput"

set_input_text :: String -> IO ()
set_input_text = set_text "contractInput"

get_input :: IO Input
get_input = Monad.liftM (input_unserial . read) get_input_text

set_input :: Input -> IO () 
set_input = set_input_text . show . input_serial

-- output

get_output_text :: IO (String)
get_output_text = get_text "contractOutput"

set_output_text :: String -> IO ()
set_output_text = set_text "contractOutput"

get_output :: IO AS
get_output = Monad.liftM (read) get_output_text

set_output :: AS -> IO () 
set_output = set_output_text . show


-- clear

clear_everything :: IO ()
clear_everything = do clear_workspace
                      set_code ""
                      set_blocknum 0
                      set_state_text "([], [])"
                      set_input_text "([], [], [], [])"
                      set_output_text ""

-- examples
depositIncentive = do clear_everything
                      code_to_contract DI.depositIncentive
                      c2b 

crowdFunding = do clear_everything
                  code_to_contract CF.crowdFunding
                  c2b

escrow = do clear_everything
            code_to_contract E.escrow
            c2b

-- workspace to code
workspace_to_code_aux :: IO (String)
workspace_to_code_aux = F.ffi (J.pack "(function () {return Blockly.Marlowe.workspaceToCode(demoWorkspace);})")

workspace_to_code :: IO (String)
workspace_to_code = do rough_code <- workspace_to_code_aux
                       return (prettyPrintContract ((read rough_code) :: Contract))

workspace_to_contract :: IO Contract
workspace_to_contract = do rough_code <- workspace_to_code_aux
                           return (read rough_code)

code_to_contract :: Contract -> IO ()
code_to_contract contr = do set_code (prettyPrintContract contr)

-- blockly to code

b2c :: IO ()
b2c = do code <- workspace_to_code
         set_code code
         refreshActions

-- code to blockly

c2b :: IO ()
c2b = do code <- get_code
         clear_workspace
         root <- get_root
         blk <- let contract = read code :: Contract in block_to_blockly contract
         connect_as_input "base_contract" root blk
         render
         refreshActions

-- input addition

commit :: Int -> Int -> Int -> Int -> IO ()
commit per cash id exp =
  do inp <- get_input
     set_input (inp {cc = Set.insert (CC (IdentCC id) per cash exp) (cc inp)})
     refreshActions

redeem :: Int -> Int -> Int -> IO ()
redeem per cash id =
  do inp <- get_input
     set_input (inp {rc = Set.insert (RC (IdentCC id) per cash) (rc inp)})
     refreshActions

claim :: Int -> Int -> Int -> IO ()
claim per cash id =
  do inp <- get_input
     set_input (inp {rp = Map.insert (IdentPay id, per) cash (rp inp)})
     refreshActions

choose :: Int -> Int -> Int -> IO ()
choose per choice id =
  do inp <- get_input
     set_input (inp {ic = Map.insert (IdentChoice id, per) choice (ic inp)})
     refreshActions

-- execute
execute :: IO ()
execute = 
  do inp <- get_input
     st <- get_state
     contr <- workspace_to_contract
     blk <- get_blocknum
     let (nst, ncontr, outp) = computeAll inp st contr (OS {random = 42, blockNumber = blk}) in do {set_output outp;
                         code_to_contract ncontr;
                         set_state nst;
                         set_input_text "([], [], [], [])";
                         set_blocknum (blk + 1);
                         c2b;
                         refreshActions}

deleteChildNodes :: String -> IO ()
deleteChildNodes = F.ffi (J.pack "(function (x) { var node = document.getElementById(x); while (node.hasChildNodes()) { node.removeChild(node.lastChild); } })")

insertNormalAction :: String -> String -> IO ()
insertNormalAction = F.ffi (J.pack "(function (x, y) {var r = document.getElementById('actions').insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x)); var c2 = r.insertCell(); var btn = document.createElement('button'); c2.appendChild(btn); btn.appendChild(document.createTextNode('Add action')); btn.style.setProperty('width', '100%'); btn.onclick = function () {Haste.addAction(y);};})")

insertActionWithNum :: String -> String -> String -> IO ()
insertActionWithNum = F.ffi (J.pack "(function (x, y, z) {var a = document.getElementById('actions'); var r = a.insertRow(); var c1 = r.insertCell(); c1.appendChild(document.createTextNode(x + ' ')); var input = document.createElement('input'); input.type = 'number'; var ch = 'ibox' + a.childNodes.length; input.id = ch; input.value = 0; input.style.setProperty('width', '5em'); c1.appendChild(input); c1.appendChild(document.createTextNode(' ' + y)); var c2 = r.insertCell(); var btn = document.createElement('button'); c2.appendChild(btn); btn.appendChild(document.createTextNode('Add action')); btn.style.setProperty('width', '100%'); btn.onclick = function () {Haste.addActionWithNum(z, document.getElementById(ch).value);};})")

data SmartInput = SICC IdentCC Person Cash Timeout
                | SIRC IdentCC Person Cash
                | SIP IdentPay Person Cash
               deriving (Eq,Ord,Show,Read)

addCommitInputs :: CC -> IO ()
addCommitInputs (CC ide@(IdentCC identcc) per cash tim)
 = insertNormalAction ("P" ++ (show per) ++ ": Make commit (with id: "
                       ++ (show identcc) ++ ") of " ++ (show cash) ++
                       " ADA expiring on: " ++ (show tim)) (show $ SICC ide per cash tim)

addRedeemInputs :: RC -> IO ()
addRedeemInputs (RC ide@(IdentCC identcc) per cash)
 = insertNormalAction ("P" ++ (show per) ++ ": Redeem " ++ (show cash) ++
                       " ADA from commit (with id: " ++ (show identcc) ++
                       ")") (show $ SIRC ide per cash)

addPayInputs :: ((IdentPay, Person), Cash) -> IO ()
addPayInputs ((ide@(IdentPay identpay), per), cash)
 = insertNormalAction ("P" ++ (show per) ++ ": Claim payment (with id: "
                       ++ (show identpay) ++ ") of " ++ (show cash) ++
                       " ADA") (show $ SIP ide per cash)

addChoiceInputs :: ((IdentChoice, Person), ConcreteChoice) -> IO ()
addChoiceInputs (pair@(IdentChoice identchoice, per), _)
 = insertActionWithNum ("P" ++ (show per) ++ ": Choose")
                       ("for choice with id " ++ (show identchoice)) (show pair)

addInputs :: Input -> IO ()
addInputs Input {cc = cci, rc = rci,
                 rp = rpi, ic = ici}
 = do mapM_ addCommitInputs (Set.toList cci)
      mapM_ addRedeemInputs (Set.toList rci)
      mapM_ addPayInputs (Map.toList rpi)
      mapM_ addChoiceInputs (Map.toList ici)

refreshActions :: IO ()
refreshActions = do inputs <- get_input
                    contr <- workspace_to_contract
                    blk <- get_blocknum
                    stat <- get_state
                    let os = OS {random = 42, blockNumber = blk}
                    deleteChildNodes "actions"
                    addInputs (getPossibleInputs os inputs contr stat)

addAction :: String -> IO ()
addAction x = case (read x) :: SmartInput of
                   SICC (IdentCC ide) per cash tim -> commit per cash ide tim
                   SIRC (IdentCC ide) per cash -> redeem per cash ide
                   SIP (IdentPay ide) per cash -> claim per cash ide

addActionWithNum :: String -> Int -> IO ()
addActionWithNum x ch = choose per ch ide
  where (IdentChoice ide, per) = (read x) :: (IdentChoice, Person)

-- alert

alert :: String -> IO ()
alert = F.ffi (J.pack "(function (x) { alert(x) ; })")

-- main

main :: IO ()
main = do c2b
          F.export (J.pack "clear_workspace") clear_everything
          F.export (J.pack "b2c") b2c
          F.export (J.pack "c2b") c2b 
          F.export (J.pack "commit") commit
          F.export (J.pack "redeem") redeem
          F.export (J.pack "claim") claim
          F.export (J.pack "choose") choose
          F.export (J.pack "execute") execute
          F.export (J.pack "refreshActions") refreshActions
          F.export (J.pack "addAction") addAction
          F.export (J.pack "addActionWithNum") addActionWithNum
          F.export (J.pack "depositIncentive") depositIncentive
          F.export (J.pack "crowdFunding") crowdFunding
          F.export (J.pack "escrow") escrow
          refreshActions
          return ()


