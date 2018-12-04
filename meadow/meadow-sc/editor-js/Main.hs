{-# LANGUAGE ForeignFunctionInterface #-}
-- | Main compiler executable.

module Main where

import GHCJS.Types (JSVal)
import Data.JSString (JSString, pack, unpack)
import GHCJS.Foreign (fromJSBool, toJSBool)
import GHCJS.Foreign.Callback (Callback, asyncCallback)

foreign import javascript safe
   "try { eval($1); } catch (err) { textarea.setValue('Error while executing Haskell code:\\n\\n' + err); textarea.setOption('mode', 'text/plain'); textarea.setOption('lineWrapping', true); }"
   evalAux :: JSString -> IO ()
eval = evalAux . pack

foreign import javascript safe
  "document.getElementById($1).onclick = $2;"
  setOnClickAux :: JSString -> Callback (IO ()) -> IO ()
setOnClick i c = do ac <- asyncCallback c
                    setOnClickAux (pack i) ac

foreign import javascript safe
  "document.getElementById($1).disabled = false;"
  enableButtonAux :: JSString -> IO ()
enableButton i = enableButtonAux (pack i)

foreign import javascript safe
  "document.getElementById($1).disabled = true;"
  disableButtonAux :: JSString -> IO ()
disableButton i = disableButtonAux (pack i)

foreign import javascript safe
  "alert($1);"
  alertAux :: JSString -> IO ()
alert s = alertAux (pack s)

foreign import javascript safe
  "myCodeMirror.setValue($1);"
   setCodeMirrorValueAux :: JSString -> IO ()
setCodeMirrorValue v = setCodeMirrorValueAux (pack v)

foreign import javascript safe
  "textarea.setValue($1);"
  setCodeMirrorValueAux2 :: JSString -> IO ()
setCodeMirrorValue2 v = setCodeMirrorValueAux2 (pack v)

foreign import javascript safe
  "textarea.setOption('mode', $1);"
  setCodeMirrorModeAux2 :: JSString -> IO ()
setCodeMirrorMode2 v = setCodeMirrorModeAux2 (pack v)

foreign import javascript safe
  "textarea.setOption('lineWrapping', $1);"
  setCodeMirrorWrappingAux2 :: JSVal -> IO ()
setCodeMirrorWrapping2 v = setCodeMirrorWrappingAux2 (toJSBool v)

setCodeMirror2Highlight = do setCodeMirrorMode2 "text/x-haskell"
                             setCodeMirrorWrapping2 False
setCodeMirror2Plain = do setCodeMirrorMode2 "text/plain"
                         setCodeMirrorWrapping2 True

foreign import javascript safe
  "document.getElementById($1).value = $2;"
   setValueAux :: JSString -> JSString -> IO ()
setValue i v = setValueAux (pack i) (pack v)

foreign import javascript safe
  "parent[$1].setValue($2);"
   setValueParentAux :: JSString -> JSString -> IO ()
setValueParent i v = setValueParentAux (pack i) (pack v)

foreign import javascript safe
  "$r = myCodeMirror.getValue();"
   getCodeMirrorValueAux :: IO JSString
getCodeMirrorValue = do r <- getCodeMirrorValueAux
                        return (unpack r)

foreign import javascript safe
  "$r = textarea.getValue();"
  getCodeMirrorValueAux2 :: IO JSString
getCodeMirrorValue2 = do r <- getCodeMirrorValueAux2
                         return (unpack r)

foreign import javascript safe
  "$r = document.getElementById($1).value;"
   getValueAux :: JSString -> IO JSString
getValue i = do r <- getValueAux (pack i)
                return (unpack r)

foreign import javascript safe
  "$r = parent[$1].getValue();"
   getValueParentAux :: JSString -> IO JSString
getValueParent i = do r <- getValueParentAux (pack i)
                      return (unpack r)

foreign import javascript safe
  "parent.document.getElementById('iframe').remove();"
  destroyIFrame :: IO ()

foreign import javascript safe
  "parent.document.getElementById('c2b').click();"
  codeToBlockly :: IO ()

foreign import javascript safe
  "parent.document.getElementById('iframe').style.display = 'none';"
  hideIFrame :: IO ()

foreign import javascript safe
    "var element = document.createElement('a'); \
    \element.setAttribute('href', 'data:text/plain;charset=utf-8,' + encodeURIComponent($1)); \
    \element.setAttribute('download', $2); \
    \element.style.display = 'none'; \
    \document.body.appendChild(element); \
    \element.click(); \
    \document.body.removeChild(element);"
  downloadFileAux :: JSString -> JSString -> IO ()
downloadFile :: String -> String -> IO ()
downloadFile content name = downloadFileAux (pack content) (pack name)

foreign import javascript safe
    "        function handleFileSelect(evt) { \
    \            var files = evt.target.files; \
    \            var reader = new FileReader(); \
    \              reader.onload = (function(theFile) { \
    \                return function(e) { \
    \                  myCodeMirror.setValue(e.target.result); \
    \                }; \
    \              })(files[0]); \
    \              reader.readAsText(files[0]); \
    \        }; \
    \        var input = $(document.createElement(\"input\")); \
    \        input.attr(\"type\", \"file\"); \
    \        input.attr(\"accept\", \".hs\"); \
    \        input.change(handleFileSelect); \
    \        input.trigger(\"click\");"
  uploadFile :: IO ()

foreign import javascript safe
    "if (window.File && window.FileReader && window.FileList && window.Blob) { $r = true; } else { $r = false; };"
  isUploadSupportedAux :: IO JSVal
isUploadSupported :: IO Bool
isUploadSupported = do b <- isUploadSupportedAux
                       return (fromJSBool b)

foreign import javascript safe
    "$.ajax({ \
    \         url: \"/run\", \
    \         method: \"POST\", \
    \         data: $1, \
    \         dataType: \"text\", \
    \         contentType: \"text/plain;charset=utf-8\", \
    \         error: function (request, status, error) { \
    \                  textarea.setValue(\"Error connecting to server!\\n\"); \
    \                  textarea.setOption('mode', 'text/plain'); \
    \                  textarea.setOption('lineWrapping', true); \
    \                  document.getElementById(\"compile\").disabled = false; \
    \                  document.getElementById(\"reset\").disabled = false; \
    \                  document.getElementById(\"example\").disabled = false; \
    \                  if (window.File && window.FileReader && window.FileList && window.Blob) { document.getElementById(\"upload\").disabled = false; }; \
    \                  document.getElementById(\"minimise\").disabled = false; \
    \                  document.getElementById(\"cancel\").disabled = false; } \
    \       }).done(function (data) { \
    \                  textarea.setValue(data.replace(new RegExp(\"^[A-Z]*: \"), \"\")); \
    \                  if (data.startsWith(\"GOOD: \")) { \
    \                     document.getElementById(\"submit\").disabled = false; \
    \                     textarea.setOption('mode', 'text/x-haskell'); \
    \                     textarea.setOption('lineWrapping', true); \
    \                  } else { \
    \                     textarea.setOption('mode', 'text/plain'); \
    \                     textarea.setOption('lineWrapping', true); \
    \                  } \
    \                  document.getElementById(\"compile\").disabled = false; \
    \                  document.getElementById(\"reset\").disabled = false; \
    \                  document.getElementById(\"example\").disabled = false; \
    \                  if (window.File && window.FileReader && window.FileList && window.Blob) { document.getElementById(\"upload\").disabled = false; }; \
    \                  document.getElementById(\"minimise\").disabled = false; \
    \                  document.getElementById(\"cancel\").disabled = false; \
    \               });"
  sendCompileAux :: JSString -> IO ()
sendCompile :: String -> IO ()
sendCompile content = sendCompileAux (pack content)

compile :: IO ()
compile = do setCodeMirrorValue2 "Compiling..."
             setCodeMirror2Plain
             disableButton "compile"
             disableButton "reset"
             disableButton "submit"
             disableButton "example"
             disableButton "upload"
             disableButton "cancel"
             y <- getCodeMirrorValue
             sendCompile y

embedCode :: [String] -> String
embedCode [] = prefix
embedCode (h:t) = (prefix ++ (h ++ "\n")) ++ (unlines (map ((take 11 $ repeat ' ') ++) t))

reset :: IO ()
reset = do x <- getValueParent "codeArea"
           setCodeMirrorValue $ embedCode $ lines x
           setCodeMirrorValue2 explanation
           setCodeMirror2Plain
           disableButton "submit"

submit :: IO ()
submit = do x <- getCodeMirrorValue2
            setValueParent "codeArea" x
            codeToBlockly

download :: IO ()
download = do c <- getCodeMirrorValue
              downloadFile c "MyContract.hs" 

upload :: IO ()
upload = return ()

minimise :: IO ()
minimise = hideIFrame

cancel :: IO ()
cancel = destroyIFrame 

example :: IO ()
example = setCodeMirrorValue exampleCode

main :: IO ()
main = do setOnClick "compile" compile 
          setOnClick "reset" reset 
          setOnClick "example" example
          setOnClick "submit" submit
          setOnClick "download" download
          setOnClick "upload" uploadFile
          setOnClick "minimise" minimise
          setOnClick "cancel" cancel 
          enableButton "compile"
          enableButton "reset"
          enableButton "example"
          enableButton "download"
          ies <- isUploadSupported
          if (ies) then enableButton "upload" else (return ())
          enableButton "minimise"
          enableButton "cancel"
          reset

prefix = "module MyContract(contract) where\n\nimport Marlowe\n\n-------------------------------------\n-- Write your code below this line --\n-------------------------------------\n\ncontract :: Contract\ncontract = " 

exampleCode = "module MyContract(contract) where\n\nimport Marlowe\n\n-------------------------------------\n-- Write your code below this line --\n-------------------------------------\n\n-- Escrow example using embedding\n\ncontract :: Contract\ncontract = CommitCash iCC1 alice\n                      (ConstMoney 450)\n                      10 100\n                      (When (OrObs (majority_chose refund)\n                                   (majority_chose pay))\n                            90\n                            (Choice (majority_chose pay)\n                                    (Pay iP1 alice bob\n                                         (AvailableMoney iCC1)\n                                         100\n                                         redeem_original)\n                                    redeem_original)\n                            redeem_original)\n                      Null\n    where majority_chose = two_chose alice bob carol\n\n-- Participants\n\nalice, bob, carol :: Person\nalice = 1\nbob = 2\ncarol = 3\n\n-- Possible votes \n\nrefund, pay :: ConcreteChoice\nrefund = 0\npay = 1\n\n-- Vote counting\n\nchose :: Integer -> ConcreteChoice -> Observation\nchose per c = PersonChoseThis (IdentChoice per) per c\n\none_chose :: Person -> Person -> ConcreteChoice -> Observation\none_chose per per' val = (OrObs (chose per val) (chose per' val)) \n                                  \ntwo_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation\ntwo_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))\n                             (AndObs (chose p2 c) (chose p3 c))\n\n-- Redeem alias\n\nredeem_original :: Contract\nredeem_original = RedeemCC iCC1 Null\n\n-- Commit identifier \n\niCC1 :: IdentCC\niCC1 = IdentCC 1\n\n-- Payment identifier\n\niP1 :: IdentPay\niP1 = IdentPay 1\n\n"

explanation = "Embedded Haskell code editor\n============================\n\nYou can use this editor to generate Marlowe code (to use with Meadow) by using Marlowe's Haskell embedding.\n\nThis version of Meadow will run the Haskell compiler in the server-side. You can control the editor and the compiler by using the buttons at the bottom:\n\n* Execute Haskell code - compiles and runs the Haskell code on the left panel and writes the output to this panel.\n\n* Import Meadow contract to Haskell code - creates a template based on the Marlowe contract in Meadow (under the editor) and shows this message. If you have just opened the Haskell editor the code in Meadow has already been imported.\n\n* Load escrow example - loads, in the left panel, an example of how the Haskell embedding of Marlowe can be used to implement an escrow contract.\n\n* Export generated contract to Meadow - once you have successfully generated a Marlowe contract from the Haskell code by clicking the \"Execute Haskell code\" button, this button will allow you to copy the generated contract (which will appear on this panel) back to Marlowe (under this editor).\n\n* Load Haskell code from file - allows you to select a \".hs\" file from your computer that will be displayed on the left panel.\n\n* Save Haskell code to file - allows you to save the code on the left panel to a \".hs\" file in your computer.\n\n* Minimise Haskell editor - will hide the Haskell editor so that you can keep using Meadow, but it will not delete its contents. If Haskell code is being executed or compiled when you minimise the editor, the process will continue in the background.\n\n* Close Haskell editor - it closes the editor. WARNING: if you close the editor or navigate away from this page, the contents of the editor will be lost. Make sure you save them to a file in your computer before that.\n\n\n"


