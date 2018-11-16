{-# LANGUAGE ForeignFunctionInterface #-}
-- | Main compiler executable.

module Main where

import           Fay
import Fay.Types
import Fay.Compiler
import GHCJS.Types (JSVal)
import Data.JSString (JSString, pack, unpack)
import GHCJS.Foreign (fromJSBool, toJSBool)
import GHCJS.Foreign.Callback (Callback, asyncCallback)

foreign import javascript safe
   "try { eval($1); } catch (err) { textarea.setValue('Error while executing Fay code:\\n\\n' + err); textarea.setOption('mode', 'text/plain'); textarea.setOption('lineWrapping', true); }"
   evalAux :: JSString -> IO ()
eval = evalAux . pack

doCompile :: String -> IO (Maybe String)
doCompile source = do res <- compileViaStr "Main.hs" (defaultConfig {configTypecheck = False, configExportRuntime = False, configExportStdlib = False}) (compileToplevelModuleText "Main.hs" source) source
                      case res of
                        Right (b , _, _) -> do {setCodeMirrorValue2 "";
                                                setCodeMirror2Highlight;
                                                eval (rt ++ (pwOutputString (execPrinter b defaultPrintReader)) ++ "Fay$$_(Main.main, true);");
                                                return Nothing}
                        Left o -> return $ Just $ show o

rt :: String
rt = "\n/*******************************************************************************\n * Misc.\n */\n\n\n// Workaround for missing functionality in IE 8 and earlier.\nif( Object.create === undefined ) {\n  Object.create = function( o ) {\n    function F(){}\n    F.prototype = o;\n    return new F();\n  };\n}\n\n// Insert properties of b in place into a.\nfunction Fay$$objConcat(a,b){\n  for (var p in b) if (b.hasOwnProperty(p)){\n    a[p] = b[p];\n  }\n  return a;\n}\n\n/*******************************************************************************\n * Thunks.\n */\n\n// Force a thunk (if it is a thunk) until WHNF.\nfunction Fay$$_(thunkish,nocache){\n  while (thunkish instanceof Fay$$$) {\n    thunkish = thunkish.force(nocache);\n  }\n  return thunkish;\n}\n\n// Apply a function to arguments (see method2 in Fay.hs).\nfunction Fay$$__(){\n  var f = arguments[0];\n  for (var i = 1, len = arguments.length; i < len; i++) {\n    f = (f instanceof Fay$$$? Fay$$_(f) : f)(arguments[i]);\n  }\n  return f;\n}\n\n// Thunk object.\nfunction Fay$$$(value){\n  this.forced = false;\n  this.value = value;\n}\n\n// Force the thunk.\nFay$$$.prototype.force = function(nocache) {\n  return nocache ?\n    this.value() :\n    (this.forced ?\n     this.value :\n     (this.value = this.value(), this.forced = true, this.value));\n};\n\n\nfunction Fay$$seq(x) {\n  return function(y) {\n    Fay$$_(x,false);\n    return y;\n  }\n}\n\nfunction Fay$$seq$36$uncurried(x,y) {\n  Fay$$_(x,false);\n  return y;\n}\n\n/*******************************************************************************\n * Monad.\n */\n\nfunction Fay$$Monad(value){\n  this.value = value;\n}\n\n// This is used directly from Fay, but can be rebound or shadowed. See primOps in Types.hs.\n// >>\nfunction Fay$$then(a){\n  return function(b){\n    return Fay$$bind(a)(function(_){\n      return b;\n    });\n  };\n}\n\n// This is used directly from Fay, but can be rebound or shadowed. See primOps in Types.hs.\n// >>\nfunction Fay$$then$36$uncurried(a,b){\n  return Fay$$bind$36$uncurried(a,function(_){ return b; });\n}\n\n// >>=\n// This is used directly from Fay, but can be rebound or shadowed. See primOps in Types.hs.\nfunction Fay$$bind(m){\n  return function(f){\n    return new Fay$$$(function(){\n      var monad = Fay$$_(m,true);\n      return Fay$$_(f)(monad.value);\n    });\n  };\n}\n\n// >>=\n// This is used directly from Fay, but can be rebound or shadowed. See primOps in Types.hs.\nfunction Fay$$bind$36$uncurried(m,f){\n  return new Fay$$$(function(){\n    var monad = Fay$$_(m,true);\n    return Fay$$_(f)(monad.value);\n  });\n}\n\n// This is used directly from Fay, but can be rebound or shadowed.\nfunction Fay$$$_return(a){\n  return new Fay$$Monad(a);\n}\n\n// Allow the programmer to access thunk forcing directly.\nfunction Fay$$force(thunk){\n  return function(type){\n    return new Fay$$$(function(){\n      Fay$$_(thunk,type);\n      return new Fay$$Monad(Fay$$unit);\n    })\n  }\n}\n\n// This is used directly from Fay, but can be rebound or shadowed.\nfunction Fay$$return$36$uncurried(a){\n  return new Fay$$Monad(a);\n}\n\n// Unit: ().\nvar Fay$$unit = null;\n\n/*******************************************************************************\n * Serialization.\n * Fay <-> JS. Should be bijective.\n */\n\n// Serialize a Fay object to JS.\nfunction Fay$$fayToJs(type,fayObj){\n  var base = type[0];\n  var args = type[1];\n  var jsObj;\n  if(base == \"action\") {\n    // A nullary monadic action. Should become a nullary JS function.\n    // Fay () -> function(){ return ... }\n    return function(){\n      return Fay$$fayToJs(args[0],Fay$$_(fayObj,true).value);\n    };\n\n  }\n  else if(base == \"function\") {\n    // A proper function.\n    return function(){\n      var fayFunc = fayObj;\n      var return_type = args[args.length-1];\n      var len = args.length;\n      // If some arguments.\n      if (len > 1) {\n        // Apply to all the arguments.\n        fayFunc = Fay$$_(fayFunc,true);\n        // TODO: Perhaps we should throw an error when JS\n        // passes mo

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

compile :: IO ()
compile = do setCodeMirrorValue2 "Compiling...\n\nThis could take more than one minute."
             setCodeMirror2Plain
             disableButton "compile"
             disableButton "reset"
             disableButton "submit"
             disableButton "example"
             disableButton "upload"
             disableButton "cancel"
             y <- getCodeMirrorValue
             x <- doCompile y
             case x of
                Just x -> do { setCodeMirrorValue2 ("Compilation error:\n\n" ++ x);
                               setCodeMirror2Plain }
                Nothing -> do { enableButton "submit" }
             enableButton "compile"
             enableButton "reset"
             enableButton "example"
             ies <- isUploadSupported
             if (ies) then enableButton "upload" else (return ())
             enableButton "minimise"
             enableButton "cancel"

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
              downloadFile c "Main.hs" 

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

prefix = "module Main where\n\nimport Marlowe\nimport Fay.FFI (ffi)\n\nsetCode :: String -> Fay ()\nsetCode = ffi \"textarea.setValue(%1)\"\n\nmain :: Fay ()\nmain = setCode (prettyPrintContract contract)\n\n-------------------------------------\n-- Write your code below this line --\n-------------------------------------\n\n\ncontract :: Contract\ncontract = "

exampleCode = "module Main where\n\nimport Marlowe\nimport Fay.FFI (ffi)\n\nsetCode :: String -> Fay ()\nsetCode = ffi \"textarea.setValue(%1)\"\n\nmain :: Fay ()\nmain = setCode (prettyPrintContract contract)\n\n-------------------------------------\n-- Write your code below this line --\n-------------------------------------\n\n-- Escrow example using embedding\n\ncontract :: Contract\ncontract = CommitCash iCC1 1\n                      (ConstMoney 450)\n                      10 100\n                      (When (OrObs (two_chose 1 2 3 0)\n                                   (two_chose 1 2 3 1))\n                            90\n                            (Choice (two_chose 1 2 3 1)\n                                    (Pay iP1 1 2\n                                         (AvailableMoney iCC1)\n                                         100\n                                         redeem_original)\n                                    redeem_original)\n                            redeem_original)\n                      Null\n\nchose :: Int -> ConcreteChoice -> Observation\nchose per c =  PersonChoseThis (IdentChoice per) per c\n\none_chose :: Person -> Person -> ConcreteChoice -> Observation\none_chose per per' val = (OrObs (chose per val) (chose per' val)) \n                                  \ntwo_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation\ntwo_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))\n                             (AndObs (chose p2 c) (chose p3 c))\n\nredeem_original :: Contract\nredeem_original = RedeemCC iCC1 Null\n\niCC1 :: IdentCC\niCC1 = IdentCC 1\n\niP1 :: IdentPay\niP1 = IdentPay 1\n\n\n"

explanation = "Embedded Fay code editor\n========================\n\nYou can use this editor to generate Marlowe code (to use with Meadow) by using Marlowe's Fay embedding.\n\nFay is a subset of Haskell (https://github.com/faylang/fay/wiki)\n\nThe editor includes a pruned version of the Fay compiler. You can control the editor and the compiler by using the buttons at the bottom:\n\n* Execute Fay code - compiles and runs the Fay code on the left panel and writes the output to this panel.\n\n* Import Meadow contract to Fay code - creates a template based on the Marlowe contract in Meadow (under the editor) and shows this message. If you have just opened the Fay editor the code in Meadow has already been imported.\n\n* Load escrow example - loads, in the left panel, an example of how the Fay embedding of Marlowe can be used to implement an escrow contract.\n\n* Export generated contract to Meadow - once you have successfully generated a Marlowe contract from the Fay code by clicking the \"Execute Fay code\" button, this button will allow you to copy the generated contract (which will appear on this panel) back to Marlowe (under this editor).\n\n* Load Fay code from file - allows you to select a \".hs\" file from your computer that will be displayed on the left panel.\n\n* Save Fay code to file - allows you to save the code on the left panel to a \".hs\" file in your computer.\n\n* Minimise Fay editor - will hide the Fay editor so that you can keep using Meadow, but it will not delete its contents. If Fay code is being executed or compiled when you minimise the editor, the process will continue in the background.\n\n* Close Fay editor - it closes the editor. WARNING: if you close the editor or navigate away from this page, the contents of the editor will be lost. Make sure you save them to a file in your computer before that.\n\nPlease note that the compiler included does not do type-checking of the code provided. This is because the Fay compiler relies on GHC for that, and this demo runs in the browser (so it does not have access to GHC). You can use GHC offline in order to type-check your programs, the source for the Marlowe module can be found in the path \"/meadow/editor/fay-code\" of the Github repository.\n\n\n"

