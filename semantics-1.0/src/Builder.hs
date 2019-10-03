module Builder where

import Control.Monad.State

import qualified Semantics as M

data BuilderState = BuilderState {
    identCC  :: Integer,
    identPay :: Integer,
    identChoice :: Integer,
    identPerson :: Integer
}

emptyBuilder :: BuilderState
emptyBuilder = BuilderState { identCC = 0, identPay = 0, identChoice = 0, identPerson = 0 }

freshCC :: State BuilderState M.IdentCC
freshCC = do
    i <- gets identCC
    modify (\s -> s { identCC = i + 1 })
    return $ M.IdentCC i

freshPay :: State BuilderState M.IdentPay
freshPay = do
    i <- gets identPay
    modify (\s -> s { identPay = i + 1 })
    return $ M.IdentPay i


buildContract b = evalState b emptyBuilder

contract = do
    c1 <- freshCC
    return c1