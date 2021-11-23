module Language.Marlowe.SemanticsDeserialisation (byteStringToContract) where

import Data.ByteString (ByteString)
import Data.Ratio ((%))
import Language.Marlowe.SemanticsTypes (Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Slot(Slot), Token(..),
                                        Value(AddValue, AvailableMoney, ChoiceValue, Cond, Constant, DivValue, MulValue, NegValue, Scale, SlotIntervalEnd, SlotIntervalStart, SubValue, UseValue),
                                        ValueId(..),)
import Language.Marlowe.Deserialisation (byteStringToInt, byteStringToList, byteStringToPositiveInt, getByteString)
import Data.Text.Encoding (decodeUtf8)

byteStringToParty :: ByteString -> Maybe (Party, ByteString)
byteStringToParty x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( case getByteString t1 of
          Nothing -> Nothing
          Just (z, t2) ->
            ( if y == 0
                then Just (PubKey z, t2)
                else
                  ( if y == 1
                      then Just (Role z, t2)
                      else Nothing
                  )
            )
      )

byteStringToChoiceId :: ByteString -> Maybe (ChoiceId, ByteString)
byteStringToChoiceId x =
  case getByteString x of
    Nothing -> Nothing
    Just (cn, t1) ->
      ( case byteStringToParty t1 of
          Nothing -> Nothing
          Just (co, t2) -> Just (ChoiceId cn co, t2)
      )

byteStringToValueId :: ByteString -> Maybe (ValueId, ByteString)
byteStringToValueId x = case getByteString x of
  Nothing -> Nothing
  Just (n, t) -> Just (ValueId (decodeUtf8 n), t)

byteStringToToken :: ByteString -> Maybe (Token, ByteString)
byteStringToToken x =
  case getByteString x of
    Nothing -> Nothing
    Just (cs, t1) ->
      ( case getByteString t1 of
          Nothing -> Nothing
          Just (tn, t2) -> Just (Token cs tn, t2)
      )

byteStringToObservation :: ByteString -> Maybe (Observation, ByteString)
byteStringToObservation x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( if y < 6
          then
            ( if y < 3
                then
                  ( case byteStringToObservation t1 of
                      Nothing -> Nothing
                      Just (lhs, t2) ->
                        ( if y < 1
                            then Just (NotObs lhs, t2)
                            else
                              ( case byteStringToObservation t2 of
                                  Nothing -> Nothing
                                  Just (rhs, t3) ->
                                    ( if y < 2
                                        then
                                          Just
                                            (AndObs lhs rhs, t3)
                                        else
                                          Just
                                            (OrObs lhs rhs, t3)
                                    )
                              )
                        )
                  )
                else
                  ( if y < 4
                      then
                        ( case byteStringToChoiceId t1 of
                            Nothing -> Nothing
                            Just (choId, t2) ->
                              Just (ChoseSomething choId, t2)
                        )
                      else
                        ( if y < 5
                            then Just (TrueObs, t1)
                            else Just (FalseObs, t1)
                        )
                  )
            )
          else
            ( case byteStringToValue t1 of
                Nothing -> Nothing
                Just (lhs, t2) ->
                  ( case byteStringToValue t2 of
                      Nothing -> Nothing
                      Just (rhs, t3) ->
                        ( if y < 9
                            then
                              ( if y < 7
                                  then Just (ValueGE lhs rhs, t3)
                                  else
                                    ( if y < 8
                                        then
                                          Just
                                            (ValueGT lhs rhs, t3)
                                        else
                                          Just
                                            (ValueLT lhs rhs, t3)
                                    )
                              )
                            else
                              ( if y < 10
                                  then Just (ValueLE lhs rhs, t3)
                                  else
                                    ( if y == 10
                                        then
                                          Just
                                            (ValueEQ lhs rhs, t3)
                                        else Nothing
                                    )
                              )
                        )
                  )
            )
      )

byteStringToValue :: ByteString -> Maybe (Value, ByteString)
byteStringToValue x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( if y < 7
          then
            ( if y < 3
                then
                  ( if y < 1
                      then
                        ( case byteStringToParty t1 of
                            Nothing -> Nothing
                            Just (accId, t2) ->
                              ( case byteStringToToken t2 of
                                  Nothing -> Nothing
                                  Just (token, t3) ->
                                    Just (AvailableMoney accId token, t3)
                              )
                        )
                      else
                        ( if y < 2
                            then
                              ( case byteStringToInt t1 of
                                  Nothing -> Nothing
                                  Just (amount, t2) ->
                                    Just (Constant amount, t2)
                              )
                            else
                              ( case byteStringToValue t1 of
                                  Nothing -> Nothing
                                  Just (subVal, t2) ->
                                    Just (NegValue subVal, t2)
                              )
                        )
                  )
                else
                  ( case byteStringToValue t1 of
                      Nothing -> Nothing
                      Just (lhs, t2) ->
                        ( case byteStringToValue t2 of
                            Nothing -> Nothing
                            Just (rhs, t3) ->
                              ( if y < 5
                                  then
                                    ( if y < 4
                                        then
                                          Just (AddValue lhs rhs, t3)
                                        else
                                          Just (SubValue lhs rhs, t3)
                                    )
                                  else
                                    ( if y < 6
                                        then
                                          Just (MulValue lhs rhs, t3)
                                        else
                                          Just (DivValue lhs rhs, t3)
                                    )
                              )
                        )
                  )
            )
          else
            ( if y < 10
                then
                  ( if y < 9
                      then
                        ( if y < 8
                            then
                              ( case byteStringToInt t1 of
                                  Nothing -> Nothing
                                  Just (n, t2) ->
                                    ( case byteStringToInt t2 of
                                        Nothing -> Nothing
                                        Just (d, t3) ->
                                          ( case byteStringToValue t3 of
                                              Nothing -> Nothing
                                              Just (rhs, t4) -> Just (Scale (n % d) rhs, t4)
                                          )
                                    )
                              )
                            else
                              ( case byteStringToChoiceId t1 of
                                  Nothing -> Nothing
                                  Just (choId, t2) -> Just (ChoiceValue choId, t2)
                              )
                        )
                      else Just (SlotIntervalStart, t1)
                  )
                else
                  ( if y < 12
                      then
                        ( if y < 11
                            then Just (SlotIntervalEnd, t1)
                            else
                              ( case byteStringToValueId t1 of
                                  Nothing -> Nothing
                                  Just (valId, t2) -> Just (UseValue valId, t2)
                              )
                        )
                      else
                        ( if y == 12
                            then
                              ( case byteStringToObservation t1 of
                                  Nothing -> Nothing
                                  Just (obs, t2) ->
                                    ( case byteStringToValue t2 of
                                        Nothing -> Nothing
                                        Just (thn, t3) ->
                                          ( case byteStringToValue t3 of
                                              Nothing -> Nothing
                                              Just (els, t4) -> Just (Cond obs thn els, t4)
                                          )
                                    )
                              )
                            else Nothing
                        )
                  )
            )
      )

byteStringToPayee :: ByteString -> Maybe (Payee, ByteString)
byteStringToPayee x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( case byteStringToParty t1 of
          Nothing -> Nothing
          Just (party, t2) ->
            ( if y == 0
                then Just (Account party, t2)
                else
                  ( if y == 1
                      then Just (Party party, t2)
                      else Nothing
                  )
            )
      )

byteStringToBound :: ByteString -> Maybe (Bound, ByteString)
byteStringToBound x =
  case byteStringToInt x of
    Nothing -> Nothing
    Just (l, bs1) ->
      ( case byteStringToInt bs1 of
          Nothing -> Nothing
          Just (u, bs2) -> Just (Bound l u, bs2)
      )

byteStringToAction :: ByteString -> Maybe (Action, ByteString)
byteStringToAction x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( if y < 2
          then
            ( if y < 1
                then
                  ( if y == 0
                      then
                        ( case byteStringToParty t1 of
                            Nothing -> Nothing
                            Just (accId, t2) ->
                              ( case byteStringToParty t2 of
                                  Nothing -> Nothing
                                  Just (party, t3) ->
                                    ( case byteStringToToken t3 of
                                        Nothing -> Nothing
                                        Just (token, t4) ->
                                          ( case byteStringToValue t4 of
                                              Nothing -> Nothing
                                              Just (val, t5) -> Just (Deposit accId party token val, t5)
                                          )
                                    )
                              )
                        )
                      else Nothing
                  )
                else
                  ( case byteStringToChoiceId t1 of
                      Nothing -> Nothing
                      Just (choId, t2) ->
                        ( case byteStringToList
                            byteStringToBound
                            t2 of
                            Nothing -> Nothing
                            Just (boundList, t3) ->
                              Just (Choice choId boundList, t3)
                        )
                  )
            )
          else
            ( if y == 2
                then
                  ( case byteStringToObservation t1 of
                      Nothing -> Nothing
                      Just (obs, t2) -> Just (Notify obs, t2)
                  )
                else Nothing
            )
      )

byteStringToCase :: ByteString -> Maybe (Case, ByteString)
byteStringToCase x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( if y < 1
          then
            ( if y == 0
                then
                  ( case byteStringToAction t1 of
                      Nothing -> Nothing
                      Just (action, t2) ->
                        ( case byteStringToContract t2 of
                            Nothing -> Nothing
                            Just (cont, t3) ->
                              Just (Case action cont, t3)
                        )
                  )
                else Nothing
            )
          else
            ( if y == 1
                then
                  ( case byteStringToAction t1 of
                      Nothing -> Nothing
                      Just (action, t2) ->
                        ( case getByteString t2 of
                            Nothing -> Nothing
                            Just (bs, t3) ->
                              Just (MerkleizedCase action bs, t3)
                        )
                  )
                else Nothing
            )
      )

byteStringToContract :: ByteString -> Maybe (Contract, ByteString)
byteStringToContract x =
  case byteStringToPositiveInt x of
    Nothing -> Nothing
    Just (y, t1) ->
      ( if y < 3
          then
            ( if y < 1
                then
                  ( if y == 0
                      then Just (Close, t1)
                      else Nothing
                  )
                else
                  ( if y < 2
                      then
                        ( case byteStringToParty t1 of
                            Nothing -> Nothing
                            Just (accId, t2) ->
                              ( case byteStringToPayee t2 of
                                  Nothing -> Nothing
                                  Just (payee, t3) ->
                                    ( case byteStringToToken t3 of
                                        Nothing -> Nothing
                                        Just (token, t4) ->
                                          ( case byteStringToValue t4 of
                                              Nothing -> Nothing
                                              Just (val, t5) ->
                                                ( case byteStringToContract t5 of
                                                    Nothing -> Nothing
                                                    Just (cont, t6) ->
                                                      Just (Pay accId payee token val cont, t6)
                                                )
                                          )
                                    )
                              )
                        )
                      else
                        ( case byteStringToObservation t1 of
                            Nothing -> Nothing
                            Just (obs, t2) ->
                              ( case byteStringToContract t2 of
                                  Nothing -> Nothing
                                  Just (cont1, t3) ->
                                    ( case byteStringToContract t3 of
                                        Nothing -> Nothing
                                        Just (cont2, t4) ->
                                          Just (If obs cont1 cont2, t4)
                                    )
                              )
                        )
                  )
            )
          else
            ( if y < 5
                then
                  ( if y < 4
                      then
                        ( case byteStringToList
                            byteStringToCase
                            t1 of
                            Nothing -> Nothing
                            Just (caseList, t2) ->
                              ( case byteStringToInt t2 of
                                  Nothing -> Nothing
                                  Just (timeout, t3) ->
                                    ( case byteStringToContract t3 of
                                        Nothing -> Nothing
                                        Just (cont, t4) ->
                                          Just (When caseList (Slot timeout) cont, t4)
                                    )
                              )
                        )
                      else
                        ( case byteStringToValueId t1 of
                            Nothing -> Nothing
                            Just (valId, t2) ->
                              ( case byteStringToValue t2 of
                                  Nothing -> Nothing
                                  Just (val, t3) ->
                                    ( case byteStringToContract t3 of
                                        Nothing -> Nothing
                                        Just (cont, t4) ->
                                          Just (Let valId val cont, t4)
                                    )
                              )
                        )
                  )
                else
                  ( if y == 5
                      then
                        ( case byteStringToObservation t1 of
                            Nothing -> Nothing
                            Just (obs, t2) ->
                              ( case byteStringToContract t2 of
                                  Nothing -> Nothing
                                  Just (cont, t3) ->
                                    Just (Assert obs cont, t3)
                              )
                        )
                      else Nothing
                  )
            )
      )
