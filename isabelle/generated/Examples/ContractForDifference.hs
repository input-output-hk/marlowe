{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Examples.ContractForDifference(CfdArgs_ext, cfd) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified HOL;
import qualified Stringa;
import qualified SemanticsTypes;
import qualified Arith;

data CfdArgs_ext a =
  CfdArgs_ext SemanticsTypes.Party SemanticsTypes.Party SemanticsTypes.Party
    SemanticsTypes.Value Arith.Int SemanticsTypes.Value Arith.Int Arith.Int
    Arith.Int Arith.Int Arith.Int a
  deriving (Prelude.Read, Prelude.Show);

ada :: SemanticsTypes.Token;
ada = SemanticsTypes.Token (Stringa.implode []) (Stringa.implode []);

counterpartyDepositDeadline :: forall a. CfdArgs_ext a -> Arith.Int;
counterpartyDepositDeadline
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = counterpartyDepositDeadline;

secondWindowBeginning :: forall a. CfdArgs_ext a -> Arith.Int;
secondWindowBeginning
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = secondWindowBeginning;

secondWindowDeadline :: forall a. CfdArgs_ext a -> Arith.Int;
secondWindowDeadline
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = secondWindowDeadline;

partyDepositDeadline :: forall a. CfdArgs_ext a -> Arith.Int;
partyDepositDeadline
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = partyDepositDeadline;

firstWindowBeginning :: forall a. CfdArgs_ext a -> Arith.Int;
firstWindowBeginning
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = firstWindowBeginning;

firstWindowDeadline :: forall a. CfdArgs_ext a -> Arith.Int;
firstWindowDeadline
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = firstWindowDeadline;

counterpartyDeposit :: forall a. CfdArgs_ext a -> SemanticsTypes.Value;
counterpartyDeposit
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = counterpartyDeposit;

counterpartyParty :: forall a. CfdArgs_ext a -> SemanticsTypes.Party;
counterpartyParty
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = counterpartyParty;

partyDeposit :: forall a. CfdArgs_ext a -> SemanticsTypes.Value;
partyDeposit
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = partyDeposit;

transferUpToDeposit ::
  SemanticsTypes.Party ->
    SemanticsTypes.Value ->
      SemanticsTypes.Party ->
        SemanticsTypes.Value ->
          SemanticsTypes.Contract -> SemanticsTypes.Contract;
transferUpToDeposit from payerDeposit to amount =
  SemanticsTypes.Pay from (SemanticsTypes.Account to) ada
    (SemanticsTypes.Cond (SemanticsTypes.ValueLT amount payerDeposit) amount
      payerDeposit);

oracleParty :: forall a. CfdArgs_ext a -> SemanticsTypes.Party;
oracleParty
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = oracleParty;

partyParty :: forall a. CfdArgs_ext a -> SemanticsTypes.Party;
partyParty
  (CfdArgs_ext partyParty counterpartyParty oracleParty partyDeposit
    partyDepositDeadline counterpartyDeposit counterpartyDepositDeadline
    firstWindowBeginning firstWindowDeadline secondWindowBeginning
    secondWindowDeadline more)
  = partyParty;

recordDifference ::
  SemanticsTypes.ValueId ->
    SemanticsTypes.ChoiceId ->
      SemanticsTypes.ChoiceId ->
        SemanticsTypes.Contract -> SemanticsTypes.Contract;
recordDifference name choiceId1 choiceId2 =
  SemanticsTypes.Let name
    (SemanticsTypes.SubValue (SemanticsTypes.ChoiceValue choiceId1)
      (SemanticsTypes.ChoiceValue choiceId2));

priceBeginning :: SemanticsTypes.Party -> SemanticsTypes.ChoiceId;
priceBeginning =
  SemanticsTypes.ChoiceId
    (Stringa.implode
      [Stringa.Char False False False False True False True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char True True False False False True True False,
        Stringa.Char True False True False False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False True True True False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char False True True False False True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char True True False False True True True False,
        Stringa.Char False False True False True True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char True True True False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False True True True False True True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char True True True False True True True False]);

initialDeposit ::
  SemanticsTypes.Party ->
    SemanticsTypes.Value ->
      Arith.Int ->
        SemanticsTypes.Contract ->
          SemanticsTypes.Contract -> SemanticsTypes.Contract;
initialDeposit by deposit timeout timeoutContinuation continuation =
  SemanticsTypes.When
    [SemanticsTypes.Case (SemanticsTypes.Deposit by by ada deposit)
       continuation]
    timeout timeoutContinuation;

oracleInput ::
  SemanticsTypes.ChoiceId ->
    Arith.Int ->
      SemanticsTypes.Contract ->
        SemanticsTypes.Contract -> SemanticsTypes.Contract;
oracleInput choiceId timeout timeoutContinuation continuation =
  SemanticsTypes.When
    [SemanticsTypes.Case
       (SemanticsTypes.Choice choiceId
         [SemanticsTypes.Bound Arith.zero_int
            (Arith.Int_of_integer (1000000000 :: Integer))])
       continuation]
    timeout timeoutContinuation;

priceEnd :: SemanticsTypes.Party -> SemanticsTypes.ChoiceId;
priceEnd =
  SemanticsTypes.ChoiceId
    (Stringa.implode
      [Stringa.Char False False False False True False True False,
        Stringa.Char False True False False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char True True False False False True True False,
        Stringa.Char True False True False False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False True True True False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char True True False False True True True False,
        Stringa.Char True False True False False True True False,
        Stringa.Char True True False False False True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char False True True True False True True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char False False False False False True False False,
        Stringa.Char True True True False True True True False,
        Stringa.Char True False False True False True True False,
        Stringa.Char False True True True False True True False,
        Stringa.Char False False True False False True True False,
        Stringa.Char True True True True False True True False,
        Stringa.Char True True True False True True True False]);

gtLtEq ::
  SemanticsTypes.Value ->
    SemanticsTypes.Value ->
      SemanticsTypes.Contract ->
        SemanticsTypes.Contract ->
          SemanticsTypes.Contract -> SemanticsTypes.Contract;
gtLtEq value1 value2 gtContinuation ltContinuation eqContinuation =
  SemanticsTypes.If (SemanticsTypes.ValueGT value1 value2) gtContinuation
    (SemanticsTypes.If (SemanticsTypes.ValueLT value1 value2) ltContinuation
      eqContinuation);

wait :: Arith.Int -> SemanticsTypes.Contract -> SemanticsTypes.Contract;
wait timeout cont = SemanticsTypes.When [] timeout cont;

cfd :: CfdArgs_ext () -> SemanticsTypes.Contract;
cfd args =
  let {
    decreaseInPrice =
      SemanticsTypes.ValueId
        (Stringa.implode
          [Stringa.Char False False True False False False True False,
            Stringa.Char True False True False False True True False,
            Stringa.Char True True False False False True True False,
            Stringa.Char False True False False True True True False,
            Stringa.Char True False True False False True True False,
            Stringa.Char True False False False False True True False,
            Stringa.Char True True False False True True True False,
            Stringa.Char True False True False False True True False,
            Stringa.Char False False False False False True False False,
            Stringa.Char True False False True False True True False,
            Stringa.Char False True True True False True True False,
            Stringa.Char False False False False False True False False,
            Stringa.Char False False False False True True True False,
            Stringa.Char False True False False True True True False,
            Stringa.Char True False False True False True True False,
            Stringa.Char True True False False False True True False,
            Stringa.Char True False True False False True True False]);
    increaseInPrice =
      SemanticsTypes.ValueId
        (Stringa.implode
          [Stringa.Char True False False True False False True False,
            Stringa.Char False True True True False True True False,
            Stringa.Char True True False False False True True False,
            Stringa.Char False True False False True True True False,
            Stringa.Char True False True False False True True False,
            Stringa.Char True False False False False True True False,
            Stringa.Char True True False False True True True False,
            Stringa.Char True False True False False True True False,
            Stringa.Char False False False False False True False False,
            Stringa.Char True False False True False True True False,
            Stringa.Char False True True True False True True False,
            Stringa.Char False False False False False True False False,
            Stringa.Char False False False False True True True False,
            Stringa.Char False True False False True True True False,
            Stringa.Char True False False True False True True False,
            Stringa.Char True True False False False True True False,
            Stringa.Char True False True False False True True False]);
    party = partyParty args;
    counterparty = counterpartyParty args;
    oracle = oracleParty args;
  } in initialDeposit party (partyDeposit args) (partyDepositDeadline args)
         SemanticsTypes.Close
         (initialDeposit counterparty (counterpartyDeposit args)
           (counterpartyDepositDeadline args) SemanticsTypes.Close
           (wait (firstWindowBeginning args)
             (oracleInput (priceBeginning oracle) (firstWindowDeadline args)
               SemanticsTypes.Close
               (wait (secondWindowBeginning args)
                 (oracleInput (priceEnd oracle) (secondWindowDeadline args)
                   SemanticsTypes.Close
                   (gtLtEq (SemanticsTypes.ChoiceValue (priceBeginning oracle))
                     (SemanticsTypes.ChoiceValue (priceEnd oracle))
                     (recordDifference decreaseInPrice (priceBeginning oracle)
                       (priceEnd oracle)
                       (transferUpToDeposit counterparty
                         (counterpartyDeposit args) party
                         (SemanticsTypes.UseValue decreaseInPrice)
                         SemanticsTypes.Close))
                     (recordDifference increaseInPrice (priceEnd oracle)
                       (priceBeginning oracle)
                       (transferUpToDeposit party (partyDeposit args)
                         counterparty (SemanticsTypes.UseValue increaseInPrice)
                         SemanticsTypes.Close))
                     SemanticsTypes.Close))))));

}
