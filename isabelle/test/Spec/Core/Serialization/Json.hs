{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Spec.Core.Serialization.Json (tests) where

import Data.Aeson (decode, encode)
import qualified Data.ByteString.Lazy as L
import MarloweCoreJson (addressExample, roleExample, dolarToken, internalPayeeExample, choiceExample)
import Test.Tasty (TestTree, TestName, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Golden (goldenVsStringDiff)
import System.FilePath ((</>))

diffCommand :: FilePath -> FilePath -> [String]
diffCommand golden actual = ["diff", "-u", "--color=always", actual, golden]

goldenPath :: FilePath
goldenPath = "test" </> "Spec" </> "Core" </> "Serialization" </> "golden"

goldenTest :: TestName -> FilePath -> IO L.ByteString -> TestTree
goldenTest name path io = goldenVsStringDiff name diffCommand path io

tests :: TestTree
tests = testGroup "Core Json"
    [ partyTests
    , tokenTests
    , payeeTests
    , choiceIdTests
    ]

-- === Party ===

partyTests :: TestTree
partyTests = testGroup "Party"
    [ testCase "Party Roundtrip" testExampleAddressRoundtrip
    , testGoldenPartyAddress
    , testGoldenPartyRole
    ]


-- TODO: Generate Gen instances and change for a property based test.
testExampleAddressRoundtrip :: IO ()
testExampleAddressRoundtrip =
    let
        roundtrip = decode $ encode addressExample
    in
        roundtrip @?= Just addressExample

testGoldenPartyAddress :: TestTree
testGoldenPartyAddress = goldenTest
    "Golden Party Address"
    (goldenPath </> "party-address.golden")
    (pure $ encode addressExample)

testGoldenPartyRole :: TestTree
testGoldenPartyRole = goldenTest
    "Golden Party Role"
    (goldenPath </> "party-role.golden")
    (pure $ encode roleExample)


-- === Token ===
tokenTests :: TestTree
tokenTests = testGroup "Token"
    [ testCase "Token Roundtrip" testTokenRoundtrip
    , testGoldenDolarToken
    ]


-- TODO: Generate Gen instances and change for a property based test.
testTokenRoundtrip :: IO ()
testTokenRoundtrip =
    let
        roundtrip = decode $ encode dolarToken
    in
        roundtrip @?= Just dolarToken

testGoldenDolarToken :: TestTree
testGoldenDolarToken = goldenTest
    "Golden Dolar Token"
    (goldenPath </> "dolar-token.golden")
    (pure $ encode dolarToken)

-- === Payee ===

payeeTests :: TestTree
payeeTests = testGroup "Payee"
    [ testCase "Payee Roundtrip" testPayeeRoundtrip
    , testGoldenInternalPayee
    ]


-- TODO: Generate Gen instances and change for a property based test.
testPayeeRoundtrip :: IO ()
testPayeeRoundtrip =
    let
        roundtrip = decode $ encode internalPayeeExample
    in
        roundtrip @?= Just internalPayeeExample

testGoldenInternalPayee :: TestTree
testGoldenInternalPayee = goldenTest
    "Golden Internal Payee"
    (goldenPath </> "internal-payee.golden")
    (pure $ encode internalPayeeExample)

-- === ChoiceId ===

choiceIdTests :: TestTree
choiceIdTests = testGroup "ChoiceId"
    [ testCase "ChoiceId Roundtrip" testChoiceIdRoundtrip
    , testGoldenChoiceId
    ]


-- TODO: Generate Gen instances and change for a property based test.
testChoiceIdRoundtrip :: IO ()
testChoiceIdRoundtrip =
    let
        roundtrip = decode $ encode choiceExample
    in
        roundtrip @?= Just choiceExample

testGoldenChoiceId :: TestTree
testGoldenChoiceId = goldenTest
    "Golden Choice Id"
    (goldenPath </> "choice-id.golden")
    (pure $ encode choiceExample)