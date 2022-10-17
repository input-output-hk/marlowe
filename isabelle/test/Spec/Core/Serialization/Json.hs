{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Spec.Core.Serialization.Json (tests) where

import Data.Aeson (ToJSON, FromJSON, decode, encode)
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy as L
import MarloweCoreJson
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

-- TODO: Generate Gen instances and change for a property based test.
roundtripTest :: ToJSON a => FromJSON a => Eq a => Show a => TestName -> [a] -> TestTree
roundtripTest testName as = testCase testName (do
    traverse (\a -> (decode $ encode a) @?= Just a) as
    return ())

tests :: TestTree
tests = testGroup "Core Json Serialization"
    [ partyTests
    , tokenTests
    , payeeTests
    , choiceIdTests
    , boundTests
    , valueTests
    , observationTests
    ]


partyTests :: TestTree
partyTests = testGroup "Party"
    [ roundtripTest "Party Roundtrip" [addressExample, roleExample]
    , goldenTest
        "Golden Party Address"
        (goldenPath </> "party-address.golden")
        (pure $ encode addressExample)
    , goldenTest
        "Golden Party Role"
        (goldenPath </> "party-role.golden")
        (pure $ encode roleExample)
    ]


tokenTests :: TestTree
tokenTests = testGroup "Token"
    [ roundtripTest "Token Roundtrip" [dolarToken]
    , goldenTest
        "Golden Dolar Token"
        (goldenPath </> "dolar-token.golden")
        (pure $ encode dolarToken)
    ]

payeeTests :: TestTree
payeeTests = testGroup "Payee"
    [ roundtripTest "Payee Roundtrip" [internalPayeeExample, externalPayeeExample]
    , goldenTest
        "Golden Internal Payee"
        (goldenPath </> "internal-payee.golden")
        (pure $ encode internalPayeeExample)
    , goldenTest
        "Golden External Payee"
        (goldenPath </> "external-payee.golden")
        (pure $ encode externalPayeeExample)
    ]

choiceIdTests :: TestTree
choiceIdTests = testGroup "ChoiceId"
    [ roundtripTest "ChoiceId Roundtrip" [choiceExample]
    , goldenTest
        "Golden Choice Id"
        (goldenPath </> "choice-id.golden")
        (pure $ encode choiceExample)
    ]

boundTests :: TestTree
boundTests = testGroup "Bound"
    [ roundtripTest "Bound Roundtrip" [exampleBound]
    , goldenTest
        "Golden Bound"
        (goldenPath </> "bound.golden")
        (pure $ encode exampleBound)
    ]

valueTests :: TestTree
valueTests = testGroup "Value"
    [ roundtripTest "Value roundtrip"
        [ constantExample
        , intervalStartExample
        , intervalEndExample
        , addExample
        , subExample
        , mulExample
        , divExample
        , negateExample
        , choiceValueExample
        , useValueExample
        , condExample
        , availableMoneyExample
        ]
    , goldenTest
        "Golden Value Constant"
        (goldenPath </> "value-constant.golden")
        (pure $ encode constantExample)
    , goldenTest
        "Golden Value Interval Start"
        (goldenPath </> "value-interval-start.golden")
        (pure $ encode intervalStartExample)
    , goldenTest
        "Golden Value Interval End"
        (goldenPath </> "value-interval-end.golden")
        (pure $ encode intervalEndExample)
    , goldenTest
        "Golden Value Add"
        (goldenPath </> "value-add.golden")
        (pure $ encode addExample)
    , goldenTest
        "Golden Value Sub"
        (goldenPath </> "value-sub.golden")
        (pure $ encode subExample)
    , goldenTest
        "Golden Value Mul"
        (goldenPath </> "value-mul.golden")
        (pure $ encode mulExample)
    , goldenTest
        "Golden Value Div"
        (goldenPath </> "value-div.golden")
        (pure $ encode divExample)
    , goldenTest
        "Golden Value Negate"
        (goldenPath </> "value-negate.golden")
        (pure $ encode negateExample)
    , goldenTest
        "Golden Value Choice"
        (goldenPath </> "value-choice.golden")
        (pure $ encodePretty choiceValueExample)
    , goldenTest
        "Golden Value Use"
        (goldenPath </> "value-use.golden")
        (pure $ encode useValueExample)
    , goldenTest
        "Golden Value Cond"
        (goldenPath </> "value-cond.golden")
        (pure $ encodePretty condExample)
    , goldenTest
        "Golden Value Available Money"
        (goldenPath </> "value-available.golden")
        (pure $ encodePretty availableMoneyExample)
    ]

observationTests :: TestTree
observationTests = testGroup "Observation"
    [ roundtripTest "Observation roundtrip"
        [ trueExample
        , falseExample
        , andExample
        , orExample
        , notExample
        , choseExample
        , valueGEExample
        , valueGTExample
        , valueLTExample
        , valueLEExample
        , valueEQExample
        ]
    , goldenTest
        "Golden Observation True"
        (goldenPath </> "observation-true.golden")
        (pure $ encode trueExample)
    , goldenTest
        "Golden Observation False"
        (goldenPath </> "observation-false.golden")
        (pure $ encode falseExample)
    , goldenTest
        "Golden Observation And"
        (goldenPath </> "observation-and.golden")
        (pure $ encode andExample)
    , goldenTest
        "Golden Observation Or"
        (goldenPath </> "observation-or.golden")
        (pure $ encode orExample)
    , goldenTest
        "Golden Observation Not"
        (goldenPath </> "observation-not.golden")
        (pure $ encode notExample)
    , goldenTest
        "Golden Observation Chose"
        (goldenPath </> "observation-chose.golden")
        (pure $ encodePretty choseExample)
    , goldenTest
        "Golden Observation Greater or Eq"
        (goldenPath </> "observation-ge.golden")
        (pure $ encode valueGEExample)
    , goldenTest
        "Golden Observation Greater"
        (goldenPath </> "observation-gt.golden")
        (pure $ encode valueGTExample)
    , goldenTest
        "Golden Observation Lower"
        (goldenPath </> "observation-lt.golden")
        (pure $ encode valueLTExample)
    , goldenTest
        "Golden Observation Lower or Eq"
        (goldenPath </> "observation-le.golden")
        (pure $ encode valueLEExample)
    , goldenTest
        "Golden Observation Equal"
        (goldenPath </> "observation-eq.golden")
        (pure $ encode valueEQExample)
    ]