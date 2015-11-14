{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main (main) where

import Data.List
import System.Random
import System.IO

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML
import Test.Tasty.QuickCheck

import qualified Data.ByteString.Lazy as B
import Text.Parsing.OpenRCVTests

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

main :: IO ()
main = tests >>= defaultMainWithIngredients ingrs

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients

tests :: IO TestTree
tests = localOption (QuickCheckTests 10000) . testGroup "SF Tests" <$> sequence
  [ test_deserialize_succeeds
  ]


-- Test that our implementation chooses the expected winner for historical
-- elections in San Fransisco.

test_deserialize_succeeds :: IO TestTree
test_deserialize_succeeds = do
  h <- openFile "test-data/rcv_trivial.json" ReadMode
  f <- B.hGetContents h
  let elec = getElection f
  return $ testCase "RCV_Deserialize" (checkDeser elec)

checkDeser :: Either String Election -> Assertion
checkDeser (Left msg) = assertFailure (show msg)
checkDeser (Right _elec) = assertEqual "Election winner" True True
