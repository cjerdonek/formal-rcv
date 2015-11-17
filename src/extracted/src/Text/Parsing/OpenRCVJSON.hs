{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.OpenRCVJSON
( Candidates(..)
, TestCase(..)
, getCandidates
, getTestCase
, testInput
, TestResult(..)
, testOutput
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import Data.Foldable
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BC
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Text (Text, unpack)

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser

data Candidates =
  Candidates
    { csNames :: Array
    }
  deriving (Show)

getCandidates :: ByteString -> Either String Candidates
getCandidates input = case decode input of
  Nothing -> Left "Input was not valid JSON"
  Just v ->  parseEither parseCandidates v

parseCandidates :: Value -> Parser Candidates
parseCandidates = withObject "toplevel" $ \e -> do
  cnames <- e .: "candidate_names"
  return (Candidates cnames)

data TestCase =
  TestCase
    { tcMeta   :: Object
    , tcInput  :: Object
    , tcOutput :: Object
    } deriving (Show)

getTestCase :: Int -> ByteString -> Either String TestCase
getTestCase index input = case decode input of
  Nothing -> Left "Input was not valid JSON"
  Just v ->  parseEither (parseTestCase index) v

parseTestCase :: Int -> Value -> Parser TestCase
parseTestCase idx = withObject "toplevel" $ \e -> do
  tcs <- e .: "test_cases"
  withArray "test_cases" parseArray tcs
  where
  parseArray vec = do
    mtc <- foldlM aux Nothing vec
    case mtc of
      Just tc -> return tc
      Nothing -> fail e

  aux (Just a) = const $ return (Just a)
  aux _ = withObject "test case" $ \obj -> do
    m <- obj .: "_meta"
    x <- m   .: "index"
    i <- obj .: "input"
    o <- obj .: "output"
    if x == idx then return $ Just $ TestCase m i o
                else return Nothing

  e = "Test case with index " ++ (show idx)
    ++ " could not be found"


testInput :: Candidates -> TestCase -> String
testInput cs tc = BC.unpack r
  where
  r = encode $ object
    [ "candidate_names" .= csNames cs
    , "_meta"           .= tcMeta tc
    , "input"           .= tcInput tc
    ]

data TestResult
  = TestResultMatch
  | TestResultMismatch String

-- Returns nothing if the string encoded output matches the candidates/testcase.
testOutput :: TestCase -> String -> TestResult
testOutput tc o = case decode (BC.pack o) of
  Nothing -> TestResultMismatch "test output is not valid JSON"
  Just v  -> match v
  where
  match :: Value -> TestResult
  match v = TestResultMismatch (BC.unpack (encode (tcOutput tc)))


data ElectionResult =
  ElectionResult
    { erRounds :: [ElectionRound]
    } deriving (Eq, Show)

data ElectionRound =
  ElectionRound
    { erElected :: Set String
    , erTotals  :: Map String Int
    } deriving (Eq,Show)

parseOutput :: Object -> Either String ElectionResult
parseOutput = undefined
