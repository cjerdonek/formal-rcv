{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.OpenRCVJSON
( Candidates(..)
, TestCase(..)
, getCandidates
, getTestCase
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import Data.Foldable
import Data.ByteString.Lazy (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Text (Text, unpack)

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser

data Candidates =
  Candidates Array
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
