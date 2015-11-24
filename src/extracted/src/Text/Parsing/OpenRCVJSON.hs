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
import qualified Data.HashMap.Strict as H
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Text as T

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser

import Text.Parsing.ElectSON (Ballot(..))

import qualified Text.Parsec as P
import qualified Text.Parsec.Text as P

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
    , tcInput  :: ElectionInput
    , tcOutput :: Object
    } deriving (Show)

data ElectionInput =
  ElectionInput
    { eiNumCandidates :: Int
    , eiBallots       :: [Ballot Integer]
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
    o <- obj .: "output"
    i <- obj .: "input"
    m <- i   .: "_meta"
    x <- m   .: "index"
    e <- parseElectionInput i
    let tc = TestCase
          { tcMeta = m
          , tcInput = e
          , tcOutput = o
          }
    if x == idx then return $ Just tc
                else return Nothing

  e = "Test case with index " ++ (show idx)
    ++ " could not be found"

parseElectionInput :: Object -> Parser ElectionInput
parseElectionInput o = do
  n <- o .: "candidate_count"
  b <- o .: "ballots"
  bs <- parseBallots b
  return ElectionInput
    { eiNumCandidates = n
    , eiBallots = bs
    }

testInput :: Candidates -> TestCase -> String
testInput cs tc = BC.unpack r
  where
  r = encode $ object
    [ "candidate_names" .= Vec.slice 0 num_candidates (csNames cs)
    , "_meta"           .= tcMeta tc
    , "ballots"         .= ballots
    ]
  num_candidates = eiNumCandidates (tcInput tc)
  bs = eiBallots (tcInput tc)
  ballots = Array $ Vec.fromList [ String $ ballotText b | b <- bs ]

ballotText :: Ballot Integer -> Text
ballotText (Ballot vs) = T.intercalate (T.pack " ")
  [ T.pack (show v) | v <- vs ]

data TestResult
  = TestResultMatch
  | TestResultMismatch String

-- Returns nothing if the string encoded output matches the candidates/testcase.
testOutput :: TestCase -> String -> TestResult
testOutput tc o = case decode (BC.pack o) of
  Nothing -> TestResultMismatch "test output is not valid JSON"
  Just v  -> case parseOutput v of
    Left err -> TestResultMismatch
      ("test output is not a valid election result: " ++ err)
    Right output_res -> case parseOutput (tcOutput tc) of
      Left err -> TestResultMismatch
        ("test case expected output is not a valid election result: " ++ err)
      Right output_expected -> case output_res == output_expected of
        False -> TestResultMismatch ("test output does not match expected output")
        True -> TestResultMatch

data ElectionResult =
  ElectionResult
    { erRounds :: [ElectionRound]
    } deriving (Eq, Show)

data ElectionRound =
  ElectionRound
    { erElected :: Set Text
    , erTotals  :: Map Text Int
    } deriving (Eq,Show)

parseOutput :: Object -> Either String ElectionResult
parseOutput output = parseEither aux output
  where
  aux o = do
    rs <- o .: "rounds"
    erRounds <- mapM parseRound rs
    return ElectionResult{..}

parseRound :: Value -> Parser ElectionRound
parseRound v = withObject "round" aux v
  where
  aux o = do
    e <- o .: "elected"
    erElected <- parseElected e
    t <- o .: "totals"
    erTotals  <- parseTotals t
    return ElectionRound{..}


parseElected :: Array -> Parser (Set Text)
parseElected a = do
  -- Let it be known: this is the first time I have ever written Haskell that
  -- would benefit from the Foldable/Traversable proposal
  es <- mapM (withText "elected" return) (Vec.toList a)
  return (Set.fromList es)

parseTotals :: Object -> Parser (Map Text Int)
parseTotals o = do
  vs <- mapM parseTotal (H.toList o)
  return (Map.fromList vs)
  where
  parseTotal (k,v) = do
    votes <- withScientific "vote count" (parseInt k) v
    return (k, votes)
  parseInt k s = case toBoundedInteger s of
    Just i -> return i
    Nothing -> fail ("Vote count of " ++ show s ++ " for "
                  ++ T.unpack k ++ " is not an integer.")

parseBallots :: Array -> Parser [Ballot Integer]
parseBallots a = mapM aux (Vec.toList a)
  where
  aux (String b) = case ballotFromText b of
    Left e -> fail (show e)
    Right t -> return t
  aux v = typeMismatch "string ballot representation" v


ballotFromText :: Text -> Either P.ParseError (Ballot Integer)
ballotFromText = P.parse parseBallot ""

parseBallot :: P.Parser (Ballot Integer)
parseBallot = do
  vs <- P.sepBy decimal (P.char ' ')
  return (Ballot vs)

decimal :: P.Parser Integer
decimal = decDigit >>= go
 where
  decDigit = digitValue <$> P.digit

  digitValue :: Char -> Integer
  digitValue c = fromIntegral (fromEnum c - fromEnum '0')

  go i = P.try (do d <- decDigit
                   go (10*i + d))
         P.<|> return i
