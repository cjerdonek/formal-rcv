{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.OpenRCVTests
( Election(..)
, Ballot(..)
, getElection
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import Data.ByteString.Lazy (ByteString)
import Data.Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as Vec

import Data.Aeson
import qualified Data.Aeson.Types  as A
import qualified Data.Aeson.Parser as A
import Text.Parsec
import Text.Parsec.Text


data Election =
  Election
  { electionMeta          :: Object
  , electionNumCandidates :: Int
  , electionCandidates    :: Map Int Text
  , electionBallots       :: [Ballot]
  }
 deriving (Show)

getElection :: ByteString -> Either String Election
getElection input = case decode input of
  Nothing -> Left "Input was not valid JSON"
  Just v ->  A.parseEither parseElection v

parseElection :: Value -> A.Parser Election
parseElection = withObject "election" $ \e -> do
  electionMeta <- e .: "_meta"
  cnames       <- e .: "candidate_names"
  ballots      <- e .: "ballots"


  electionCandidates <- withArray "candidate_names" parseCandidates cnames
  let electionNumCandidates = Map.size electionCandidates
  electionBallots    <- withArray "ballots" parseBallots ballots

  return Election{..}

  where
  parseCandidates :: Array -> A.Parser (Map Int Text)
  parseCandidates a = do
    kvs <- mapM aux (Prelude.zip [1..] (Vec.toList a))
    return (Map.fromList kvs)
    where
    aux (i, A.String t) = return (i, t)
    aux (_, v) = A.typeMismatch "string candidate name" v

  parseBallots :: Array -> A.Parser [Ballot]
  parseBallots a = mapM aux (Vec.toList a)
    where
    aux (A.String b) = case ballotText b of
      Left e -> fail (show e)
      Right t -> return t
    aux v = A.typeMismatch "string ballot representation" v

data Ballot = Ballot [Integer]
 deriving (Show)

ballotText :: Text -> Either ParseError Ballot
ballotText = parse parseBallot ""

parseBallot :: Parser Ballot
parseBallot = do
  vs <- sepBy decimal (char ' ')
  return (Ballot vs)


decimal :: Parser Integer
decimal = decDigit >>= go
 where
  decDigit = digitValue <$> digit

  digitValue :: Char -> Integer
  digitValue c = fromIntegral (fromEnum c - fromEnum '0')

  go i = try (do d <- decDigit
                 go (10*i + d))
         <|> return i
