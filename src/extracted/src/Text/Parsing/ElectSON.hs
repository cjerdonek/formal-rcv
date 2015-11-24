{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.ElectSON
( Election(..)
, Ballot(..)
, getElection
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import Data.ByteString.Lazy (ByteString)
import Data.Text
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser


data Election c =
  Election
  { electionMeta          :: Object
  , electionCandidates    :: Set c
  , electionBallots       :: [Ballot c]
  }
 deriving (Eq, Show)

data Ballot c = Ballot [c]
 deriving (Eq, Show)


getElection :: ByteString -> Either String (Election Text)
getElection input = case decode input of
  Nothing -> Left "Input was not valid JSON"
  Just v ->  parseEither parseElection v

parseElection :: Value -> Parser (Election Text)
parseElection = withObject "election" $ \e -> do
  electionMeta <- e .: "_meta"
  cs           <- e .: "candidates"
  bs           <- e .: "ballots"

  electionCandidates <- withArray "candidates"
    parseCandidates cs
  electionBallots    <- withArray "ballots"
    (parseBallots electionCandidates) bs

  return Election{..}

  where
  parseCandidates :: Array -> Parser (Set Text)
  parseCandidates a = do
    cs <- mapM aux (Vec.toList a)
    return (Set.fromList cs)
    where
    aux :: Value -> Parser Text
    aux (String t) = return t
    aux v = typeMismatch "string candidate name" v

parseBallots :: Set Text -> Array -> Parser [Ballot Text]
parseBallots candidates a = do
  bs <- mapM parseBallot (Vec.toList a)
  return bs
  where
  parseBallot :: Value -> Parser (Ballot Text)
  parseBallot  = withArray "ballot" $ \a -> do
    vs <- mapM aux (Vec.toList a)
    return (Ballot vs)
  aux :: Value -> Parser Text
  aux (String t) | Set.member t candidates = return t
                 | otherwise = typeMismatch "known candidate" (String t)
  aux v = typeMismatch "valid candidate type" v
