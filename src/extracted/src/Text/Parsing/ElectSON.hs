{-# LANGUAGE CPP #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.ElectSON where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import           Data.ByteString.Lazy (ByteString)
import           Data.List (group, sort)
import           Data.Text (Text)
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser

optField :: ToJSON a => Text -> Maybe a -> [Pair] -> [Pair]
optField _  Nothing  xs = xs
optField nm (Just x) xs = (nm .= x) : xs

-- type decls

-- | An Election is the top-level JSON representation of an election:
--   this includes some fields that are only important for testing.
data Election vote = Election
  { elIsTest     :: Bool
  , elCounts     :: Maybe [Int]
  , elVotes      :: [vote]
  , elCandidates :: [Integer]
  , elTiebreak   :: [Integer]
  , elResults    :: Maybe Results
  } deriving (Eq, Show)

-- | An RCVVote represents a ranking of all the candidates, as well as
--   a unique identifier for that vote.
data RCVVote = RCVVote
  { rcvTest  :: Bool
  , rcvId    :: Integer
  , rcvRanks :: [[Integer]]
  } deriving (Eq, Show)

-- | A PluralityVote represents a vote for a single candidate, as well
--   as a unique identifier for that vote.
data PluralityVote = PluralityVote
  { plTest   :: Bool
  , plId     :: Integer
  , plChoice :: Integer
  } deriving (Eq, Show)

-- | The results of an election include a winner as optionally a
--   record of how that winner was chosen by elimination of
--   successive candidates.
data Results = Results
  { rsWinner :: Integer
  , rsRecord :: Maybe [Record]
  } deriving (Eq, Show)

-- | A Record is a step in the vote-counting process, with a tally
--   of votes per candidate and a list of the eliminated candidates
data Record = Record
  { rcTally      :: [(Integer, Integer)]
  , rcEliminated :: [Integer]
  } deriving (Eq, Show)

-- To/FromJSON instances

class GetCandidates vote where
  getCandidates :: vote -> [Integer]

instance GetCandidates RCVVote where
instance GetCandidates PluralityVote where

instance (GetCandidates v, FromJSON v) => FromJSON (Election v) where
  parseJSON = withObject "election" $ \o -> do
    elIsTest   <- o .:? "isTest" .!= False
    elCounts   <- o .:? "counts"
    elVotes    <- o .:  "votes"
    elResults  <- o .:? "results"
    elTiebreak <- o .:? "tiebreak" .!= []
    let elCandidates = sortNub (concat (map getCandidates elVotes))
    return Election { .. }

instance ToJSON v => ToJSON (Election v) where
  toJSON Election { .. } = object
    $ optField "results" elResults
    [ "isTest"   .= elIsTest
    , "counts"   .= elCounts
    , "votes"    .= elVotes
    , "tiebreak" .= elTiebreak
    ]

instance FromJSON RCVVote where
  parseJSON = withObject "vote" $ \o -> do
    rcvTest  <- o .:? "test" .!= False
    rcvId    <- o .:  "id"
    rcvRanks <- o .:  "ranks"
    return RCVVote { .. }

instance ToJSON RCVVote where
  toJSON RCVVote { .. } = object $
    [ "id"    .= rcvId
    , "ranks" .= rcvRanks
    , "test"  .= rcvTest
    ]

instance FromJSON PluralityVote where
  parseJSON = withObject "vote" $ \o -> do
    plTest   <- o .:? "test" .!= False
    plId     <- o .:  "id"
    plChoice <- o .:  "selection"
    return PluralityVote { .. }

instance ToJSON PluralityVote where
  toJSON PluralityVote { .. } = object $
    [ "id"        .= plId
    , "selection" .= plChoice
    , "test"      .= plTest
    ]


instance FromJSON Results where
  parseJSON = withObject "result" $ \o -> do
    rsWinner <- o .:  "winner"
    rsRecord <- o .:? "record"
    return Results { .. }

instance ToJSON Results where
  toJSON Results { .. } = object
    $ optField "record" rsRecord
    [ "winner" .= rsWinner ]


instance FromJSON Record where
  parseJSON = withObject "record" $ \o -> do
    tallies      <- o .: "tally"
    rcTally      <- mapM go tallies
    rcEliminated <- o .: "eliminated"
    return Record { .. }
    where go = withObject "tally element" $ \o ->
            (,) <$> o .: "candidate" <*> o .: "firstChoices"

instance ToJSON Record where
  toJSON Record { .. } = object
    [ "tally" .= [ object [ "candidate" .= x
                          , "firstChoices" .= y
                          ]
                 | (x, y) <- rcTally
                 ]
    , "eliminated" .= rcEliminated
    ]

-- | If an election is a test and has a set of counts, we should
--   repeat each vote by that number of counts.
expandRCVTest :: Election v -> Election v
expandRCVTest e@Election
  { elIsTest = True
  , elCounts = Just ns
  , elVotes  = vs
  } = e { elVotes = Prelude.concat
                      [ replicate n v
                      | v <- vs
                      | n <- ns
                      ]
        }
expand e = e

sortNub :: Ord a => [a] -> [a]
sortNub = map head . group . sort

getElection :: (FromJSON v, GetCandidates v) => ByteString -> Either String (Election v)
getElection = eitherDecode

encodeElection :: ToJSON v => Election v -> ByteString
encodeElection = encode
