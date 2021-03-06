{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}

module Main where

import           System.IO (stdin, stdout)
import           System.Exit (die)
import           Data.Aeson (eitherDecode, encode)
import qualified Data.ByteString.Lazy as B
import           Text.Parsing.ElectSON

import BinIntConvert
import SF_imp

main :: IO ()
main = do
  input <- B.hGetContents stdin
  election <- catchParseErr "election" (eitherDecode input)
  let results = run election
  B.hPut stdout (encode results)
  return ()

catchParseErr :: (Show a) => String -> Either String a -> IO a
catchParseErr _ (Right a) = return a
catchParseErr ctx (Left e) = die msg
  where msg = "Fatal: when parsing " ++ ctx ++ ": " ++ e


run :: Election RCVVote -> Maybe Results
run (Election {..}) = results
  where results = case winner of
          Just w -> Just $ Results
            { rsWinner = w
            , rsRecord =
                Just $ [ Record
                           { rcTally      = b
                           , rcEliminated = e
                           }
                       | e <- record
                       | b <- bins
                       ]
            }
          Nothing -> Nothing
        bins = fmap (fmap (fmap n2int)) bins'
        ((winner, record), bins') =
          run_election relDec tieBreak votes elCandidates
        votes = map rcvRanks elVotes

relDec :: Eq c => c -> c -> Bool
relDec = (==)

-- Picked arbitrarily
tieBreak :: [c] -> Maybe c
tieBreak [] = Nothing
tieBreak (c:_) = Just c
