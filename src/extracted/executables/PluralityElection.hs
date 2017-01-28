{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}

module Main where

import           System.IO (stdin, stdout)
import           System.Exit (die)
import           Data.Aeson (eitherDecode, encode)
import qualified Data.ByteString.Lazy as B
import           Text.Parsing.ElectSON

import BinIntConvert
import Plurality

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

run :: Election PluralityVote -> Maybe Results
run (Election {..}) = results
  where results = case winner of
          Just w -> Just $ Results
            { rsWinner = w
            , rsRecord = Nothing
            }
          Nothing -> Nothing
        winner = runPluralityElection (==) votes
        votes = map plChoice elVotes

relDec :: Eq c => c -> c -> Bool
relDec = (==)
