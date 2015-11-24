
module Main where

import System.IO
import System.Exit
import qualified Data.ByteString.Lazy as B
import Text.Parsing.ElectSON

main :: IO ()
main = do
  input <- B.hGetContents stdin
  election <- catchParseErr "election" (getElection input)
  hPutStrLn stderr (show election)
  return ()

catchParseErr :: (Show a) => String -> Either String a -> IO a
catchParseErr _ (Right a) = return a
catchParseErr ctx (Left e) = hPutStrLn stderr msg >> exitFailure
  where msg = "Fatal: when parsing " ++ ctx ++ ": " ++ e
