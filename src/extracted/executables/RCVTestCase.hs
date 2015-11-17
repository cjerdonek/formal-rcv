
module Main where

import SimpleGetOpt
import System.Exit      (exitFailure)
import System.Directory (doesFileExist)
import System.IO

import Control.Monad (when, unless)

import qualified Data.ByteString.Lazy as B

import Text.Parsing.OpenRCVJSON

data Config =
  Config
    { confConstants :: FilePath
    , confTests     :: FilePath
    , confTestCase  :: Int
    , confVerbose   :: Bool
    } deriving (Show)

defaultConfig :: Config
defaultConfig = Config
  { confConstants = "constants.json"
  , confTests     = "irv.json"
  , confTestCase  = 1
  , confVerbose   = False
  }


opts :: OptSpec Config
opts = OptSpec
  { progDefaults = defaultConfig
  , progParamDocs = []
  , progParams    = \_ _ -> Left "Invalid parameter"
  , progOptions =
      [ Option ['c'] ["constants"]
        "JSON file containing \"candidate_name\" constants"
        $ ReqArg "FILE" $ \f s -> Right s { confConstants = f }

      , Option ['t'] ["tests"]
        "JSON file containing \"test_cases\""
        $ ReqArg "FILE" $ \f s -> Right s { confTests = f }

      , Option ['a'] ["case"]
        "Test case index"
        $ ReqArg "INT" $ \a s -> case reads a of
            [(i,"")] -> Right s { confTestCase = i }
            _ -> Left ("\"" ++ a ++ "\" is not a valid test case index")

      , Option ['v'] ["verbose"]
        "Print debugging output"
        $ NoArg $ \s -> Right s { confVerbose = True }
      ]
  }

main :: IO ()
main = do
  conf <- getOpts opts
  run conf

run :: Config -> IO ()
run c = do
  when (confVerbose c) $ print c
  c_file <- getBSContents "constants" (confConstants c)
  candidates <- catchParseErr "constants" (getCandidates c_file)

  t_file <- getBSContents "tests" (confTests c)
  test <- catchParseErr "tests" (getTestCase (confTestCase c) t_file)

  print candidates
  print test

catchParseErr :: (Show a) => String -> Either String a -> IO a
catchParseErr _ (Right a) = return a
catchParseErr ctx (Left e) = hPutStrLn stderr msg >> exitFailure
  where msg = "Fatal: when parsing " ++ ctx ++ ": " ++ e

assertExists :: String -> FilePath -> IO ()
assertExists name fp = do
  e <- doesFileExist fp
  unless e $ do
    hPutStrLn stderr msg
    exitFailure
  where
  msg = "Fatal: no file at path given for " ++ name ++ ": " ++ fp

getBSContents :: String -> FilePath -> IO B.ByteString
getBSContents name fp = do
  assertExists name fp
  B.readFile fp


