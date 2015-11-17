
module Main where

import SimpleGetOpt
import System.Directory (doesFileExist)
import System.Exit      (exitFailure, exitSuccess, ExitCode(..))
import System.FilePath  ((</>))
import System.IO
import System.Process

import Control.Monad (when, unless)

import qualified Data.ByteString.Lazy as B

import Text.Parsing.OpenRCVJSON

data Config =
  Config
    { confConstants :: FilePath
    , confTests     :: FilePath
    , confTestCase  :: Int
    , confVerbose   :: Bool
    , confExe       :: [String]
    } deriving (Show)

defaultConfig :: Config
defaultConfig = Config
  { confConstants = "constants.json"
  , confTests     = "irv.json"
  , confTestCase  = 1
  , confVerbose   = False
  , confExe       = []
  }


opts :: OptSpec Config
opts = OptSpec
  { progDefaults = defaultConfig
  , progParamDocs = [("EXE","executable under test")]
  , progParams    = \p s -> Right s { confExe = confExe s ++ [p] }
  , progOptions =
      [ Option ['c'] ["constants"]
        "JSON file containing \"candidate_name\" constants"
        $ ReqArg "FILE" $ \f s -> Right s { confConstants = f }

      , Option ['t'] ["tests"]
        "JSON file containing \"test_cases\""
        $ ReqArg "FILE" $ \f s -> Right s { confTests = f }

      , Option ['p'] ["rcv-path"]
        "Path to open-rcv-tests repository"
        $ ReqArg "PATH" $ \f s -> Right s
            { confConstants = f </> "tests/constants.json"
            , confTests = f </> "tests/irv.json"
            }
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
  verbose $ print c
  c_file <- getBSContents "constants" (confConstants c)
  candidates <- catchParseErr "constants" (getCandidates c_file)

  t_file <- getBSContents "tests" (confTests c)
  test <- catchParseErr "tests" (getTestCase (confTestCase c) t_file)

  verbose $ print candidates
  verbose $ print test

  let input = testInput candidates test
  verbose $ putStrLn "Test input:" >> putStrLn input

  output <- execSubprocess c input

  verbose $ putStrLn "Test output:" >> putStrLn output

  let r = testOutput test output

  case r of
    TestResultMatch -> do
      verbose $ putStrLn "PASS: Test matched expected output."
    TestResultMismatch s -> do
      verbose $ putStrLn "FAIL: Test did not match expected output."
      hPutStrLn stderr s
      exitFailure

  exitSuccess
  where
  verbose = when (confVerbose c)

execSubprocess :: Config -> String -> IO String
execSubprocess conf input = do
  when (null e) $ hPutStrLn stderr notest >> exitFailure
  (exitcode, output, err) <- readProcessWithExitCode cmd args input
  unless (null err) $ hPutStr stderr err
  case exitcode of
    ExitSuccess -> return output
    ExitFailure n -> hPutStrLn stderr (childfail n) >> exitFailure
  where
  e = confExe conf
  cmd = head e
  args = tail e
  notest = "Fatal: no executable under test given"
  childfail n = "Fatal: child process exited with error code " ++ show n

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


