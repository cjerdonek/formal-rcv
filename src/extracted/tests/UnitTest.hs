{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
module Main (main) where

import Test.Tasty
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML
import Test.Tasty.QuickCheck

import Sf_tests

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

main :: IO ()
main = tests >>= defaultMainWithIngredients ingrs

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients

tests :: IO TestTree
tests = return $ localOption (QuickCheckTests 10000) $
  testGroup "SF Tests" $
  [ testProperty "drop_none_keeps" prop_drop_none_keeps
  , testProperty "next_ranking_contains" prop_next_ranking_contains
  , testProperty "next_ranking_not_eliminated" prop_next_ranking_not_eliminated
  , testProperty "next_ranking_not_overvote" prop_next_ranking_not_overvote
  ] 
