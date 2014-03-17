module Main where

{- To run:
$ cabal install quickcheck # if you don't have it
$ runhaskell isabelle-authors-conjecture
-}

import Test.QuickCheck

main :: IO ()
main = quickCheck (prop_append :: [Int] -> [Int] -> Int -> Bool)

prop_append xs ys n = (xs ++ ys) !! (length xs + n) == xs !! n
