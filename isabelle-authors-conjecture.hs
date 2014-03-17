module Main where

{- To run:
$ cabal install quickcheck # if you don't have it
$ runhaskell isabelle-authors-conjecture
-}

import Test.QuickCheck

main :: IO ()
main = quickCheck (prop_append :: [Int] -> [Int] -> Int -> Bool)

safeBang :: [a] -> Int -> Maybe a
safeBang xs n = if (n >= 0) && (n < length xs)
                then Just $ xs !! n
                else Nothing
                     
prop_append xs ys n = ((xs ++ ys) `safeBang` (length xs + n)) == (xs `safeBang` n)
