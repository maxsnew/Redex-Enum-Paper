module Main where

{- To run:
$ cabal install quickcheck # if you don't have it

# and then either:
$ runhaskell isabelle-authors-conjecture

# or
$ ghc isabelle-authors-conjecture.hs
$ ./isabelle-authors-conjecture

-}

import Test.QuickCheck

main :: IO ()
main = quickCheckWith stdArgs {maxSuccess=1000} prop_append

safeBang :: [a] -> Int -> Maybe a
safeBang xs n = if (n >= 0) && (n < length xs)
                then Just $ xs !! n
                else Nothing
                     
prop_append :: [Int] -> [Int] -> Int -> Bool
prop_append xs ys n = ((xs ++ ys) `safeBang` (length xs + n)) == (xs `safeBang` n)
