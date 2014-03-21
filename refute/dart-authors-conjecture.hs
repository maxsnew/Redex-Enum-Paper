module Main where

import Test.QuickCheck

main :: IO ()
main = quickCheckWith stdArgs {maxSuccess=1000} prop_arith

prop_arith :: Int -> Int -> Bool
prop_arith x y = not ((x /= y) && (x*2 == x+10))
