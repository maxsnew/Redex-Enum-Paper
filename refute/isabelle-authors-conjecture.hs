module Main where
import Test.QuickCheck

-- START
main :: IO ()
main = quickCheckWith 
       stdArgs {maxSuccess=1000} 
       prop

nth :: [a] -> Int -> Maybe a
nth xs n = if (n >= 0) && (n < length xs)
           then Just (xs !! n)
           else Nothing
                     
prop :: [Int] -> [Int] -> Int -> Bool
prop xs ys n = 
  (nth (xs ++ ys) (length xs + n)) == 
  (nth xs n)
-- STOP

