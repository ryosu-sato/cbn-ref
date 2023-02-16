module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  assert (n <= mult n n) ()
  where
    mult :: Int -> Int -> Int
    mult n m
      | n <= 0 || m <= 0 = 0
      | otherwise = n + mult n (m-1)

main :: IO ()
main = return ()
