module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> Int -> {v:Bool | v} @-}
test :: Int -> Int -> Bool
test m n =
  ackermann m n >= n
  where
    ackermann :: Int -> Int -> Int
    ackermann m n
      | m == 0    = n + 1
      | n == 0    = ackermann (m-1) 1
      | otherwise = ackermann (m-1) (ackermann m (n-1))

{-@ test2 :: Int -> Int -> {v:Bool | v} @-}
test2 :: Int -> Int -> Bool
test2 m n =
  ackermann m n >= n
  where
    ackermann :: Int -> Int -> Int
    ackermann m n
      | m == 0    = n + 1
      | otherwise = n

main :: IO ()
main = return ()
