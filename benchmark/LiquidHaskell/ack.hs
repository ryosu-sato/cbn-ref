module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> Int -> () @-}
test :: Int -> Int -> ()
test m n =
  if m>=0 && n>=0 then assert (ackermann m n >= n) () else ()
  where
    ackermann :: Int -> Int -> Int
    ackermann m n
      | m == 0    = n + 1
      | n == 0    = ackermann (m-1) 1
      | otherwise = ackermann (m-1) (ackermann m (n-1))

main :: IO ()
main = return ()
