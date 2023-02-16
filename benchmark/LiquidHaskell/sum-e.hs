module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  assert (n+1 <= sum_ n) ()
  where
    sum_ :: Int -> Int
    sum_ n
      | n <= 0 = 0
      | otherwise = n + sum_ (n-1)

main :: IO ()
main = return ()
