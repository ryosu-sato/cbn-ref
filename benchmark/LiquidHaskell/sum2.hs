module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  assert (n <= sum_ n 0) ()
  where
    sum_ :: Int -> Int -> Int
    sum_ n a
      | n <= 0 = a
      | otherwise = n + sum_ (n-1) a

main :: IO ()
main = return ()
