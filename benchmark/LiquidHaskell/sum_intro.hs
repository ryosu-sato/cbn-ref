module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  assert (n <= sum_ n) ()
  where
    add :: Int -> Int -> Int
    add x y = x + y
    sum_ :: Int -> Int
    sum_ n
      | n <= 0 = 0
      | otherwise = add n (sum_ (n-1))

main :: IO ()
main = return ()
