module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  if n <= 101 then
    assert (mc91 n == 91) ()
  else
    ()
  where
    mc91 :: Int -> Int
    mc91 x
      | x > 100 = x - 10
      | otherwise = mc91 (mc91 (x + 11))

main :: IO ()
main = return ()
