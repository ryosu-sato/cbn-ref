module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  assert (copy (copy n) == n) ()
  where
    copy :: Int -> Int
    copy x =
      if x == 0
      then 0
      else 1 + copy (x-1)

main :: IO ()
main = return ()
