module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> Int @-}
test :: Int -> Int
test n =
  assert False loop
  where
    loop :: Int
    loop = loop

main :: IO ()
main = return ()
