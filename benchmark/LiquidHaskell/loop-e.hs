module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n =
  let r = loop in
    assert False ()
  where
    loop :: Int
    loop = loop

main :: IO ()
main = return ()
