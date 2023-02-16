module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> Int -> Int -> () @-}
test :: Int -> Int -> Int -> ()
test x y z =
  let m = max_ f x y z in
  assert (f x m == m) ()
  where
    max_ :: (Int -> Int -> Int) -> Int -> Int -> Int -> Int
    max_ max2 x y z = max2 (max2 x y) z
    f :: Int -> Int -> Int
    f x y = if x >= y then x else y

main :: IO ()
main = return ()
