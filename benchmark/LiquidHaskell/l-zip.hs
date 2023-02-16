module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> Int -> Int @-}
test :: Int -> Int -> Int
test n m = if n == m then r else 0
  where
    r = zip_ n m
    zip_ :: Int -> Int -> Int
    zip_ x y
      | x == 0 =
          if y == 0 then
            x
          else
            assert False 0
      | otherwise =
          if y == 0 then
            assert False 0
          else
            1 + zip_ (x - 1) (y - 1)

main :: IO ()
main = return ()
