module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: Int -> () @-}
test :: Int -> ()
test n = assert (map_ (zip_ n n) == n) ()
  where
    f :: (Int -> Int -> Int) -> Int -> Int -> Int
    f g x y = g (x+1) (y+1)
    unzip_ :: Int -> (Int -> Int -> Int) -> Int
    unzip_ x k
      | x == 0 = k 0 0
      | otherwise = unzip_ (x-1) (f k)
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
    map_ :: Int -> Int
    map_ x
      | x == 0 = x
      | otherwise = 1 + map_ (x - 1)


main :: IO ()
main = return ()
