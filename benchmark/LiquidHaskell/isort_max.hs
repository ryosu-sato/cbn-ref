module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ test :: (Int -> Int) -> Int -> Int @-}
test :: (Int -> Int) -> Int -> Int
test rnd n =
  if n > 1 then m else 0
  where
    m :: Int
    m = max_list rnd xs

    xs :: Int
    xs = make_list n

    max_list :: (Int -> Int) -> Int -> Int
    max_list rnd xs = hd rnd (isort rnd xs)

    make_list :: Int -> Int
    make_list n
      | n <= 0 = 0
      | otherwise = 1 + make_list (n-1)

    isort :: (Int -> Int) -> Int -> Int
    isort rnd xs
      | xs <= 1 = xs
      | otherwise =
        let x = rnd 0
            xs' = xs - 1 in
          insert rnd x (isort rnd xs')

    insert :: (Int -> Int) -> Int -> Int -> Int
    insert rnd x xs
      | rnd x == 0 = 1 + xs
      | otherwise = 1 + insert rnd x (xs - 1)

    hd :: (Int -> Int) -> Int -> Int
    hd rnd xs
      | xs <= 0 = assert False 0
      | otherwise = rnd 0

main :: IO ()
main = return ()
