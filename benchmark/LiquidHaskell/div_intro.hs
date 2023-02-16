module Main where

{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ div_ :: Int -> {v:Int|v != 0} -> Int @-}
div_ :: Int -> Int -> Int
div_ = div

{-@ test :: (Int -> Int) -> Int -> Maybe Int @-}
test :: (Int -> Int) -> Int -> Maybe Int
test f n =
  if n <= 0 then Nothing else Just r
  where
    sum :: (Int -> Int) -> Int -> Int -> Int
    sum f i n
      | i >= n = 0
      | otherwise = f i + sum f (i+1) n
    unsafe_average f n = div_ (sum f 0 n) n
    r = unsafe_average f n

main :: IO ()
main = return ()
