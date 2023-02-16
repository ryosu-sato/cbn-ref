-- Main.hs
module Main where

{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ myDiv :: Int -> NonZero -> Int @-}
myDiv :: Int -> Int -> Int
myDiv = div

{-@ lazy main @-}
main :: IO ()
main = do
  n <- getLine
  m <- getLine
  case safeDiv (read n) (read m) of
    Just res -> print res
    Nothing -> do
      putStrLn "第二引数に0が入力されています"
      putStrLn "もう一度入力してください"
      main

{-@ safeDiv :: Int -> Int -> Maybe Int @-}
safeDiv :: Int -> Int -> Maybe Int
safeDiv n m
  | check     = Just $ div n m
  | otherwise = Nothing
  where
   check = True

{-@ checkedDiv :: Int -> {v: Int | v /= 0} -> Int @-}
checkedDiv :: Int -> Int -> Int
checkedDiv = div


{-@ assert :: {v:Bool | v} -> a -> a @-}
assert :: Bool -> a -> a
assert _ x = x

{-@ mysum :: x:Int -> {v:Int | v >= x} @-}
mysum :: Int -> Int
mysum n =
  if n <= 0 then
    0
  else
    n + mysum (n-1)

test :: Int -> Int
test n = assert (n <= mysum n) 0

{-@ udiv :: Int -> {v:Int | v != 0} -> Int @-}
udiv :: Int -> Int -> Int
udiv = div

test2 x =
  let z = collatz x in
  let z' = z + 1 in
  udiv x z'
  where
    collatz :: Int -> Int
    collatz n
      | n == 1 = 1
      | n `mod` 2 == 0 = collatz (n `udiv` 2)
      | otherwise = collatz (3*n+1)

test3 :: Int -> Int
test3 n =
  let r = loop + 1 in
  if 1 == n then
    assert False 0
  else
    1
  where
    loop :: Int
    loop = loop
