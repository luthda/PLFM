module Exercise03 where

-- 3.2
bools :: [Bool]
bools = [True, False, False, True]

nums :: [[Int]]
nums = [[1,2],[2,3]]

add :: Int -> Int -> Int -> Int
add x y z  = x + y + z

copy :: a -> (a, a)
copy x = (x ,x)

apply :: (a -> b) -> a -> b
apply f x = f x




