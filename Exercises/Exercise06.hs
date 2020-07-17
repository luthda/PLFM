module Exercise06 where

-- 6.1
factorial 0 = 1
factorial n | n > 0 = n * factorial (n - 1)

-- 6.2
sumdown :: Int -> Int
sumdown 0 = 0
sumdown x = x + sumdown (x - 1)

-- 6.3
(^) :: Int -> Int -> Int
x ^ 0 = 1
x ^ y = x * (x Exercise06.^ (y - 1))

-- 6.6
and :: [Bool] -> Bool
and [] = True
and (bool:bools) = if bool == True then Exercise06.and (bools) else False

concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) = x ++ Exercise06.concat xs

replicate :: Int -> a -> [a]
replicate 0 x = []
replicate n x = x : Exercise06.replicate (n - 1) x

(!!) :: [a] -> Int -> a
(x:_) !! 0 = x
(_:xs) !! n = xs Exercise06.!! (n-1)

elem :: Eq a => a -> [a] -> Bool
elem _ [] = False
elem x (y:ys) = if x == y then True else Exercise06.elem x ys

even :: Int -> Bool
even 0 = True
even n = Exercise06.even (n-2)

len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs

qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort smaller ++ [x] ++ qsort bigger
                where
                  smaller = [s | s <- xs, s <= x]
                  bigger = [b | b <- xs, b > x]
