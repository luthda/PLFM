module Exercise05 where

pairs :: [a] -> [(a,a)]
pairs xs = zip xs (tail xs)

calcPowerOf100 = sum [x^2 | x <- [1..100]]

-- 5.2
grid :: Int -> Int -> [(Int, Int)]
grid m n = [(x, y) | x <- [0..m], y <- [0..n]]

-- 5.3
square :: Int -> [(Int, Int)]
square n = [(x, y) | (x, y) <- grid n n, x /= y]

-- 5.4
replicate :: Int -> a -> [a]
replicate x a = [a | _ <- [1..x]]

-- 5.5
pyths :: Int -> [(Int, Int, Int)]
pyths n = [(x, y, z) | x <- [1..n], y <- [1..n], z <- [1..n], x^2 + y^2 == z^2]

all1 :: (a -> Bool) -> [a] -> Bool
all1 p xs = and [p x | x <- xs]

applyAndReturnAllElements p xs = [p x | x <- xs]
applyAndReturnFilteredElements p xs = [x | x <- xs, p x]