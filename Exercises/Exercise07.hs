module Exercise07 where

-- 7.1
mapAndFilter f p xs = Prelude.map f (Prelude.filter p xs)

-- 7.2
all :: (a -> Bool) -> [a] -> Bool
all p (x:xs) = and [p x | x <- xs]
-- all p = and . map p

any :: (a -> Bool) -> [a] -> Bool
any p (x:xs) = or [p x | x <- xs]
-- any p = or . map p

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile p (x:xs) | p x = x : Exercise07.takeWhile p xs
                   | otherwise = []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p (x:xs) | p x = Exercise07.dropWhile p xs
                   | otherwise = x:xs

-- 7.3
map f = foldr (\x xs -> f x : xs) []
filter p = foldr (\x xs -> if p x then x:xs else xs) []

-- 7.4
dec2int :: [Int] -> Int
dec2int = foldl (\x y -> 10 * x + y) 0

sum:: Num a => [a] -> a
sum xs = foldr (+) 0 xs