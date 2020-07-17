module Exercise01 where

xs :: [Int]
xs = [1, 2, 3, 4, 5]

add' x y = x + y

-- 1.3
product :: [Int] -> Int
product [] = 1
product (x:xs) = x * Exercise01.product xs

-- 1.4
qsort [] = []
qsort (x:xs) = qsort larger ++ [x] ++ qsort smaller
               where
                  smaller = [a | a <- xs, a <= x]
                  larger = [a | a <- xs, a > x]