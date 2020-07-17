module Exercise02 where

--2.1
double :: Num a => a -> a
double x = x + x

quadruple x = double (double x)

factorial n = product [1..n]

-- average ns = sum ns `div` length ns

-- 2.4
last xs = head (reverse xs)

--2.5
init xs = take (length xs - 1) xs