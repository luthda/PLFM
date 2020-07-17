module Exercise04 where

-- 4.1
halve :: [a] -> ([a],[a])
halve xs = splitAt ((length xs)`div`2) xs

-- 4.2
third :: [a] -> a
--third xs =  head(tail(tail xs))
--third xs = xs !! 2
third (_:_:x:_) = x

-- 4.3
safetail :: [a] -> [a]
--safetail xs = if null xs then [] else tail xs
{-safetail xs | null xs == True = []
            | otherwise = tail xs-}
safetail [] = []
safetail (_:xs) = xs

-- 4.4
{-
(||) :: Bool -> Bool -> Bool
True || True = True
True || False = True
False || True = True
False || False = False

False || False = False
_ || _ = True

False || b = b
True || _ = True

b || c | b == c = b
       | otherwise = True

a && b = if a then
            if b then True else False
         else
            False

a || b = if a then b else False
-}

-- 4.7
mult :: Int -> Int -> Int -> Int
--mult x y z = x * y * z
mult = \x -> (\y -> (\z -> x * y * z))

-- 4.8
luhnDouble :: Int -> Int
luhnDouble x = if x * 2 > 9 then x * 2 - 9 else x * 2

luhn :: Int -> Int -> Int -> Int -> Bool
luhn a b c d = if ( luhnDouble a + b + luhnDouble c + d) `mod` 10 == 0 then True else False