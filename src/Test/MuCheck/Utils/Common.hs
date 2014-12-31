-- | Common functions used by MuCheck
module Test.MuCheck.Utils.Common where

import System.FilePath (splitExtension)
import System.Random
import Data.List

-- | The `choose` function generates subsets of a given size
choose :: [a] -> Int -> [[a]]
choose xs n = filter (\x -> length x == n) $ subsequences xs

-- | The `coupling` function produces all possible pairings, and applies the
-- given function to each
coupling :: Eq a => (a -> a -> t) -> [a] -> [t]
coupling fn ops = [fn o1 o2 | o1 <- ops, o2 <- ops, o1 /= o2]


-- | The `genFileNames` function lazily generates filenames of mutants
genFileNames :: String -> [String]
genFileNames s =  map newname [1..]
    where (name, ext) = splitExtension s
          newname :: Int -> String
          newname i= name ++ "_" ++ show i ++ ext

-- | The `replace` function replaces first element in a list given old and new values as a pair
replace :: Eq a => (a,a) -> [a] -> [a]
replace (o,n) lst = map replaceit lst
  where replaceit v
          | v == o = n
          | otherwise = v

-- | The `sample` function takes a random generator and chooses a random sample
-- subset of given size.
sample :: (RandomGen g) => g -> Int -> [t] -> [t]
sample _ 0 _ = []
sample g n xs = val : sample g' (n - 1) (remElt idx xs)
  where val = xs !! idx
        (idx,g')  = randomR (0, length xs - 1) g

-- | The `sampleF` function takes a random generator, and a fraction and
-- returns subset of size given by fraction
sampleF :: (RandomGen g) => g -> Rational -> [t] -> [t]
sampleF g f xs = sample g l xs
    where l = round $ f * fromIntegral (length xs)

-- | The `remElt` function removes element at index specified from a list
remElt :: Int -> [a] -> [a]
remElt idx xs = front ++ ack
  where (front,_:ack) = splitAt idx xs

-- | The `swapElts` function swaps two elements in a list given their indices
swapElts :: Int -> Int -> [t] -> [t]
swapElts i j ls = [get k x | (k, x) <- zip [0..length ls - 1] ls]
  where get k x | k == i = ls !! j
                | k == j = ls !! i
                | otherwise = x

-- | The `genSwapped` generates a list of lists where each element has been
-- swapped by another
genSwapped :: [t] -> [[t]]
genSwapped lst = map (\(x:y:_) -> swapElts x y lst) swaplst
  where swaplst = choose [0..length lst - 1] 2
