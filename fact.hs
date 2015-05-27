{-# LANGUAGE TypeOperators #-}

import Data.Functor

data Id x = I { i :: x }
data Const x y = K { k :: x }
data (x :+: y) z = SumL (x z) | SumR (y z)
data (x :*: y) z = Prod (x z) (y z)
data Fix x = In { out :: x (Fix x) }

data Zero
type One = Const ()

instance Functor Id where
    fmap = (I .) . (. i)

instance Functor (Const x) where
    fmap = const (K . k)

instance (Functor x, Functor y) => Functor (x :+: y) where
    f `fmap` (SumL x) = SumL (f `fmap` x)
    f `fmap` (SumR y) = SumR (f `fmap` y)

instance (Functor x, Functor y) => Functor (x :*: y) where
    f `fmap` (Prod x y) = Prod (f `fmap` x) (f `fmap` y)

appI :: (a -> b) -> Id a -> b
appI = (. i)

appK :: (a -> b) -> Const a c -> b
appK = (. k)

appSum :: (a c -> d, b c -> d) -> (a :+: b) c -> d
(f, _) `appSum` (SumL x) = f x
(_, g) `appSum` (SumR x) = g x

appProd :: (a c -> b c -> d) -> (a :*: b) c -> d
f `appProd` (Prod x y) = f x y

-- Folds and unfolds for "free"!

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . (fmap $ cata f) . out

ana :: Functor f => (a -> f a) -> a -> Fix f
ana f = In . (fmap $ ana f) . f

-- Lfix T. 1 + T
type Nat = Fix (One :+: Id)

showNat :: Nat -> Integer
showNat = cata $ appSum (const 0, appI succ)

readNat :: Integer -> Nat
readNat = ana (\x -> if x == 0 then SumL $ K () else SumR $ I $ pred x)

zero :: Nat
zero = In $ SumL $ K ()

suc :: Nat -> Nat
suc = In . SumR . I

prd :: Nat -> Nat
prd = appSum (const zero, i) . out

plus :: Nat -> Nat -> Nat
plus x = cata $ appSum (const x, appI suc)

mult :: Nat -> Nat -> Nat
mult x = cata $ appSum (const zero, appI (`plus` x))

-- Lfix T. 1 + A x T
type List a = Fix (One :+: (Const a :*: Id))

nil :: List a
nil = In $ SumL $ K ()

cons :: a -> List a -> List a
cons x = In . SumR . Prod (K x) . I

downto1 :: Nat -> List Nat
downto1 = ana (appSum (const $ SumL $ K (), appI (\x -> SumR $ Prod (K $ suc x) (I x))) . out)

prod :: List Nat -> Nat
prod = cata $ appSum (const $ suc zero, appProd (\x y -> (k x) `mult` (i y)))

fact :: Nat -> Nat
fact = prod . downto1

factorial :: Integer -> Integer
factorial = showNat . fact . readNat

-- Can we do rose trees?
-- Sadly, List cannot be made into a functor without some fugly newtype juggling, but [] already is
-- The principle is exactly the same, though.

-- Lfix T. A x List T
type Rose a = Fix (Const a :*: [])

-- ...and voila, our `cata` and `ana` just work.

divtree :: Integer -> Rose Integer
divtree = ana (\n -> Prod (K n) (divisors n))

flatten :: Rose Integer -> [Integer]
flatten = cata $ appProd (\x xs -> k x : concat xs)

divisors :: Integer -> [Integer]
divisors n = [x | x <- [2 .. n `div` 2], n `mod` x == 0]

main = do
    putStrLn $ show $ showNat ((readNat 3) `mult` (readNat 7))
    putStrLn $ show $ factorial 7
    putStrLn $ show $ flatten $ divtree 72

