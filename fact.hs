import Data.Functor

data I x = I { i :: x }
data K x y = K { k :: x }
data Sum x y z = SumL (x z) | SumR (y z)
data Prod x y z = Prod (x z) (y z)
data Mu x = In { out :: x (Mu x) }

instance Functor I where
    fmap = (I .) . (. i)

instance Functor (K x) where
    fmap = const (K . k)

instance (Functor x, Functor y) => Functor (Sum x y) where
    f `fmap` (SumL x) = SumL (f `fmap` x)
    f `fmap` (SumR y) = SumR (f `fmap` y)

instance (Functor x, Functor y) => Functor (Prod x y) where
    f `fmap` (Prod x y) = Prod (f `fmap` x) (f `fmap` y)

appI :: (a -> b) -> I a -> b
appI = (. i)

appK :: (a -> b) -> K a c -> b
appK = (. k)

appSum :: (a c -> d, b c -> d) -> Sum a b c -> d
(f, _) `appSum` (SumL x) = f x
(_, g) `appSum` (SumR x) = g x

appProd :: (a c -> b c -> d) -> Prod a b c -> d
f `appProd` (Prod x y) = f x y

-- Folds and unfolds for "free"!

cata :: Functor f => (f a -> a) -> Mu f -> a
cata f = f . ((f `cata`) `fmap`) . out

ana :: Functor f => (a -> f a) -> a -> Mu f
ana f = In . ((f `ana`) `fmap`) . f

-- Lfix T. 1 + T
type Nat = Mu (Sum (K ()) I)

showNat :: Nat -> Integer
showNat = (((const 0, (succ `appI`)) `appSum`) `cata`)

readNat :: Integer -> Nat
readNat = ((\x -> if x == 0 then SumL (K ()) else SumR (I (pred x))) `ana`)

zero :: Nat
zero = (In . SumL . K) ()

suc :: Nat -> Nat
suc = In . SumR . I

prd :: Nat -> Nat
prd = ((const zero, (id `appI`)) `appSum`) . out

plus :: Nat -> Nat -> Nat
plus x = (((const x, (suc `appI`)) `appSum`) `cata`)

mult :: Nat -> Nat -> Nat
mult x = (((const zero, ((`plus` x) `appI`)) `appSum`) `cata`)

-- Lfix T. 1 + A x T
type List a = Mu (Sum (K ()) (Prod (K a) I))

nil :: List a
nil = (In . SumL . K) ()

cons :: a -> List a -> List a
cons x = In . SumR . Prod (K x) . I

downto1 :: Nat -> List Nat
downto1 = ((((const (SumL (K ())), ((\x -> SumR (Prod (K (suc x)) (I x))) `appI`)) `appSum`) . out) `ana`)

prod :: List Nat -> Nat
prod = (((const (suc zero), ((\x y -> (id `appK` x) `mult` (id `appI` y)) `appProd`)) `appSum`) `cata`)

fact :: Nat -> Nat
fact = prod . downto1

factorial :: Integer -> Integer
factorial = showNat . fact . readNat

-- Can we do rose trees?
-- Sadly, List cannot be made into a functor without some fugly newtype juggling, but [] already is
-- The principle is exactly the same, though.

-- Lfix T. A x List T
type Rose a = Mu (Prod (K a) [])

-- ...and voila, our `cata` and `ana` just work.

divtree :: Integer -> Rose Integer
divtree = ((\n -> Prod (K n) (divisors n)) `ana`)

flatten :: Rose Integer -> [Integer]
flatten = (((\x xs -> (id `appK` x) : concat xs) `appProd`) `cata`)

divisors :: Integer -> [Integer]
divisors n = [x | x <- [2 .. n `div` 2], n `mod` x == 0]

