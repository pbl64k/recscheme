import Data.Functor

data I x = I x
data K x y = K x
data Sum x y z = SumL (x z) | SumR (y z)
data Prod x y z = Prod (x z) (y z)
data Mu x = In (x (Mu x))

instance Functor I where
    f `fmap` (I x) = I (f x)

instance Functor (K x) where
    f `fmap` (K x) = K x

instance (Functor x, Functor y) => Functor (Sum x y) where
    f `fmap` (SumL x) = SumL (f `fmap` x)
    f `fmap` (SumR y) = SumR (f `fmap` y)

instance (Functor x, Functor y) => Functor (Prod x y) where
    f `fmap` (Prod x y) = Prod (f `fmap` x) (f `fmap` y)

unI (I x) = x

unK (K x) = x

unSum f _ (SumL x) = f x
unSum _ g (SumR x) = g x

unProd f (Prod x y) = f x y

out (In x) = x

f `cata` (In x) = f ((f `cata`) `fmap` x)

f `ana` x = In ((f `ana`) `fmap` (f x))

type Nat = Mu (Sum (K ()) I)

showNat :: Nat -> Int
showNat = cata (unSum (const 0) (succ . unI))

readNat :: Int -> Nat
readNat = ana (\x -> if x == 0 then SumL (K ()) else SumR (I (pred x)))

zero :: Nat
zero = (In . SumL . K) ()

suc = In . SumR . I

prd = unSum (const zero) unI . out

plus x = cata (unSum (const x) (suc . unI))

mult x = cata (unSum (const zero) ((`plus` x) . unI))

type List a = Mu (Sum (K ()) (Prod (K a) I))

nil :: List a
nil = (In . SumL . K) ()

cons = ((In . SumR) .) . (Prod . K)

unf :: Nat -> List Nat
unf = ana (unSum (const (SumL (K ()))) ((\x -> SumR (Prod (K (suc x)) (I x))) . unI) . out)

prod :: List Nat -> Nat
prod = cata (unSum (const (suc zero)) (unProd (\x y -> (unK x) `mult` (unI y))))

fact = prod . unf

factorial = showNat . fact . readNat

