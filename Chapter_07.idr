-- 7.1
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

-- Exercise 1
Eq Shape where
   (==) (Triangle x z) (Triangle x' z') = x == x' && z == z'
   (==) (Rectangle x z) (Rectangle x' z') = x == x' && z == z'
   (==) (Circle x) (Circle x') = x == x'
   (==) _ _ = False

-- Exercise 2
area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Ord Shape where
    compare shape1 shape2 = compare (area shape1) (area shape2)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]

-- 7.2
data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

Num ty => Num (Expr ty) where
    (+) = Add
    (*) = Mul
    fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
    negate x = 0 - x
    (-) = Sub
    abs = Abs

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

-- Exercise 1
Show num => Show (Expr num) where
    show (Val x) = show x
    show (Add expr1 expr2) = "(" ++ show expr1 ++ " + " ++ show expr2 ++ ")"
    show (Sub expr1 expr2) = "(" ++ show expr1 ++ " - " ++ show expr2 ++ ")"
    show (Mul expr1 expr2) = "(" ++ show expr1 ++ " * " ++ show expr2 ++ ")"
    show (Div expr1 expr2) = "(" ++ show expr1 ++ " / " ++ show expr2 ++ ")"
    show (Abs x) = "|" ++ show x ++ "|"

-- Exercise 2
(Neg ty, Integral ty, Eq ty) => Eq (Expr ty) where
    (==) x y = eval x == eval y

-- Exercise 3
(Neg ty, Integral ty) => Cast (Expr ty) ty where
    cast expr = eval expr

-- 7.3
-- Exercise 1
Functor Expr where
    map f (Val x) = Val (f x)
    map f (Add expr1 expr2) = Add (map f expr1) (map f expr2)
    map f (Sub expr1 expr2) = Sub (map f expr1) (map f expr2)
    map f (Mul expr1 expr2) = Mul (map f expr1) (map f expr2)
    map f (Div expr1 expr2) = Div (map f expr1) (map f expr2)
    map f (Abs expr) = Abs (map f expr)

-- Exercise 2
data Vect : Nat -> Type -> Type where
    Nil : Vect Z ty
    (::) : ty -> Vect k ty -> Vect (S k) ty

Eq ty => Eq (Vect n ty) where
    (==) [] [] = True
    (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (Vect n) where
    foldr f acc [] = acc
    foldr f acc (x :: xs) = f x (foldr f acc xs)
