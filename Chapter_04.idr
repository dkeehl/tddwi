module Chapter4

import Data.Vect

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

%name Tree tree, tree1

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x tree@(Node left val right) =
  case compare x val of
       LT => Node (insert x left) val right
       EQ => tree
       GT => Node left val (insert x right)

-- 4.1
-- Exercise 1
listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

-- Exercise 2
treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = treeToList left ++ [x] ++ treeToList right

-- Exercise 3
data Expr = Val Int
          | Add Expr Expr
          | Sub Expr Expr
          | Mult Expr Expr

-- Exercise 4
evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mult x y) = evaluate x * evaluate y

-- Exercise 5
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) =
  if x > y then Just x else Just y

-- Exercise 6
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))
testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive triangle@(Triangle _ _)) = Just (area triangle)
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

-- 4.2
-- Exercise 1 and 2
data PowerSource = Petrol | Pedal | Electric
data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Electriccar : Vehicle Electric

-- Exercise 3 and 4
vectTake : (m : Nat) -> Vect (m + n) elem -> Vect m elem
vectTake Z _ = []
vectTake (S k) (x :: xs) = x :: vectTake k xs

-- Exercise 5
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
  case integerToFin pos n of
       Nothing  => Nothing
       Just idx => Just (index idx xs + index idx ys)

-- 4.3
-- See DataStore.idr
