import Data.Vect
allLengths : Vect len String -> Vect len Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

insert : Ord elem =>
         (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x (y :: xs) = case x < y of
                          False => y :: insert x xs
                          True => x :: y :: xs

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in
                        insert x xsSorted

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect len elem)) ->
                  Vect n (Vect (S len) elem)
--transposeHelper [] [] = []
--transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys
transposeHelper = zipWith (::)

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                         transposeHelper x xsTrans

addMatHelper : Num a => (x : Vect m a) -> (y : Vect m a) ->
                        (xsAdd : Vect len (Vect m a)) ->
                        Vect (S len) (Vect m a)
addMatHelper x y xsAdd = zipWith (+) x y :: xsAdd

addMatrix : Num a =>
            Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = let xsAdd = addMatrix xs ys in
                                    addMatHelper x y xsAdd

dotProduct : Num a => (x : Vect m a) -> (y : Vect m a) -> a
dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) = x * y + dotProduct xs ys

multVectToMat : Num a =>
                (x : Vect m a) -> (ysTrans : Vect p (Vect m a)) -> Vect p a
multVectToMat x [] = []
multVectToMat x (y :: xs) = dotProduct x y :: multVectToMat x xs

multMatrixHelper : Num a =>
                   (xs : Vect n (Vect m a)) ->
                   (ysTrans : Vect p (Vect m a)) ->
                   Vect n (Vect p a)
multMatrixHelper [] ysTrans = []
multMatrixHelper (x :: xs) ysTrans =
  let xsProduct = multMatrixHelper xs ysTrans in
      multVectToMat x ysTrans :: xsProduct

multMatrix : Num a =>
             Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix xs ys = let ysTrans = transposeMat ys in
                       multMatrixHelper xs ysTrans
