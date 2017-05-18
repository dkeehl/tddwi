data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a -> Vect k a -> Vect (S k) a

-- 7.1
-- Exercise 1
same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

-- Exercise 2
same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

-- Exercise 3
data ThreeEq : a -> b -> c -> Type where
     MkTreeEq : a = b -> b = c -> ThreeEq a b c

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x y z (MkTreeEq prf1 prf2) =
    MkTreeEq (cong prf1) (cong prf2)

-- 7.2
-- Exercise 1
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = let try = plusSuccRightSucc m k in
                             rewrite myPlusCommutes k m in try

-- Exercise 2
myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
        reverse' {n} {m = S k} acc (x :: xs) =
            let result = reverse' (x :: acc) xs in
                rewrite sym $ plusSuccRightSucc n k in result

-- 7.3
-- Exercise 1
headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
                  (contra : (x = y) -> Void) ->
                  ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
                  (contra : (xs = ys) -> Void) ->
                  ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

-- Exercise 2
DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) =
      case decEq x y of
           Yes Refl => case decEq xs ys of
                            Yes Refl => Yes Refl
                            No contra => No (tailUnequal contra)
           No contra => No (headUnequal contra)
