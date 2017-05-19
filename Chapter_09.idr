-- 9.1
-- Exercise 1
data Elem : a -> List a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notThere : Elem value xs -> Void) ->
            (notHere : (value = x) -> Void) ->
            Elem value (x :: xs) -> Void
notInTail notThere notHere Here = notHere Refl
notInTail notThere notHere (There later) = notThere later

isElem : DecEq a => (value : a) -> (xs : List a) -> Dec (Elem value xs)
isElem value [] = No notInNil
isElem value (x :: xs)
    = case decEq value x of
           Yes Refl => Yes Here
           No notHere => case isElem value xs of
                              Yes prf => Yes (There prf)
                              No notThere => No (notInTail notThere notHere)

-- Exercise 2
data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value

notLastNil : Last [] value -> Void
notLastNil LastOne impossible
notLastNil (LastCons _) impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast contra (LastCons prf) = notLastNil prf

notLastCons : (contra : Last (y :: xs) value -> Void) ->
              Last (x :: (y :: xs)) value -> Void
notLastCons contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notLastNil
isLast [x] value = case decEq x value of
                        Yes Refl => Yes LastOne
                        No contra => No(notLast contra)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
                                   Yes prf => Yes (LastCons prf)
                                   No contra => No (notLastCons contra)
