import Data.Primitives.Views
import ConsoleIO
import System

%default total

-- 11.1
-- Exercise 1
every_other : Stream a -> Stream a
every_other (x :: x' :: xs) = x' :: every_other xs

-- Exercise 2
data InfList : Type -> Type where
     (::) : (x : a) -> (xs : Inf (InfList a)) -> InfList a

Functor InfList where
  map f (x :: xs) = f x :: map f xs

-- Exercise 3
data Face = Head | Tail

getFace : Int -> Face
getFace x with (divides x 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem == 0 then Head else Tail

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count = map getFace . take count

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

-- Exercise 4
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx
    = let next = (approx + (number / approx)) / 2 in
          approx :: square_root_approx number next

square_root_bound : (max : Nat) -> (number : Double) -> (bound : Double) ->
                    (approxs : Stream Double) -> Double
square_root_bound Z number bound (value :: xs) = value
square_root_bound (S k) number bound (value :: xs)
    = let diff = abs $ value * value - number in
          if diff < bound
             then value
             else square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001 $
                     square_root_approx number number

-- 11.2
data InfIO : Type where
     Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

run : Fuel -> InfIO -> IO ()
run Dry _ = putStrLn "Out of fuel"
run (More fuel) (Do c f) = do res <- c
                              run fuel (f res)

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do putStr prompt
                             res <- getLine
                             putStr $ action res
                             totalREPL prompt action

-- 11.3
-- Exercise 1
data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                         then Pure QuitCmd
                         else Pure (Answer $ cast answer)

mutual
  quiz : Stream Int -> (times : Nat) -> (score : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) times score
      = do PutStr
             ("Score so far: " ++ show score ++ " / " ++ show times ++ "\n")
           -- here (>>=) is Bind
           input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ? ")
           -- here (>>=) is DO
           case input of
                Answer answer => if answer == num1 * num2
                                    then correct nums times score
                                    else wrong nums (num1 * num2) times score
                QuitCmd => Quit (score, times)

  correct : Stream Int -> (times : Nat) -> (score : Nat) -> ConsoleIO (Nat, Nat)
  correct nums times score = do PutStr "Correct!\n"
                                quiz nums (times + 1) (score + 1)

  wrong : Stream Int -> (answer : Int) ->  (times : Nat) -> (score : Nat) ->
          ConsoleIO (Nat, Nat)
  wrong nums answer times score
      = do PutStr ("Wrong, the answer is " ++ show answer ++ "\n")
           quiz nums (times + 1) score

arithInputs : (seed : Int) -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

partial
main : IO ()
main = do seed <- time
          Just (score, times) <- run forever $
            quiz (arithInputs (fromInteger seed)) 0 0
            | Nothing => putStrLn "Run out of fuel"
          putStrLn ("Final score: " ++ show score ++ " / " ++ show times)
