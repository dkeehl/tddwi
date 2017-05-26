import Data.Vect

-- 13.1
-- Exercise 1
namespace Door
  data DoorState = DoorClosed | DoorOpen

  data DoorCmd : Type -> DoorState -> DoorState -> Type where
       Open : DoorCmd () DoorClosed DoorOpen
       Close : DoorCmd () DoorOpen DoorClosed
       RingBell : DoorCmd () state state

       Pure : ty -> DoorCmd ty state state
       (>>=): DoorCmd a state1 state2 ->
              (a -> DoorCmd b state2 state3) ->
              DoorCmd b state1 state3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do RingBell
              Open
              RingBell
              Close

-- Exercise 2
namespace Guess
  data GuessCmd : Type -> Nat -> Nat -> Type where
       Try : Integer -> GuessCmd Ordering (S k) k

       Pure : ty -> GuessCmd ty state state
       (>>=) : GuessCmd a state1 state2 ->
               (a -> GuessCmd b state2 state3) ->
               GuessCmd b state1 state3

threeGuesses : GuessCmd () 3 0
threeGuesses = do Try 10
                  Try 20
                  Try 15
                  Pure ()

-- Exercise 3
namespace Matter
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
       Melt : MatterCmd () Solid Liquid
       Boil : MatterCmd () Liquid Gas
       Condense : MatterCmd () Gas Liquid
       Freeze : MatterCmd () Liquid Solid

       Pure : ty -> MatterCmd ty state state
       (>>=): MatterCmd a state1 state2 ->
              (a -> MatterCmd b state2 state3) ->
              MatterCmd b state1 state3

iceSteam : MatterCmd () Solid Gas
iceSteam = do Melt
              Boil

steamIce : MatterCmd () Gas Solid
steamIce = do Condense
              Freeze

-- 13.2
-- Exercise 1, 2, 3, 4
data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop : StackCmd Integer (S height) height
     Top : StackCmd Integer (S height) (S height)

     GetStr : StackCmd String height height
     PutStr : String -> StackCmd () height height

     Pure : ty -> StackCmd ty height height
     (>>=) : StackCmd a height1 height2 ->
             (a -> StackCmd b height2 height3) ->
             StackCmd b height1 height3

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight ->
           IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: stk) Pop = pure (x, stk)
runStack stk@(x :: xs) Top = pure (x, stk)
runStack stk GetStr = do str <- getLine
                         pure (str, stk)
runStack stk (PutStr str) = do putStr str
                               pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do (val, newStack) <- runStack stk x
                            runStack newStack (f val)

data StackIO : Nat -> Type where
     Do : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 ->
          (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry _ _ = pure ()
run (More fuel) stk (Do c f) = do (val, newStack) <- runStack stk c
                                  run fuel newStack (f val)

data StkInput = Number Integer
              | Add
              | Subtruct
              | Multiply
              | Negate
              | Discard
              | Duplicate

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtruct" = Just Subtruct
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Duplicate
strToInput str = if all isDigit (unpack str)
                    then Just (Number (cast str))
                    else Nothing

mutual
  stackCalc : StackIO height
  stackCalc = do PutStr "> "
                 input <- GetStr
                 case strToInput input of
                      Nothing => do PutStr "Invalid input\n"
                                    stackCalc
                      Just (Number x) => do Push x
                                            stackCalc
                      Just Add => tryAdd
                      Just Subtruct => trySub
                      Just Multiply => tryMult
                      Just Negate => tryNeg
                      Just Discard => tryDiscard
                      Just Duplicate => tryDup

  tryAdd : StackIO height
  tryAdd = applyTwo (+)

  trySub : StackIO height
  trySub = applyTwo (-)

  tryMult : StackIO height
  tryMult = applyTwo (*)

  tryNeg: StackIO height
  tryNeg {height = S k} = do x <- Pop
                             Push (- x)
                             PutStr $ show (- x) ++ "\n"
                             stackCalc
  tryNeg {height = Z} = noItem

  tryDiscard : StackIO height
  tryDiscard {height = S k} = do x <- Pop
                                 PutStr $ "Discarded " ++ show x ++ "\n"
                                 stackCalc
  tryDiscard {height = Z} = noItem

  tryDup : StackIO height
  tryDup {height = S k} = do x <- Top
                             Push x
                             PutStr $ "Duplicated " ++ show x ++ "\n"
                             stackCalc
  tryDup {height = Z} = noItem

  noItem : StackIO Z
  noItem = do PutStr "No item on stack\n"
              stackCalc

  applyTwo : (Integer -> Integer -> Integer) -> StackIO height
  applyTwo {height = S (S k)} f = do x <- Pop
                                     y <- Pop
                                     Push (f x y)
                                     PutStr $ show (f x y) ++ "\n"
                                     stackCalc
  applyTwo _ = do PutStr "Fewer than two items on stack\n"
                  stackCalc

partial
main : IO ()
main = run forever [] stackCalc
