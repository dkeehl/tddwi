import System
import Data.Vect

-- 5.1
-- Exercise 1
printLonger : IO ()
printLonger = do str1 <- getLine
                 str2 <- getLine
                 printLn (max (length str1) (length str2))

-- Exercise 2
printLonger' : IO ()
printLonger' = getLine >>=
               \str1 => getLine >>=
               \str2 => printLn (max (length str1) (length str2))

-- 5.2
-- Exercise 1, 2 and 3
readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure (Just (cast input))
     else pure Nothing

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess n times = do
  putStr $ "Input a number to guess\n" ++ show times ++ ":"
  Just m <- readNumber
    | Nothing => do putStrLn "Invalid number, try again"
                    guess n times
  case compare m n of
       LT => do putStrLn "Too low, try again"
                guess n (times + 1)
       EQ => putStrLn "Correct"
       GT => do putStrLn "Too high, try again"
                guess n (times + 1)

main : IO ()
main = do n <- time
          let target = abs (mod n 100)
          guess (cast target) 1

-- Exercise 4
myRepl : (prompt : String) -> (onInput : String -> String) -> IO ()
myRepl prompt onInput = do
  putStr prompt
  str <- getLine
  putStr $ onInput str
  myRepl prompt onInput

myReplWith : (state : a) -> (prompt : String) ->
             (onInput : a -> String -> Maybe (String, a)) -> IO ()
myReplWith state prompt onInput = do
  putStr prompt
  str <- getLine
  case onInput state str of
       Nothing => pure ()
       Just (output, state') => do
         putStr output
         myReplWith state' prompt onInput

-- 5.3
-- Exercise 1
readToBlank : IO (List String)
readToBlank = do
  str <- getLine
  if str == ""
     then pure []
     else do strs <- readToBlank
             pure (str :: strs)

-- Exercise 2
readAndSave : IO ()
readAndSave = do
  putStrLn "Enter some words, blank line to end"
  xs <- readToBlank
  putStrLn "Enter a filename:"
  fname <- getLine
  Right _ <- writeFile fname (unlines xs)
    | Left err => putStrLn (show err)
  putStrLn $ "Wrote to file " ++ fname

-- Exercise 3
readLines : (f : File) -> IO (n : Nat ** Vect n String)
readLines f = do
  eof <- fEOF f
  if eof
     then pure (_ ** [])
     else do Right l <- fGetLine f | Left err => pure (_ ** [])
             (_ ** ls) <- readLines f
             pure (_ ** l :: ls)

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile fn = do
  Right f <- openFile fn Read | Left err => do putStrLn (show err)
                                               pure (_ ** [])
  contents <- readLines f
  closeFile f
  pure contents



















--
