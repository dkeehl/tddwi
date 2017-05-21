module ConsoleIO

%default total

public export
data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

     Pure : a -> Command a
     Bind : Command a -> (a -> Command b) -> Command b

export
runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

public export
-- the argument of ConsoleIO, mainly to check the value returned by Quit
data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     -- the second argument of DO, a -> Inf (ConsoleIO b), which can use just
     -- Inf (ConsoleIO), is so designed to use the /do/ notation.
     DO : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
  export
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleIODo
  export
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = DO

public export
data Fuel = Dry | More (Lazy Fuel)

export
run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry _ = pure Nothing
run _ (Quit x) = pure (Just x)
run (More fuel) (DO c f) = do res <- runCommand c
                              run fuel (f res)

export
partial
forever : Fuel
forever = More forever
