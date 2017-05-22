import ConsoleIO

%default total

data Input = Cat String
           | Copy String String
           | Exit

parseHelp : String -> String -> Maybe Input
parseHelp "cat" rest = Just (Cat rest)
parseHelp "copy" rest = case words rest of
                             [arg1, arg2] => Just (Copy arg1 arg2)
                             _ => Nothing
parseHelp "exit" "" = Just Exit
parseHelp _ _ = Nothing

parseInput : String -> Maybe Input
parseInput input = let (cmd, args) = span (/= ' ') input in
                       parseHelp cmd (trim args)

usage : String
usage = "usage:\ncat [filename]\ncopy [source] [destination]\nexit\n"

mutual
  shell : ConsoleIO ()
  shell = do PutStr "> "
             input <- GetLine
             case parseInput input of
                  Just c => excuteCommand c
                  Nothing => do PutStr $ "Invalid command.\n" ++ usage
                                shell

  excuteCommand : Input -> ConsoleIO ()
  excuteCommand (Cat fn) = do Right s <- ReadFile fn
                                | Left err => errorHandler err
                              PutStr $ s ++  "\n"
                              shell
  excuteCommand (Copy src dest) = do Right s <- ReadFile src
                                       | Left err => errorHandler err
                                     Right () <- WriteFile dest s
                                       | Left err => errorHandler err
                                     shell
  excuteCommand Exit = Quit ()

  errorHandler : FileError -> ConsoleIO ()
  errorHandler err = do PutStr $ show err ++ "\n"
                        shell

partial
main : IO ()
main = do run forever shell
          pure ()
