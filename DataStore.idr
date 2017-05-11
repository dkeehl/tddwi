module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData s items) = s

items : (store : DataStore) -> Vect (size store) String
items (MkData s items) = items

addToStore : DataStore -> String -> DataStore
addToStore (MkData s items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'

data Command = Add String
             | Get Integer
             | Search String
             | Size
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True  => Just (Get (cast val))
parseCommand "search" str = Just (Search str)
parseCommand "size" "" = Just Size
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => Just ("Out of Range\n", store)
           Just id => Just (index id store_items ++ "\n", store)

searchString_ : Vect n String -> String -> String
searchString_ items {n} str = showLines (findIndices (isInfixOf str) items)
  where
    showLines : List (Fin m) -> String
    showLines [] = ""
    showLines (i :: is) =
      let i' = finToInteger i in
          -- adding this to pass type checking
          -- the Nothing case is impossible, for m is never greater than n 
          case integerToFin i' n of
               Nothing => ""
               Just id =>
                 show i' ++ ": " ++ index id items ++ "\n" ++ showLines is

searchString : (store : DataStore) -> (str : String) -> String
searchString (MkData _ items) str =
  case searchString_ items str of
       "" => "Can't find " ++ str ++ "\n"
       _  => searchString_ items str

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse inp of
       Nothing           => Just ("Invalid command\n", store)
       Just (Add item)   =>
         Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
       Just (Get pos)    => getEntry pos store
       Just (Search str) => Just (searchString store str, store)
       Just Size         => Just (show (size store) ++ "\n", store)
       Just Quit         => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
