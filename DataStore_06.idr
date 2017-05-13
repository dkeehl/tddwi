module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem
           = MkData schema _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) ->
                Vect (S old) (SchemaType schema)
    addToData [] = [newitem]
    addToData (item :: items') = item :: addToData items'

data Command : Schema -> Type where
     SetSchema : (newshema : Schema) -> Command schema
     Add : SchemaType schema -> Command schema
     Get : Integer -> Command schema
     GetAll : Command schema
     Quit : Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString item = getQuoted (unpack item)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"' :: xs) =
      case span (/= '"') xs of
        (quoted, '"' :: xs') => Just (pack quoted, ltrim (pack xs'))
        _ => Nothing
    getQuoted _ = Nothing

parsePrefix SInt item = case span isDigit item of
                             ("", _) => Nothing
                             (num, rest) => Just (cast num, ltrim rest)

parsePrefix SChar item = getChr (unpack item)
  where
    getChr : List Char -> Maybe (Char, String)
    getChr (x :: xs) = Just (x, ltrim (pack xs))
    getChr [] = Nothing

parsePrefix (schemal .+. schemar) item = do
  (l_val, rest) <- parsePrefix schemal item
  (r_val, rest') <- parsePrefix schemar rest
  Just ((l_val, r_val), rest')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = do (res, "") <- parsePrefix schema input
                                  | _ => Nothing
                                Just res

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) = case xs of
                                    [] => Just SString
                                    _  => do xs_sch <- parseSchema xs
                                             Just (SString .+. xs_sch)
parseSchema ("Int" :: xs) = case xs of
                                 [] => Just SInt
                                 _  => do xs_sch <- parseSchema xs
                                          Just (SInt .+. xs_sch)
parseSchema ("Char" :: xs) = case xs of
                                  [] => Just SChar
                                  _  => do xs_sch <- parseSchema xs
                                           Just (SChar .+. xs_sch)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) ->
               Maybe (Command schema)
parseCommand schema "add" rest = do restok <- parseBySchema schema rest
                                    Just (Add restok)
parseCommand schema "get" val = if val == ""
                                   then Just GetAll
                                   else if all isDigit (unpack val)
                                           then Just (Get (cast val))
                                           else Nothing
parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest = do schemaok <- parseSchema (words rest)
                                       Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (iteml, itemr)
        = display iteml ++ ", " ++ display itemr

getEntry : (pos : Integer) -> (store : DataStore) -> String
getEntry pos store =
  let store_items = items store in
      case integerToFin pos (size store) of
           Nothing => "Out of range\n"
           Just id => display (index id store_items) ++ "\n"

setSchema : DataStore -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                              Z   => Just (MkData schema _ [])
                              S _ => Nothing

listAll : DataStore -> String
listAll (MkData _ _ items) = listAll' 0 items
  where
    listAll' : Nat -> Vect n (SchemaType schema) -> String
    listAll' _ [] = ""
    listAll' k (x :: xs)
             = show k  ++ ": "  ++ display x ++ "\n" ++ listAll' (k + 1) xs

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp =
  case parse (schema store) inp of
       Nothing                   => Just ("Invalid command\n", store)
       Just (Add item)           =>
         Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
       Just (Get pos)            => Just (getEntry pos store, store)
       Just GetAll               => Just (listAll store, store)
       Just Quit                 => Nothing
       Just (SetSchema newshema) =>
         case setSchema store newshema of
              Nothing     =>
                Just ("Can't update schema when entries in store\n", store)
              Just store' => Just ("OK\n", store')

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
