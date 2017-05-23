import Control.Monad.State

-- 12.1
-- Exercise 1
update : (stateType -> stateType) -> State stateType ()
update f = do state <- get
              put (f state)

increase : Nat -> State Nat ()
increase x = update (+x)

-- Exercise 2
data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                      (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node ltree val rtree) = do countEmpty ltree
                                       countEmpty rtree

-- Exercise 3
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = do (empty, node) <- get
                          put (empty + 1, node)
countEmptyNode (Node ltree x rtree) = do countEmptyNode ltree
                                         countEmptyNode rtree
                                         (empty, node) <- get
                                         put (empty, node + 1)

-- 12.3
record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

     GetRandom : Command Int
     GetGameState : Command GameState
     PutGameState : GameState -> Command ()

     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

-- Exercise 2
mutual
  Functor Command where
    map func c = do res <- c
                    pure (func res)

  Applicative Command where
    pure = Pure
    (<*>) mf mx = do f <- mf
                     x <- mx
                     pure (f x)

  Monad Command where
    (>>=) = Bind

-- Exercise 1
updatGameState : (GameState -> GameState) -> Command ()
updatGameState f = do st <- GetGameState
                      PutGameState (f st)

-- Exercise 3
record Votes where
       constructor MkVotes
       upvotes : Integer
       downvotes : Integer

record Article where
       constructor MkArticle
       title : String
       url : String
       score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore a = upvotes (score a) - downvotes (score a)

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)
goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

-- Exercise 4
addUpvote : Article -> Article
addUpvote = record { score->upvotes $= (+1) }

addDownvote : Article -> Article
addDownvote = record { score->downvotes $= (+1) }
