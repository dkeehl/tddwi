VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

strToInput : String -> Maybe Input
strToInput "insert" = Just COIN
strToInput "vend" = Just VEND
strToInput "change" = Just CHANGE
strToInput x = if all isDigit (unpack x)
                  then Just (REFILL (cast x))
                  else Nothing

data CoinResult = Inserted | Rejected

data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
     InsertCoin : MachineCmd CoinResult (pounds, chocs)
                             (\res => case res of
                                           Inserted => (S pounds, chocs)
                                           Rejected => (pounds, chocs))
     Vend       : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
     GetCoins   : MachineCmd () (pounds, chocs)     (const (Z, chocs))

     Display : String ->
                  MachineCmd () state               (const state)
     Refill : (bars : Nat) ->
                  MachineCmd () (Z, chocs)          (const (Z, bars + chocs))

     GetInput : MachineCmd (Maybe Input) state (const state)

     Pure : (res : ty) -> MachineCmd ty (state_fn res)  state_fn
     (>>=) : MachineCmd a state1 state2_fn ->
             ((res : a) -> MachineCmd b (state2_fn res) state3_fn) ->
             MachineCmd b state1 state3_fn

data MachineIO : VendState -> Type where
     Do : MachineCmd a state1 state2_fn ->
          ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1

runMachine : MachineCmd ty inState outState_fn -> IO ty
runMachine InsertCoin = do putStr "Press 1 to insert a coin\n"
                           "1" <- getLine | _ => do putStrLn "Coin rejected"
                                                    pure Rejected
                           putStrLn "Coin inserted"
                           pure Inserted
runMachine Vend = putStrLn "Please take your chocolate"
runMachine {inState = (pounds, _)} GetCoins
     = putStrLn (show pounds ++ " coins returned")
runMachine (Display str) = putStrLn str
runMachine (Refill bars)
     = putStrLn ("Chocolate remaining: " ++ show bars)
runMachine {inState = (pounds, chocs)} GetInput
     = do putStrLn ("Coins: " ++ show pounds ++ "; " ++
                    "Stock: " ++ show chocs)
          putStr "> "
          x <- getLine
          pure (strToInput x)
runMachine (Pure x) = pure x
runMachine (cmd >>= prog) = do x <- runMachine cmd
                               runMachine (prog x)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> MachineIO state -> IO ()
run (More fuel) (Do c f)
     = do res <- runMachine c
          run fuel (f res)
run Dry p = pure ()


namespace MachineDo
  (>>=) : MachineCmd a state1 state2_fn ->
          ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = S p} {chocs = S c} = do Vend
                                         Display "Enjoy!"
                                         machineLoop
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop

  refill : (num : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill _ = do Display "Can't refill: Coins in machine"
                machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop =
       do Just x <- GetInput | Nothig => do Display "Invalid input"
                                            machineLoop
          case x of
              COIN => do Inserted <- InsertCoin | Rejected => machineLoop
                         machineLoop
              VEND => vend
              CHANGE => do GetCoins
                           Display "Change returned"
                           machineLoop
              REFILL num => refill num

main : IO ()
main = run forever (machineLoop {pounds = 0} {chocs = 1})
