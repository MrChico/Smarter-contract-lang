import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

--The state is kept in a simple key-value mapping
balances = Map.singleton "0x1" 100

zeroAsDefault :: Maybe Int -> Int ; zeroAsDefault mx = case mx of {Nothing -> 0; Just x -> x}

transfer :: String -> String -> Int -> State (Map.Map String Int) ()
transfer from to n = do
  bal <- get
  let fromBal = zeroAsDefault $ Map.lookup from bal
  if fromBal < n
    then do put bal
    else do
    modify $ Map.insert from (fromBal - n)
    modify $ Map.insertWith (+) to n


main = do
  print "Trying to transfer more than what one has simply returns the original array:"
  print $ execState (transfer "0x1" "0x2" 110) balances
  print ""
  print "Otherwise transaction proceeds"
  print $ execState (transfer "0x1" "0x2" 10) balances 
