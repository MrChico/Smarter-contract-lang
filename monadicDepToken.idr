import Control.ST
import Data.Map.Base as Map

--Monadic token utilizing dependent types

--As before
zeroAsDefault : Maybe Nat -> Nat
zeroAsDefault (Just n) = n
zeroAsDefault Nothing = 0

{-With dependent types, we can guard our transfer functionality by requiring a proof that the senders balance is sufficient. Our goal is to prove that applications of transfer renders the total supply unchanged.

Idris allows for stateful reasoning via the type STrans (or its syntactically cleaner variant ST). See State Machines all the way down by Edwin Brady for details

Approach 1: 
- Balances as Map String Nat
- Transfer as a monadic function depending on whether there is sufficient balance or not
-}


interface Token (m : Type -> Type) where
  initialize : String -> Nat -> ST m Var [Add (\bal => [bal ::: State (Map String Nat)])]
  --sufficientFunds : (bal : Var) -> (n : Nat) -> (from : String) -> (to : String) -> ST m Bool [bal ::: State (Map String Nat)]
  transfer : (bal : Var) -> (from : String) -> (to : String) -> (n : Nat) -> ST m Bool [bal ::: State (Map String Nat)]

implementation Token m where
  initialize owner amount = do bal <- new (singleton owner amount)
                               pure bal
                               
  transfer bal from to amount = do bal <- read bal
                                   if (lte amount (zeroAsDefault $ lookup from bal))
                                     then returning True 
                                       modify $ insert from ((lookup from bal) - amount)
                                       modify $ insertWith (+) to amount
                                     else pure False
                                   
{-
Approach 2:
- Model balances as Map String Nat, the fundamental resource on which our monad will be operating.
- Create an interface, Token, listing the possible actions on the balances resource.
- Create a function guardedTransfer, requiring not only balances as a resource, but also a proof that sufficient balance exists
- Functionality for creating 
-}


--Lemma that for all natural numbers m, n and k with k <= m,
--m + n = m - k + n + k
total lem : (m : Nat) -> (n : Nat) -> (k : Nat) -> (smaller : Nat.LTE k m) -> (plus m  n = plus ((-) {smaller} m k)  (plus n  k))
lem Z Z Z _ = Refl
lem (S m) Z Z _ = Refl
lem Z _ (S _) _ impossible
lem (S j) Z (S k) (LTESucc s) = trans (cong (lem j 0 k s)) (plusSuccRightSucc (minus j k) k)
lem Z (S j) Z _ = cong (sym (plusZeroRightNeutral j))
lem (S i) (S j) Z _ = cong (plusConstantLeft (S j) (S (plus j 0)) i (cong (sym (plusZeroRightNeutral j))))
lem (S i) (S j) (S k) (LTESucc s) = trans (cong (trans (lem i (S j) k s) (plusConstantLeft (S (plus j k)) (plus j (S k)) (minus i k) (plusSuccRightSucc j k)))) (plusSuccRightSucc (minus i k) (plus j (S k)))

balList : List (String, Nat)


sumEntries : Map String Nat -> Nat

moveQuantity : String -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> Nat.GTE (zeroAsDefault (Map.lookup from x)) n -> Map String Nat
moveQuantity to from n bal pf = ?as

moveQualityConstantSupply : (to : String) -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> (pf : Nat.GTE (zeroAsDefault (Map.lookup from x)) n) -> sumEntries(x) = sumEntries(moveQuantity to from n x pf)


--One could probably design interfaces which specify the sender of transactions and other blockchain-specific parameters
--But how does one reason about the state? 


--Interface a la 'State machines all the way down'
{-
interface Token (m : Type -> Type) where

  
  initialize : (intialOwner : String) -> (totalSupply : Nat) -> STrans m Var [] (\bal => [bal ::: Balances (singleton initialOwner totalSupply)])

--I would like to be able to refer to certain properties of the state in the type declaration of functions operating on it. For example, in the following transfer function, it would be nice if one could require that the bal variable satisfied that the from balance is at least as large as the amount one wants to transfer. In other words, I would want to guard the function by requiring a pf term of '(LTE amount (zeroAsDefault (lookup from bal)'. This does not type check however...
    transfer : (from : String) -> (to : String) -> (amount : Nat) -> (bal : Var) -> 
             STrans m () 
  -}
--I am tempted to work with the STrans primitives new, read and delete directly


intialize : (from : String) -> (n : Nat) -> ST m Var [add (State (Map String Nat))]

--Want to get rid of bal in the following:

ttransfer : (from : String) -> (to : String) -> (n : Nat) -> (x : Var) -> 
  ST m Bool [x ::: State (Map String Nat)]



--Not quite right.. We want x to be a resource
tttransfer : (from : String) -> (to : String) -> (n : Nat) -> (x : Map String Nat) -> Nat.GTE (zeroAsDefault (Map.lookup from x)) n -> 
  STrans m () [y ::: State (Map String Nat)]
              (const [y ::: State (Map String Nat)])


incremen : (x : Var) -> (y : Var) -> ST m () [x ::: State Integer, y ::: State Integer]

increment : (x : Var) -> STrans m () [x ::: State Integer]
                                     (const [x ::: State Integer])
increment x = do num <- read x
                 write x (num + 1)

makeAndIncrement : Integer -> STrans m Integer [] (const [])
makeAndIncrement init = do var <- new init
                           increment var
                           x <- read var
                           delete var
                           pure x


-- Local Variables:
-- idris-load-packages: ("contrib")

-- End:
