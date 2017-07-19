import Control.ST
import Data.Map.Base as Map

--Monadic token utilizing dependent types

{-With dependent types, we can guard our transfer functionality by requiring a proof that the senders balance is sufficient, as well as prove that applications of transfer renders the total supply unchanged.

The strategy is the following: 
Implement `balance` as a String->Nat mapping
Prove that the sum of all entries in balance is unchanged -}

--As before
zeroAsDefault : Maybe Nat -> Nat
zeroAsDefault (Just n) = n
zeroAsDefault Nothing = 0

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



sumEntries : Map String Nat -> Nat

moveQuantity : String -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> Nat.GTE (zeroAsDefault (Map.lookup from x)) n -> Map String Nat
moveQuantity to from n bal pf = ?as

moveQualityConstantSupply : (to : String) -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> (pf : Nat.GTE (zeroAsDefault (Map.lookup from x)) n) -> sumEntries(x) = sumEntries(moveQuantity to from n x pf)


--One could probably design interfaces which specify the sender of transactions and other blockchain-specific parameters
--But how does one reason about the state? 



intialize : (from : String) -> (n : Nat) -> ST m Var [add (State (Map String Nat))]

--Want to get rid of bal in the following:
transfer : (from : String) -> (to : String) -> (n : Nat) -> (bal : Map String Nat) -> (x : Var) -> (y : Var) ->
           ST m () [x ::: State (Map String Nat),
           y ::: State (LTE n (zeroAsDefault (lookup from bal)))
           ]
           


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
