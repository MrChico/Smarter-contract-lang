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
lem : (m : Nat) -> (n : Nat) -> (k : Nat) -> (smaller : Nat.LTE k m) -> (plus m  n = plus ((-) {smaller} m k)  (plus n  k))
lem Z Z Z _ = Refl
lem (S m) Z Z _ = Refl
lem Z _ (S _) _ impossible
lem (S j) Z (S k) (LTESucc s) = trans (cong (lem j 0 k s)) (plusSuccRightSucc (minus j k) k)
lem Z (S j) Z _ = cong (sym (plusZeroRightNeutral j))
lem (S i) (S j) Z _ = eqSucc (plus i (S j)) (plus i (S (plus j 0))) (plusConstantLeft (S j) (S (plus j 0)) i (cong (sym (plusZeroRightNeutral j))))
lem (S i) (S j) (S k) (LTESucc s) = trans (eqSucc (plus i (S j)) (plus (minus i k) (plus j (S k))) (trans (lem i (S j) k s) (plusConstantLeft (S (plus j k)) (plus j (S k)) (minus i k) (plusSuccRightSucc j k)))) (plusSuccRightSucc (minus i k) (plus j (S k)))



sumEntries : Map String Nat -> Nat

moveQuantity : String -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> Nat.GTE (zeroAsDefault (Map.lookup from x)) n -> Map String Nat
moveQuantity to from n bal pf = ?as

moveQualityConstantSupply : (to : String) -> (from : String) -> (n : Nat) -> (x : Map String Nat) -> (pf : Nat.GTE (zeroAsDefault (Map.lookup from x)) n) -> sumEntries(x) = sumEntries(moveQuantity to from n x pf)


transfer : (from : String) -> (to : String) -> (n : Nat) -> (x : Map String Nat) -> Nat.GTE (zeroAsDefault (Map.lookup from x)) n -> STrans m () [y ::: State (Map String Nat)]
                                     (const [y ::: State (Map String Nat)])
--transfer amount from to x = do bal <- read x
--                               write x bal
                            

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
