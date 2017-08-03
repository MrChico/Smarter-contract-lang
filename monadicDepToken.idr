import Control.ST
import Data.Map.Base as Map
--import KVStore as FiniteMap

interface (Ord k, Functor m) => FiniteMap (m : Type -> Type) k where
    get : k -> m a -> Maybe a
    singleton : k -> a ->  (m a)
    insert : k -> a -> (m a) -> (m a)
    insertWith : (a -> a -> a) -> k -> a -> m a -> m a
    
implementation Functor (Map a) where
  map f (Bin k x y z w) = (Bin k x (f y) (map f z) (map f w))
  map f Tip = Tip

implementation (Ord a) => FiniteMap (Map a) a where 
  get = Map.lookup
  singleton = Map.singleton
  insert = Map.insert
  insertWith = Map.insertWith
--Monadic token utilizing dependent types
--A token should be a monad on the kv-store interface.
--One would first want to translate the Edison API haskell library to idris



--As before
zeroAsDefault : Maybe Nat -> Nat
zeroAsDefault = fromMaybe 0

{-With dependent types, our goal is to prove that applications of transfer renders the total supply unchanged.

Idris allows for stateful reasoning via the type STrans (or its syntactically cleaner variant ST). See State Machines all the way down by Edwin Brady for details

Approach 1: 
- Balances as Map String Nat
- Transfer as a monadic function depending on whether there is sufficient balance or not
-}

--n-foldApp :


interface Token (m : Type -> Type) where
  initialize : String -> Nat -> ST m Var [Add (\bal => [bal ::: State (Map String Nat)])]
  --sufficientFunds : (bal : Var) -> (n : Nat) -> (from : String) -> (to : String) -> ST m Bool [bal ::: State (Map String Nat)]
  transfer : (bal : Var) -> (from : String) -> (to : String) ->  ST m (Map String Nat) [bal ::: State (Map String Nat)]

implementation Token m where
  initialize owner amount = do bal <- new (singleton owner amount)
                               pure bal
  transfer bal from to = do state <- read bal
                            let fromBal = zeroAsDefault $ lookup from state
                            case fromBal of
                                 Z => pure state
                                 S n => do
                                        update bal $ Map.insert from n
                                        update bal $ Map.insertWith (+) to 1
                                        read bal


{-
Approach 2: The invariance must be captured on the type level. Anything that satisfies the Token interface must have the sum of balances be invariant..
Maybe model individual balances as labels [(martinBalance ::: Fin n :: jackBalance ::: Fin m)] and so on. Transfer function would then transform the resources by something along the lines of:
[(martinBalance ::: Fin (S n) :: jackBalance ::: Fin m) => (martinBalance ::: Fin n :: jackBalance ::: Fin (S m))] 

-}

{-
Approach 3: The token interface is stateless and requires proofs of invariants, but is used to implement a stateful library.
-}


-- Just to make things clearer.
Address : Type
Address = String

-- We "need" this to be able to sum all balances. (Weird that it isn't in the Map library.)



Foldable (Map a) where
  foldr _ acc Tip = acc
  foldr f acc (Bin _ _ v leftTree rightTree) =
    let rightRes = foldr f acc rightTree
        midRes   = f v rightRes
     in foldr f midRes leftTree

  foldl _ acc Tip = acc
  foldl f acc (Bin _ _ v leftTree rightTree) =
    let leftRes = foldl f acc leftTree
        midRes  = f leftRes v
     in foldl f midRes rightTree

totalSupply : (FiniteMap m k) => () -> a -> Nat
--totalSupply f struc = ?wha
{-
interface constToken (t : Address -> Nat -> Type) where
  -- Get the balance of an address.
  balance      : Address -> t Address Nat -> Nat

  -- Move `amount` tokens from `from` to `to`.
  transfer     : Address -> Address -> Nat -> t a b -> t a b

  -- Total supply should be constant.
  constSupply  : totalSupply tokens = totalSupply (transfer from to amount tokens)

  -- Balances should be updated after transfer.
  transferTo   : balance to tokens + amount = balance to (transfer from to amount tokens)
  transferFrom : balance from tokens = balance from (transfer from to amount tokens) + amount
-}
{-
implementation Token Map Address Nat where
  balance a b = fromMaybe 0 $ lookup a b
  totalSupply = sum
  transfer = ?waht
  constSupply = ?whta
  transferTo = ?hwat
  transferFrom = ?hawt

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
