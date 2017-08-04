module JacksToken

import Data.Map.Base as Map
import KVStore

Address : Type
Address = String


Functor (Map a) where
  map f (Bin k x y z w) = (Bin k x (f y) (map f z) (map f w))
  map f Tip = Tip

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

interface (Foldable (f Address), KVStore f Address Nat) => ConstToken (f : Type -> Type -> Type) Address Nat where
  -- Get the balance of an address.
  balance : Address -> f Address Nat -> Nat
  balance user = fromMaybe 0 . get user

  totalSupply : Foldable (f Address) => f Address Nat -> Nat
  totalSupply = ?what

  -- Move `amount` tokens from `from` to `to`.
  transfer     : Address -> Address -> Nat -> f Address Nat -> f Address Nat


  -- Total supply should be constant.
  constSupply : Foldable (f Address) => (tokens : f Address Nat) -> totalSupply tokens = totalSupply (transfer from to amount tokens)

  -- Balances should be updated after transfer.
  --transferTo   : (plus (balance to tokens) amount) = (balance to (transfer from to amount tokens))
  --transferFrom : balance from tokens = plus (balance from (transfer from to amount tokens)) amount




--ConstToken Map Address Nat where
--  transfer from to amount balances = 