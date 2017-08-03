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

interface (KVStore f a b, Num b, Foldable (f a)) => ConstToken (f : Type -> Type -> Type) a b where
  -- Get the balance of an address.
  balance : a -> f a b -> b
  balance a = fromMaybe 0 . get a

  totalSupply : f a b -> b
  totalSupply = sum

  -- Move `amount` tokens from `from` to `to`.
  transfer     : a -> a -> b -> f a b -> f a b


  -- Total supply should be constant.
  constSupply  : totalSupply tokens = totalSupply (transfer from to amount tokens)

  -- Balances should be updated after transfer.
  transferTo   : balance to tokens + amount = balance to (transfer from to amount tokens)
  transferFrom : balance from tokens = balance from (transfer from to amount tokens) + amount




--ConstToken Map Address Nat where
--  transfer from to amount balances = 