module ConcreteToken

import Data.Map.Base as Map

Address : Type
Address = String

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

Balances : Type
Balances = Map Address Nat

balance : Address -> Balances -> Nat
balance a = fromMaybe 0 . lookup a

transfer : (f : Address) -> Address -> (n : Nat) -> (bs : Balances) -> {auto p: LTE n (balance f bs)} -> Balances
transfer from to amount balances = let credited = insertWith plus to amount balances
									   fromBal  = balance from balances
									in insert from (fromBal-amount) credited

init : Address -> Nat -> Balances
init = singleton

totalSupply : Balances -> Nat
totalSupply = sum


{-
constSupply : totalSupply tokens = totalSupply (transfer from to amount tokens)
constSupply = ?what


transferTo   : (plus (balance to tokens) amount) = (balance to (transfer from to amount tokens))
transferTo = ?waht

transferFrom : balance from tokens = plus (balance from (transfer from to amount tokens)) amount
transferFrom = ?hawt-}