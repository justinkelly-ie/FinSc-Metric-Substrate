module Stage0.Vexel.Byte

import Data.List
import public Stage0.Singleton.Sing
import public Stage0.BoxInt
import Stage0.Multiset
import public Stage0.Singleton.Bit

%default total

-----------------------------------------------------------------------
-- BOOLE ALGEBRA OVER VEXELS (MULTISETS)
--
-- A Vexel representing logical state inputs/outputs.
-- Defined as a list of singleton bit-gates over Bit.
-----------------------------------------------------------------------

||| A Byte is a one-dimensional logic vector represented as a Vexel state.
public export
Byte : (state : Type) -> Type
Byte state = Multiset Bit (Sing state)

-----------------------------------------------------------------------
-- VECTOR ARITHMETIC
-----------------------------------------------------------------------

||| Pointwise addition (XOR) of two Boole vectors.
public export
addByte : Eq state => Byte state -> Byte state -> Byte state
addByte x y = annihilateMultiset (addMultiset x y)

||| Helper to lookup the weight of a state coordinate in a Byte.
public export
lookupWeight : Eq state => state -> Byte state -> Bit
lookupWeight _ ZeroM = Zero
lookupWeight x (AddM (MkSing y) w rest) =
  if x == y then w + lookupWeight x rest else lookupWeight x rest

||| Pointwise multiplication (AND) of two Boole vectors.
public export
mulByte : (Eq state) => Byte state -> Byte state -> Byte state
mulByte ZeroM _ = ZeroM
mulByte (AddM (MkSing x) w1 xs) ys =
  let w2   = lookupWeight x ys
      prod = w1 * w2
  in if isZero prod
       then mulByte xs ys
       else AddM (MkSing x) prod (mulByte xs ys)

||| Scalar multiplication: multiply every component by a Bit.
public export
scaleByte : Bit -> Byte state -> Byte state
scaleByte s bytes = if isOne s then bytes else ZeroM

||| The zero vector.
public export
zeroByte : Byte state
zeroByte = ZeroM

||| The one vector (all components One) relative to a finite domain of states.
public export
oneByte : List state -> Byte state
oneByte [] = ZeroM
oneByte (x :: xs) = AddM (MkSing x) One (oneByte xs)

-----------------------------------------------------------------------
-- PREDICATES
-----------------------------------------------------------------------

||| Test whether a Boole vector is the zero vector.
public export
isZeroByte : Byte state -> Bool
isZeroByte ZeroM = True
isZeroByte _     = False

||| Test whether a Boole vector is nonzero.
public export
isNonZeroByte : Byte state -> Bool
isNonZeroByte v = not (isZeroByte v)

-----------------------------------------------------------------------
-- ARISTOTLE'S FOUR SYLLOGISTIC FORMS
-----------------------------------------------------------------------

||| Every Q is a P: Every active coordinate in Q is active in P.
public export
everyQisP : Eq state => Byte state -> Byte state -> Bool
everyQisP ZeroM _ = True
everyQisP (AddM (MkSing x) w xs) ys =
  (isZero w || isOne (lookupWeight x ys)) && everyQisP xs ys

||| No Q is a P: Q · P = 0.
public export
noQisP : Eq state => Byte state -> Byte state -> Bool
noQisP q p = isZeroByte (mulByte q p)

||| Some Q is a P: Q · P ≠ 0.
public export
someQisP : Eq state => Byte state -> Byte state -> Bool
someQisP q p = isNonZeroByte (mulByte q p)

||| Some Q is not a P: Some active coordinate in Q is not active in P.
public export
someQnotP : Eq state => Byte state -> Byte state -> Bool
someQnotP ZeroM _ = False
someQnotP (AddM (MkSing x) w xs) ys =
  (isOne w && not (isOne (lookupWeight x ys))) || someQnotP xs ys
