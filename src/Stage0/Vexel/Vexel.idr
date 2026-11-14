module Stage0.Vexel.Vexel

import Stage0.Multiset
import public Stage0.Token
import Stage0.Bit
import public Stage0.BoxInt
import Data.List

%default total

||| A Vexel is a one-dimensional state vector represented as a multiset of Tokens.
||| This is Wildberger's discrete, algebraic replacement for a standard vector.
public export
Vexel : (c : Type) -> (a : Type) -> Type
Vexel c a = Multiset c (Token a)

||| Canonical unambiguous alias for polymorphic multiset state vectors.
public export
GenericVexel : (c : Type) -> (a : Type) -> Type
GenericVexel = Vexel

||| Checks if an atomic token is full (non-zero).
||| Since Token always holds a value, any Token a is always full.
public export
isFull : Token a -> Bool
isFull _ = True

||| Check if an item exists in a list (wrapper for elem).
public export
contains : Eq a => a -> List a -> Bool
contains = elem

||| Removes the first occurrence of an item from a list.
public export
removeFirst : Eq a => a -> List a -> List a
removeFirst _ [] = []
removeFirst x (y :: ys) = if x == y then ys else y :: removeFirst x ys

||| Evaluates addition (`+`) across a Vexel container.
||| Governed entirely by the localized structural fold-in rule:
||| Adding two filled tokens inside the same cell forces a collapse.
public export
addVexels : (Eq a, Num c, Eq c) => Vexel c a -> Vexel c a -> Vexel c a
addVexels x y = annihilateMultiset (addMultiset x y)

||| Helper to lookup coordinate weights in a Vexel.
public export
lookupWeight : (Eq a, Num c, Eq c) => a -> Vexel c a -> c
lookupWeight _ ZeroM = 0
lookupWeight x (AddM (MkToken y) w rest) =
  if x == y then w + lookupWeight x rest else lookupWeight x rest

------------------------------------------------------------------------
-- DEPENDENTLY TYPED VEXEL (DepVexel)
------------------------------------------------------------------------

||| A dependently typed Vexel tracking active coordinates in its type index.
public export
data DepVexel : (a : Type) -> List a -> Type where
  DepEmptyV : DepVexel a []
  DepAddV   : {x : a} -> DepToken a x -> {rest : List a} -> DepVexel a rest -> DepVexel a (x :: rest)

public export
freezeDepVexel : {0 contents : List a} -> DepVexel a contents -> List a
freezeDepVexel DepEmptyV = []
freezeDepVexel (DepAddV (MkDepToken x) prev) = x :: freezeDepVexel prev

||| Maps a runtime Vexel (multiset of tokens) to a type-level list of active coordinates.
public export
vexelToMSet : Vexel Bit a -> List a
vexelToMSet ZeroM = []
vexelToMSet (AddM (MkToken x) w xs) =
  if isOne w
     then x :: vexelToMSet xs
     else vexelToMSet xs
