module Stage0.Vexel.Vexel

import Stage0.Multiset
import Stage0.Singleton.Sing
import Stage0.Singleton.Bit
import public Stage0.BoxInt
import Data.List

%default total

||| A Vexel is a one-dimensional state vector represented as a multiset of Singletons.
||| This is Wildberger's discrete, algebraic replacement for a standard vector.
public export
Vexel : (c : Type) -> (a : Type) -> Type
Vexel c a = Multiset c (Sing a)

||| Canonical unambiguous alias for polymorphic multiset state vectors.
public export
GenericVexel : (c : Type) -> (a : Type) -> Type
GenericVexel = Vexel

||| Checks if a singleton is full (non-zero).
||| Since Sing always holds a value, any Sing a is always full.
public export
isFull : Sing a -> Bool
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
||| Adding two filled singleton tokens inside the same cell forces a collapse.
public export
addVexels : (Eq a, Num c, Eq c) => Vexel c a -> Vexel c a -> Vexel c a
addVexels x y = annihilateMultiset (addMultiset x y)

||| Helper to lookup coordinate weights in a Vexel.
public export
lookupWeight : (Eq a, Num c, Eq c) => a -> Vexel c a -> c
lookupWeight _ ZeroM = 0
lookupWeight x (AddM (MkSing y) w rest) =
  if x == y then w + lookupWeight x rest else lookupWeight x rest
