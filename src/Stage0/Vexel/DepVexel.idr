module Stage0.Vexel.DepVexel

import Data.List
import Stage0.Singleton.DepSing
import Stage0.Singleton.Sing
import Stage0.Singleton.Bit
import Stage0.Vexel.Vexel
import Stage0.Multiset

%default total

||| A dependently typed Vexel.
public export
data DepVexel : (a : Type) -> List a -> Type where
  DepEmptyV : DepVexel a []

  ||| Adds a dependent singleton to the Vexel.
  DepAddV : {x : a} ->
            DepSing a x ->
            {rest : List a} ->
            DepVexel a rest ->
            DepVexel a (x :: rest)

public export
freezeDepVexel : {0 contents : List a} -> DepVexel a contents -> List a
freezeDepVexel DepEmptyV = []
freezeDepVexel (DepAddV (MkDepSing x) prev) = x :: freezeDepVexel prev

||| Maps a runtime Vexel (multiset of singletons) to a type-level list of active coordinates.
public export
vexelToMSet : Vexel Bit a -> List a
vexelToMSet ZeroM = []
vexelToMSet (AddM (MkSing x) w xs) =
  if isOne w
     then x :: vexelToMSet xs
     else vexelToMSet xs
