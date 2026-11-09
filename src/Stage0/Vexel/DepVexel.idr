module Stage0.Vexel.DepVexel

import Data.List
import public Stage0.Token
import Stage0.Singleton.DepSing
import Stage0.Singleton.Sing
import Stage0.Bit
import Stage0.Vexel.Vexel
import Stage0.Multiset

%default total

||| A dependently typed Vexel.
public export
data DepVexel : (a : Type) -> List a -> Type where
  DepEmptyV : DepVexel a []

  ||| Adds a dependent token to the Vexel.
  DepAddV : {x : a} ->
            DepToken a x ->
            {rest : List a} ->
            DepVexel a rest ->
            DepVexel a (x :: rest)

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
