module Stage0.Singleton.SingFraction

import Stage0.Multiset
import Stage0.Singleton.Sing
import public Stage0.BoxInt
import public Stage0.Singleton.Bit
import Stage0.Vexel.Vexel
import Stage0.Vexel.Byte

%default total

public export
0 TrivialBase : Type
TrivialBase = Nat

public export
BaseAnchor : TrivialBase
BaseAnchor = 0

||| A type alias for a Singleton Bit-Gate Multiset.
||| Defined directly as a Vexel state.
public export
SingBitGateMset : (state : Type) -> Type
SingBitGateMset state = Vexel Bit state

||| The empty (zero) singleton bit-gate state.
public export
emptySingBitGate : SingBitGateMset state
emptySingBitGate = ZeroM

||| Insert a state with a given Bit weight into the singleton bit-gate multiset.
public export
insertSingBit : Eq state => state -> Bit -> SingBitGateMset state -> SingBitGateMset state
insertSingBit s w m =
  if w == Zero then m else addVexels (AddM (MkSing s) One ZeroM) m

||| Evaluate the binary flag for a state in the singleton bit-gate multiset.
public export
evaluateSingState : Eq state => SingBitGateMset state -> state -> Bit
evaluateSingState m s = lookupWeight s m

||| A singleton Boole Fraction type.
||| Establishes type-level division-by-zero protection using strictly positive Sing.
public export
record SingBooleFraction (state : Type) where
  constructor OverSingCircuit
  numeratorBitMset : SingBitGateMset state
  denominatorUnit  : Sing TrivialBase

||| Canonical unit denominator singleton multiset.
public export
theSingUnitConstant : Sing TrivialBase
theSingUnitConstant = MkSing BaseAnchor

||| Smart constructor: builds a SingBooleFraction with the strictly positive unit denominator.
public export
mkSingBooleFraction : SingBitGateMset state -> SingBooleFraction state
mkSingBooleFraction bits = OverSingCircuit bits theSingUnitConstant

||| Evaluate a state from the singleton fraction.
public export
evalSingFraction : Eq state => SingBooleFraction state -> state -> Bit
evalSingFraction (OverSingCircuit num _) s = evaluateSingState num s

||| Lift the singleton multiset to BoxInt weights.
public export
liftSingBitGateToBoxInt : SingBitGateMset state -> Vexel BoxInt state
liftSingBitGateToBoxInt ZeroM = ZeroM
liftSingBitGateToBoxInt (AddM k w rest) =
  AddM k (bitToBoxInt w) (liftSingBitGateToBoxInt rest)

||| Lift the singleton fraction to BoxInt, transitioning to Row 2.
public export
liftSingToRow2 : SingBooleFraction state -> Vexel BoxInt state
liftSingToRow2 (OverSingCircuit num _) = liftSingBitGateToBoxInt num
