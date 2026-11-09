module Stage0.Singleton.SingFraction

import Stage0.Multiset
import public Stage0.Token
import Stage0.Singleton.Sing
import public Stage0.BoxInt
import public Stage0.Bit
import Stage0.Vexel.Vexel
import Stage0.Vexel.Byte
import Stage1.Basis.CoordCell
import Stage1.UnixelFraction

%default total

public export
0 TrivialBase : Type
TrivialBase = Nat

public export
BaseAnchor : TrivialBase
BaseAnchor = 0

||| A type alias for a Bit-Gate Multiset over atomic tokens.
||| Defined directly as a Vexel state.
public export
SingBitGateMset : (state : Type) -> Type
SingBitGateMset state = Vexel Bit state

||| Canonical alias for token bit-gate multiset.
public export
TokenBitGateMset : (state : Type) -> Type
TokenBitGateMset = SingBitGateMset

||| The empty (zero) bit-gate state.
public export
emptySingBitGate : SingBitGateMset state
emptySingBitGate = ZeroM

||| Insert a state with a given Bit weight into the bit-gate multiset.
public export
insertSingBit : Eq state => state -> Bit -> SingBitGateMset state -> SingBitGateMset state
insertSingBit s w m =
  if w == Zero then m else addVexels (AddM (MkToken s) One ZeroM) m

||| Evaluate the binary flag for a state in the bit-gate multiset.
public export
evaluateSingState : Eq state => SingBitGateMset state -> state -> Bit
evaluateSingState m s = lookupWeight s m

||| A Boole Fraction type over a Unixel denominator: a FractionalBox holding a Vexel of Bits.
||| Establishes compile-time division-by-zero protection using strictly non-zero Unixel denominators.
public export
BooleFraction : (state : Type) -> Type
BooleFraction state = FractionalBox (Vexel Bit state)

||| Legacy alias for BooleFraction.
public export
SingBooleFraction : (state : Type) -> Type
SingBooleFraction = BooleFraction

||| Canonical unit denominator Unixel.
public export
theSingUnitConstant : Unixel
theSingUnitConstant = mkUnixel 1

||| Smart constructor: builds a BooleFraction with the strictly positive unit denominator.
public export
mkBooleFraction : SingBitGateMset state -> BooleFraction state
mkBooleFraction bits = OverUnixel bits theSingUnitConstant

||| Legacy constructor alias for mkBooleFraction.
public export
mkSingBooleFraction : SingBitGateMset state -> SingBooleFraction state
mkSingBooleFraction = mkBooleFraction

||| Legacy constructor wrapper for OverSingCircuit.
public export
OverSingCircuit : SingBitGateMset state -> Unixel -> SingBooleFraction state
OverSingCircuit = OverUnixel

||| Evaluate a state from the Boole fraction.
public export
evalBooleFraction : Eq state => BooleFraction state -> state -> Bit
evalBooleFraction (OverUnixel num _) s = evaluateSingState num s

||| Legacy alias for evalBooleFraction.
public export
evalSingFraction : Eq state => SingBooleFraction state -> state -> Bit
evalSingFraction = evalBooleFraction

||| Lift the bit-gate multiset to BoxInt weights.
public export
liftSingBitGateToBoxInt : SingBitGateMset state -> Vexel BoxInt state
liftSingBitGateToBoxInt ZeroM = ZeroM
liftSingBitGateToBoxInt (AddM k w rest) =
  AddM k (bitToBoxInt w) (liftSingBitGateToBoxInt rest)

||| Lift the Boole fraction to BoxInt, transitioning to Row 2.
public export
liftBooleToRow2 : BooleFraction state -> Vexel BoxInt state
liftBooleToRow2 (OverUnixel num _) = liftSingBitGateToBoxInt num

||| Legacy alias for liftBooleToRow2.
public export
liftSingToRow2 : SingBooleFraction state -> Vexel BoxInt state
liftSingToRow2 = liftBooleToRow2

-----------------------------------------------------------------------
-- 3. CANONICAL BRIDGE TO UNIXEL FRACTION
-----------------------------------------------------------------------

||| Converts a SingBooleFraction to the canonical FractionalBox over Unixel.
public export
singBooleFractionToFractionalBox : SingBooleFraction state -> FractionalBox (SingBitGateMset state)
singBooleFractionToFractionalBox = id

||| Converts a canonical FractionalBox over Unixel back to a SingBooleFraction.
public export
fractionalBoxToSingBooleFraction : FractionalBox (SingBitGateMset state) -> SingBooleFraction state
fractionalBoxToSingBooleFraction = id
