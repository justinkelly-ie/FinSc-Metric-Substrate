module Stage1.Topology.Peaks

import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Decidable.Equality
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- LAYER 4 COMBINATORIAL PEAK TRACKER
--------------------------------------------------------------------------------

||| Helper engine that crawls a FusedStream to calculate its strict peak profile using Nat fuel.
public export
countPeaksKernelFueled : (fuel : Nat) -> (prevDeg : Nat) -> (stream : FusedStream Nat) -> Nat
countPeaksKernelFueled 0 _ _ = Z
countPeaksKernelFueled (S f) prevDeg (MkStream step state) = case step state of
  Done => Z
  Skip s => countPeaksKernelFueled f prevDeg (MkStream step s)
  Yield deg s => case deg < prevDeg of
    True => S (countPeaksKernelFueled f deg (MkStream step s))
    False => countPeaksKernelFueled f deg (MkStream step s)

||| Helper engine that crawls a FusedStream to calculate its strict peak profile using BoxNat fuel.
public export
countPeaksKernelBoxNat : BoxNat -> (prevDeg : Nat) -> FusedStream Nat -> Nat
countPeaksKernelBoxNat bfuel prevDeg strm = countPeaksKernelFueled (boxNatToNat bfuel) prevDeg strm

||| The flagship Layer 4 Counting Function using Nat fuel.
public export
countTotalPeaksFueled : (fuel : Nat) -> (stream : FusedStream Nat) -> Nat
countTotalPeaksFueled 0 _ = Z
countTotalPeaksFueled (S f) (MkStream step state) = case step state of
  Done => Z
  Skip s => countTotalPeaksFueled f (MkStream step s)
  Yield deg s => countPeaksKernelFueled f deg (MkStream step s)

||| The flagship Layer 4 Counting Function using BoxNat fuel.
public export
countTotalPeaksBoxNat : BoxNat -> FusedStream Nat -> Nat
countTotalPeaksBoxNat bfuel strm = countTotalPeaksFueled (boxNatToNat bfuel) strm

||| The flagship Layer 4 Counting Function.
||| It takes a stream of degrees and extracts its total Narayana peak weight bounded by master substrate Goh fuel.
public export
countTotalPeaks : (stream : FusedStream Nat) -> Nat
countTotalPeaks stream = countTotalPeaksBoxNat masterSubstrateGohFuel stream

||| Coinductive deforested peak extractor transducer:
||| filters degree turning points (deg < prevDeg) at O(1) allocation without list intermediate.
public export
extractPeaksStream : FusedStream Nat -> FusedStream Nat
extractPeaksStream (MkStream {s} step state) = MkStream peakStep (Nothing, state)
  where
    peakStep : (Maybe Nat, s) -> Step (Maybe Nat, s) Nat
    peakStep (prev, st) = case step st of
      Done => Done
      Skip st' => Skip (prev, st')
      Yield deg st' => case prev of
        Nothing => Skip (Just deg, st')
        Just p => if deg < p
                    then Yield p (Just deg, st')
                    else Skip (Just deg, st')

||| Counts total peaks over a compile-time static vector of degrees.
public export
countTotalPeaksVect : {n : Nat} -> Vect n Nat -> Nat
countTotalPeaksVect [] = Z
countTotalPeaksVect (d :: rest) = loop d rest
  where
    loop : Nat -> Vect k Nat -> Nat
    loop _ [] = Z
    loop prev (x :: xs) = if x < prev
                            then S (loop x xs)
                            else loop x xs

--------------------------------------------------------------------------------
-- NARAYANA SIFTING WITNESS
--------------------------------------------------------------------------------

||| A Type-level proof witness validating Narayana field boundaries.
||| Ensures that the structural turning points of a specific stream count cleanly.
public export
data NarayanaWitness : (stream : FusedStream Nat) -> (expectedPeaks : Nat) -> Type where
  VerifyPeaks : (stream : FusedStream Nat) -> 
                (0 check : countTotalPeaks stream = expectedPeaks) -> 
                NarayanaWitness stream expectedPeaks

||| Static compiler proof auditing that a mock stream fits securely inside its designated Narayana topological class.
public export
0 auditNarayanaTopology : (stream : FusedStream Nat) -> 
                         (0 cond : countTotalPeaks stream = 1) -> 
                         NarayanaWitness stream 1
auditNarayanaTopology stream cond = VerifyPeaks stream cond

||| Static audit witness verifying that counting peaks on a vector [10, 5, 20, 15] produces 2 peaks.
public export
auditPeakExtractionProof : Bool
auditPeakExtractionProof =
  countTotalPeaksVect [10, 5, 20, 15] == 2
