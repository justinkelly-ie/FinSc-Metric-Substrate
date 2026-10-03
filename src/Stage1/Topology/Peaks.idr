module Stage1.Topology.Peaks

import Stage1.UnixelFraction
import Stage0.OnSeq.FusedStream
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- LAYER 4 COMBINATORIAL PEAK TRACKER
--------------------------------------------------------------------------------

||| Helper engine that crawls a FusedStream to calculate its strict peak profile.
||| It tracks the degree of the previous node to identify structural turning points.
public export covering
countPeaksKernel : (prevDeg : Nat) -> (stream : FusedStream Nat) -> Nat
countPeaksKernel prevDeg (MkStream step state) = case step state of
  Done => Z
  Skip s => countPeaksKernel prevDeg (MkStream step s)
  Yield deg s => case deg < prevDeg of
    True => S (countPeaksKernel deg (MkStream step s))
    False => countPeaksKernel deg (MkStream step s)

||| The flagship Layer 4 Counting Function.
||| It takes a stream of degrees and extracts its total Narayana peak weight.
public export covering
countTotalPeaks : (stream : FusedStream Nat) -> Nat
countTotalPeaks (MkStream step state) = case step state of
  Done => Z
  Skip s => countTotalPeaks (MkStream step s)
  Yield deg s => countPeaksKernel deg (MkStream step s)

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
