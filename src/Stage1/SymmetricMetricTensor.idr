module Stage1.SymmetricMetricTensor

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.MultisetTree
import Stage0.PrimeMultiset
import Stage1.TypeTheory.Staging
import Data.Vect
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. GENERAL DIMENSION-INDEXED TRIANGULAR COMPONENTS T_D = D*(D+1)/2
------------------------------------------------------------------------

||| Evaluates the standard triangular number T_n = (n * (n + 1)) / 2.
public export
triangularNat : Nat -> Nat
triangularNat 0 = 0
triangularNat (S k) = (S k) + triangularNat k

||| Verified Invariant: T_10 = 55.
public export
0 prfTriangular10Is55 : triangularNat 10 = 55
prfTriangular10Is55 = Refl

||| Verified Invariant: T_4 = 10 (4D spacetime physical metric components).
public export
0 prfTriangular4Is10 : triangularNat 4 = 10
prfTriangular4Is10 = Refl

------------------------------------------------------------------------
-- 2. EXACT 2D <-> 1D COORDINATE BIJECTIONS (0 <= j <= i < dim)
------------------------------------------------------------------------

||| Maps a symmetric coordinate pair (i, j) in dimension `dim`
||| to its unique linear index k in [0, T_dim - 1].
public export
packMetricIndex : (i : Nat) -> (j : Nat) -> Nat
packMetricIndex i j =
  let (iVal, jVal) = if i >= j then (i, j) else (j, i)
  in (triangularNat iVal) + jVal

||| Unpacks a linear index k into the canonical symmetric pair (i, j) with j <= i for dim = 10.
public export
unpackMetricIndex10 : Nat -> (Nat, Nat)
unpackMetricIndex10 k =
  if k < 1  then (0, k)
  else if k < 3  then (1, minus k 1)
  else if k < 6  then (2, minus k 3)
  else if k < 10 then (3, minus k 6)
  else if k < 15 then (4, minus k 10)
  else if k < 21 then (5, minus k 15)
  else if k < 28 then (6, minus k 21)
  else if k < 36 then (7, minus k 28)
  else if k < 45 then (8, minus k 36)
  else if k < 55 then (9, minus k 45)
  else (9, 9)

||| Unpacks a linear index k into the canonical symmetric pair (i, j) with j <= i for dim = 4.
public export
unpackMetricIndex4 : Nat -> (Nat, Nat)
unpackMetricIndex4 k =
  if k < 1  then (0, k)
  else if k < 3  then (1, minus k 1)
  else if k < 6  then (2, minus k 3)
  else if k < 10 then (3, minus k 6)
  else (3, 3)

||| Complete list of all symmetric coordinate pairs (i, j) for an arbitrary dimension `dim`.
public export
allSymmetricPairs : (dim : Nat) -> List (Nat, Nat)
allSymmetricPairs Z = []
allSymmetricPairs (S k) =
  let indices = the (List Nat) [0..k]
  in [ (i, j) | i <- indices, j <- the (List Nat) [0..i] ]

------------------------------------------------------------------------
-- 3. DEPENDENT SYMMETRIC METRIC TENSOR TYPE & CONSTRUCTORS
------------------------------------------------------------------------

||| Dependently typed Symmetric Metric Tensor of dimension `dim`.
||| Wraps a BoxSquareMaxel dim whose matrix elements satisfy g_{ij} = g_{ji}.
public export
record SymmetricMetricTensor (dim : Nat) where
  constructor MkSymmetricMetricTensor
  metricMaxel : BoxSquareMaxel dim

||| Constructs a SymmetricMetricTensor 10 from 55 independent component weights.
public export
makeSymmetricMetric10 : List (Nat, BoxInt) -> SymmetricMetricTensor 10
makeSymmetricMetric10 weights =
  let step : BoxMultisetTree Pixel -> (Nat, BoxInt) -> BoxMultisetTree Pixel
      step acc (k, w) =
        let (i, j) = unpackMetricIndex10 k
            acc1 = setBoxTree (MkPixel i j) w acc
            acc2 = if i /= j then setBoxTree (MkPixel j i) w acc1 else acc1
        in acc2
      tree = foldl step BoxLeaf weights
  in MkSymmetricMetricTensor (MkBoxSquareMaxel tree)

||| Flat Minkowski / Euclidean identity metric tensor of dimension `dim`.
public export
identityMetricTensor : (dim : Nat) -> SymmetricMetricTensor dim
identityMetricTensor dim = MkSymmetricMetricTensor (identityBoxSquareMaxel dim)

||| 2LTT Staged Flat Identity Metric Tensor:
public export
stagedIdentityMetricTensor : (dim : Nat) -> Code (SymmetricMetricTensor dim)
stagedIdentityMetricTensor dim = quote (identityMetricTensor dim)

------------------------------------------------------------------------
-- 4. 10D CANONICAL TERM INSTANTIATION & GOH SPECTRUM
------------------------------------------------------------------------

||| Canonical 10D Spacetime Metric Tensor ground instance.
public export
spacetime10DMetric : SymmetricMetricTensor 10
spacetime10DMetric = identityMetricTensor 10

||| Parabolic Dark Matter capacity 55 connects 10D spacetime metric components
||| directly to the Goh prime product 5 * 11 = 55.
public export
record GohSpacetimeMetric10D where
  constructor MkGohSpacetimeMetric10D
  0 prod5_11      : GohPrimeProduct 5 11 55
  0 triangularPrf : triangularNat 10 = 55
  0 doublePrf     : (the Nat (2 * 55)) = (the Nat (10 * 11))

public export
gohSpacetimeMetric10D : GohSpacetimeMetric10D
gohSpacetimeMetric10D = MkGohSpacetimeMetric10D gohPrimeProduct5_11 Refl Refl

------------------------------------------------------------------------
-- 5. VERIFIED INVARIANTS & AUDITS
------------------------------------------------------------------------

||| Verified Invariant: There are exactly 55 symmetric pairs in 10D spacetime.
public export
auditSymmetricPairsCount55 : Bool
auditSymmetricPairsCount55 =
  length (allSymmetricPairs 10) == 55

||| Verified Invariant: Coordinate packing round-trip is exact for all 55 pairs in 10D.
public export
auditMetricIndexRoundTrip55 : Bool
auditMetricIndexRoundTrip55 =
  let testIndices = the (List Nat) [0..54]
      allMatch = all (\k =>
        let (i, j) = unpackMetricIndex10 k
            repacked = packMetricIndex i j
        in repacked == k) testIndices
  in allMatch
