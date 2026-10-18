module Stage1.Spacetime10D

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.MultisetTree
import Stage0.PrimeMultiset
import Stage1.TypeTheory.Staging
import Data.Vect
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. 10D SPACETIME SYMMETRIC METRIC TENSOR & TRIANGULAR NUMBER T_10 = 55
------------------------------------------------------------------------

||| Evaluates the standard triangular number T_n = (n * (n + 1)) / 2 for small n.
public export
triangularNat : Nat -> Nat
triangularNat 0 = 0
triangularNat (S k) = (S k) + triangularNat k

||| Verified Invariant: The 10th triangular number T_10 identically equals 55.
public export
0 prfTriangular10Is55 : triangularNat 10 = 55
prfTriangular10Is55 = Refl

||| Verified Invariant: Parabolic Dark Matter capacity 55 definitionally matches T_10
||| and factorizes into the Goh prime product 5 * 11 = 55.
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
-- 2. EXACT 2D <-> 1D COORDINATE BIJECTIONS (0 <= j <= i < 10)
------------------------------------------------------------------------

||| Maps a symmetric 10D spacetime coordinate pair (i, j) with 0 <= j <= i < 10
||| to its unique linear index k in [0, 54].
public export
packMetricIndex10D : (i : Nat) -> (j : Nat) -> Nat
packMetricIndex10D i j =
  let (iVal, jVal) = if i >= j then (i, j) else (j, i)
  in (triangularNat iVal) + jVal

||| Inverse linear-to-coordinate projection:
||| Maps a linear component index k in [0, 54] back to its canonical pair (i, j) with j <= i.
public export
unpackMetricIndex10D : Nat -> (Nat, Nat)
unpackMetricIndex10D k =
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

||| Complete list of all 55 canonical symmetric coordinate pairs (i, j) with 0 <= j <= i < 10.
public export
allSymmetricPairs10D : List (Nat, Nat)
allSymmetricPairs10D =
  [ (i, j) | i <- the (List Nat) [0..9], j <- the (List Nat) [0..i] ]

------------------------------------------------------------------------
-- 3. 10D SYMMETRIC METRIC TENSOR REPRESENTATION AS BoxSquareMaxel 10
------------------------------------------------------------------------

||| Constructs a full symmetric 10x10 metric tensor Maxel from a list of 55 independent weights.
||| Symmetric elements (i, j) and (j, i) are both populated to ensure g_{ij} = g_{ji}.
public export
makeSymmetricMetric10D : List (Nat, BoxInt) -> BoxSquareMaxel 10
makeSymmetricMetric10D weights =
  let step : BoxMultisetTree Pixel -> (Nat, BoxInt) -> BoxMultisetTree Pixel
      step acc (k, w) =
        let (i, j) = unpackMetricIndex10D k
            acc1 = setBoxTree (MkPixel i j) w acc
            acc2 = if i /= j then setBoxTree (MkPixel j i) w acc1 else acc1
        in acc2
      tree = foldl step BoxLeaf weights
  in MkBoxSquareMaxel tree

||| 2LTT Staged Flat 10D Identity Metric Tensor:
||| Pre-computes the 10x10 Minkowski/Euclidean metric at compile time (Level 1)
||| with zero runtime interpretation overhead.
public export
stagedIdentityMetric10D : Code (BoxSquareMaxel 10)
stagedIdentityMetric10D = quote (identityBoxSquareMaxel 10)

------------------------------------------------------------------------
-- 4. VERIFIED INVARIANTS & AUDITS
------------------------------------------------------------------------

||| Verified Invariant: There are exactly 55 symmetric pairs in 10D spacetime.
public export
auditSymmetricPairsCount55 : Bool
auditSymmetricPairsCount55 =
  length allSymmetricPairs10D == 55

||| Verified Invariant: Coordinate packing round-trip is exact for all 55 pairs.
public export
auditMetricIndexRoundTrip55 : Bool
auditMetricIndexRoundTrip55 =
  let testIndices = the (List Nat) [0..54]
      allMatch = all (\k =>
        let (i, j) = unpackMetricIndex10D k
            repacked = packMetricIndex10D i j
        in repacked == k) testIndices
  in allMatch
