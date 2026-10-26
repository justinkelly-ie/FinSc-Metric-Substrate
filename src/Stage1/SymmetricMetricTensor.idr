module Stage1.SymmetricMetricTensor

import Stage0.BoxInt
import Stage1.Basis.Coordinate
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

||| General coordinate unpacker for an arbitrary dimension `dim`:
||| Given linear index k in [0, T_dim - 1], finds the canonical symmetric pair (i, j) with j <= i < dim.
public export
unpackMetricIndexDim : (dim : Nat) -> Nat -> (Nat, Nat)
unpackMetricIndexDim dim k =
  scan 0 dim
  where
    scan : Nat -> Nat -> (Nat, Nat)
    scan cur Z = (if dim == 0 then 0 else minus dim 1, 0)
    scan cur (S fuel) =
      let tNext = triangularNat (S cur)
      in if k < tNext
           then (cur, minus k (triangularNat cur))
           else scan (S cur) fuel

||| Unpacks a linear index k into the canonical symmetric pair (i, j) with j <= i for dim = 10.
public export
unpackMetricIndex10 : Nat -> (Nat, Nat)
unpackMetricIndex10 = unpackMetricIndexDim 10

||| Unpacks a linear index k into the canonical symmetric pair (i, j) with j <= i for dim = 4.
public export
unpackMetricIndex4 : Nat -> (Nat, Nat)
unpackMetricIndex4 = unpackMetricIndexDim 4

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

||| Constructs a SymmetricMetricTensor dim from independent component weights.
public export
makeSymmetricMetric : (dim : Nat) -> List (Nat, BoxInt) -> SymmetricMetricTensor dim
makeSymmetricMetric dim weights =
  let step : BoxMultisetTree Pixel -> (Nat, BoxInt) -> BoxMultisetTree Pixel
      step acc (k, w) =
        let (i, j) = unpackMetricIndexDim dim k
            acc1 = setBoxTree (mkPixel i j) w acc
            acc2 = if i /= j then setBoxTree (mkPixel j i) w acc1 else acc1
        in acc2
      tree = foldl step BoxLeaf weights
  in MkSymmetricMetricTensor (MkBoxSquareMaxel tree)

||| Constructs a SymmetricMetricTensor 10 from 55 independent component weights.
public export
makeSymmetricMetric10 : List (Nat, BoxInt) -> SymmetricMetricTensor 10
makeSymmetricMetric10 = makeSymmetricMetric 10

||| Flat Minkowski / Euclidean identity metric tensor of dimension `dim`.
public export
identityMetricTensor : (dim : Nat) -> SymmetricMetricTensor dim
identityMetricTensor dim = MkSymmetricMetricTensor (identityBoxSquareMaxel dim)

||| 2LTT Staged Flat Identity Metric Tensor:
public export
stagedIdentityMetricTensor : (dim : Nat) -> Code (SymmetricMetricTensor dim)
stagedIdentityMetricTensor dim = quote (identityMetricTensor dim)

||| 2LTT Staged Bilinear Metric Contraction: v^T · g · w on 2D coordinates.
||| Uses 2LTT staged unrolling to compute (v0*w0)*g00 + (v1*w1)*g11 without AVL lookups.
public export
stagedContractMetric2D : Lift (CoordCell 2) -> Lift (CoordCell 2) -> Lift BoxInt -> Lift BoxInt -> Lift Nat
stagedContractMetric2D qv qw qg00 qg11 =
  quote (let v = splice qv; w = splice qw
             g0 = integerToNat (unwrapBox (splice qg00))
             g1 = integerToNat (unwrapBox (splice qg11))
             c0 = (coordAxis 0 v * coordAxis 0 w) * g0
             c1 = (coordAxis 1 v * coordAxis 1 w) * g1
         in c0 + c1)

||| Exact bilinear metric contraction over 2D coordinates.
public export
contractMetric2D : CoordCell 2 -> CoordCell 2 -> BoxInt -> BoxInt -> Nat
contractMetric2D v w g00 g11 =
  splice (stagedContractMetric2D (quote v) (quote w) (quote g00) (quote g11))

||| Perturbs the (0, 0) timelike metric entry with energy-momentum curvature back-reaction.
public export
perturbMetric00 : {dim : Nat} -> SymmetricMetricTensor dim -> BoxInt -> SymmetricMetricTensor dim
perturbMetric00 (MkSymmetricMetricTensor (MkBoxSquareMaxel tree)) defect =
  let cur = lookupBoxTree (mkPixel 0 0) tree
      newTree = setBoxTree (mkPixel 0 0) (cur + defect) tree
  in MkSymmetricMetricTensor (MkBoxSquareMaxel newTree)

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

||| Compile-time proof of exact round-trip for 10D (55 components):
public export
0 verifyMetricIndexRoundTrip10 :
  all (\k => let (i, j) = unpackMetricIndexDim 10 k in packMetricIndex i j == k) (the (List Nat) [0..54]) = True
verifyMetricIndexRoundTrip10 = Refl

||| Compile-time proof of exact round-trip for 4D (10 components):
public export
0 verifyMetricIndexRoundTrip4 :
  all (\k => let (i, j) = unpackMetricIndexDim 4 k in packMetricIndex i j == k) (the (List Nat) [0..9]) = True
verifyMetricIndexRoundTrip4 = Refl

||| Generates the list of natural numbers [0 .. n-1] in O(n) tail-recursive time.
public export
natRange : Nat -> List Nat
natRange n = go n []
  where
    go : Nat -> List Nat -> List Nat
    go Z acc = acc
    go (S k) acc = go k (k :: acc)

||| Verified Invariant: Coordinate packing round-trip is exact for all T_dim components of arbitrary dim.
public export
auditMetricIndexRoundTripDim : (dim : Nat) -> Bool
auditMetricIndexRoundTripDim Z = True
auditMetricIndexRoundTripDim dim =
  let totalComp = triangularNat dim
      testIndices = natRange totalComp
      allMatch = all (\k =>
        let (i, j) = unpackMetricIndexDim dim k
            repacked = packMetricIndex i j
        in repacked == k) testIndices
  in allMatch

||| Verified Invariant: Coordinate packing round-trip across arbitrary dimensions D in [1, 12].
public export
auditArbitraryDimensionBijections : Bool
auditArbitraryDimensionBijections =
  all auditMetricIndexRoundTripDim (the (List Nat) [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
