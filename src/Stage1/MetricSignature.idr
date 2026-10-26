module Stage1.MetricSignature

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Basis.Coordinate
import Stage1.Carrier.Vexel
import Stage1.Carrier.Maxel
import Data.Vect
import Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. FUNDAMENTAL METRIC BASIS WEIGHTS
------------------------------------------------------------------------

||| Discrete basis weights for metric signature generation:
||| - NegOne: Timelike / Hyperbolic component (eigenvalue -1)
||| - Zero:   Lightlike / Parabolic component (eigenvalue 0)
||| - PosOne: Spacelike / Elliptic component (eigenvalue +1)
public export
data BasisWeight = NegOne | Zero | PosOne

%inline public export
basisWeightEq : BasisWeight -> BasisWeight -> Bool
basisWeightEq NegOne NegOne = True
basisWeightEq Zero   Zero   = True
basisWeightEq PosOne PosOne = True
basisWeightEq _      _      = False

public export
Eq BasisWeight where
  NegOne == NegOne = True
  Zero   == Zero   = True
  PosOne == PosOne = True
  _      == _      = False

public export
Show BasisWeight where
  show NegOne = "-1"
  show Zero   = "0"
  show PosOne = "+1"

||| Converts a BasisWeight into its discrete BoxInt scalar value.
%inline public export
weightToBoxInt : BasisWeight -> BoxInt
weightToBoxInt NegOne = MkBoxInt (-1)
weightToBoxInt Zero   = MkBoxInt 0
weightToBoxInt PosOne = MkBoxInt 1

------------------------------------------------------------------------
-- 2. METRIC SIGNATURE AS A DISCRETE MULTISET
------------------------------------------------------------------------

||| A Metric Signature is defined natively as a discrete multiset (Box) of BasisWeights.
||| Instead of continuous tensor fields, the metric form is determined solely by token counts.
public export
MetricSignature : Type
MetricSignature = Box BasisWeight

||| Monomorphic lookup of token multiplicity avoiding typeclass dictionary stalls.
public export
lookupWeight : BasisWeight -> MetricSignature -> BoxInt
lookupWeight _ (MkBox []) = MkBoxInt 0
lookupWeight target (MkBox ((w, c) :: rest)) =
  if basisWeightEq w target then c else lookupWeight target (MkBox rest)

||| Counts the number of occurrences of a given BasisWeight in a MetricSignature.
%inline public export
countWeight : BasisWeight -> MetricSignature -> Nat
countWeight w sig = boxToNat (lookupWeight w sig)

------------------------------------------------------------------------
-- 3. CANONICAL CHROMOGEOMETRIC 2D & 3D SIGNATURES
------------------------------------------------------------------------

||| Blue Elliptic 2D Signature: g = diag(+1, +1) (Two PosOne tokens).
public export
ellipticSignature2D : MetricSignature
ellipticSignature2D = MkBox [(PosOne, MkBoxInt 2)]

||| Red Hyperbolic 2D Signature: g = diag(+1, -1) (One PosOne, One NegOne).
public export
hyperbolicSignature2D : MetricSignature
hyperbolicSignature2D = MkBox [(PosOne, MkBoxInt 1), (NegOne, MkBoxInt 1)]

||| Green Parabolic 2D Signature: g = diag(+1, 0) (One PosOne, One Zero).
public export
parabolicSignature2D : MetricSignature
parabolicSignature2D = MkBox [(PosOne, MkBoxInt 1), (Zero, MkBoxInt 1)]

||| Null Substrate 2D Signature: g = diag(0, 0) (Two Zero tokens).
public export
substrateSignature2D : MetricSignature
substrateSignature2D = MkBox [(Zero, MkBoxInt 2)]

||| Blue Elliptic 3D Signature: 3D spatial canvas with three PosOne tokens.
public export
ellipticSignature3D : MetricSignature
ellipticSignature3D = MkBox [(PosOne, MkBoxInt 3)]

||| Minkowski 4D Relativistic Spacetime Signature: diag(+1, +1, +1, -1) (Three PosOne, One NegOne).
public export
minkowski4DSignature : MetricSignature
minkowski4DSignature = MkBox [(PosOne, MkBoxInt 3), (NegOne, MkBoxInt 1)]

------------------------------------------------------------------------
-- 4. CONSTRUCTING DIAGONAL MAXELS FROM MULTISET SIGNATURES
------------------------------------------------------------------------

||| Extracts the two diagonal metric weights from a 2D MetricSignature.
||| Uses pattern matching on canonical multiset constructors for definitional reduction.
public export
signatureWeights2D : MetricSignature -> (BoxInt, BoxInt)
signatureWeights2D (MkBox [(PosOne, MkBoxInt 2)])                            = (MkBoxInt 1, MkBoxInt 1)
signatureWeights2D (MkBox [(PosOne, MkBoxInt 1), (NegOne, MkBoxInt 1)])      = (MkBoxInt 1, MkBoxInt (-1))
signatureWeights2D (MkBox [(PosOne, MkBoxInt 1), (Zero, MkBoxInt 1)])        = (MkBoxInt 1, MkBoxInt 0)
signatureWeights2D (MkBox [(Zero, MkBoxInt 2)])                              = (MkBoxInt 0, MkBoxInt 0)
signatureWeights2D _                                                         = (MkBoxInt 1, MkBoxInt 1)

||| Generates a canonical 2D diagonal Maxel metric tensor from a 2D MetricSignature.
||| Uses token multiplicities directly to populate matrix diagonals.
public export
signatureToMaxel2D : MetricSignature -> Maxel
signatureToMaxel2D sig =
  let (w0, w1) = signatureWeights2D sig
  in singletonCell (mkPixel 0 0) w0 <+> singletonCell (mkPixel 1 1) w1

||| Evaluates the 2D Quadrance of a coordinate pair (x, y) under a MetricSignature:
||| Q(x, y) = g_00 * x^2 + g_11 * y^2
public export
signatureQuadrance2D : MetricSignature -> BoxInt -> BoxInt -> BoxInt
signatureQuadrance2D sig x y =
  let (w0, w1) = signatureWeights2D sig
      qx = mulBox w0 (mulBox x x)
      qy = mulBox w1 (mulBox y y)
  in addBox qx qy

||| Evaluates the exact 2D Quadrance of a CoordCell 2 under a MetricSignature.
public export
signatureCellQuadrance2D : MetricSignature -> CoordCell 2 -> BoxInt
signatureCellQuadrance2D sig c =
  signatureQuadrance2D sig (natToBoxInt (coordAxis 0 c)) (natToBoxInt (coordAxis 1 c))

------------------------------------------------------------------------
-- 5. TYPE-LEVEL PROOFS & WITNESSES
------------------------------------------------------------------------

||| Erased proof witness verifying that Blue Elliptic 2D quadrance of (3, 4) is 3^2 + 4^2 = 25.
public export
0 prfEllipticQuadrance25 : signatureQuadrance2D Stage1.MetricSignature.ellipticSignature2D (MkBoxInt 3) (MkBoxInt 4) = MkBoxInt 25
prfEllipticQuadrance25 = Refl

||| Erased proof witness verifying that Red Hyperbolic 2D quadrance of (5, 4) is 5^2 - 4^2 = 9.
public export
0 prfHyperbolicQuadrance9 : signatureQuadrance2D Stage1.MetricSignature.hyperbolicSignature2D (MkBoxInt 5) (MkBoxInt 4) = MkBoxInt 9
prfHyperbolicQuadrance9 = Refl

||| Erased proof witness verifying that Green Parabolic 2D quadrance of (3, 4) is 3^2 + 0 = 9.
public export
0 prfParabolicQuadrance9 : signatureQuadrance2D Stage1.MetricSignature.parabolicSignature2D (MkBoxInt 3) (MkBoxInt 4) = MkBoxInt 9
prfParabolicQuadrance9 = Refl

------------------------------------------------------------------------
-- 6. CANONICAL MAXELN 2 METRIC TENSORS & 2LTT STAGED QUADRANCES
------------------------------------------------------------------------

||| Blue Elliptic Metric Tensor as MaxelN 2: diag(1, 1), det = +1.
public export
ellipticMetricMaxel2 : MaxelN 2
ellipticMetricMaxel2 = mkMaxel2 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 1)

||| Red Hyperbolic Metric Tensor as MaxelN 2: diag(1, -1), det = -1.
public export
hyperbolicMetricMaxel2 : MaxelN 2
hyperbolicMetricMaxel2 = mkMaxel2 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt (-1))

||| Green Parabolic Metric Tensor as MaxelN 2: diag(1, 0), det = 0.
public export
parabolicMetricMaxel2 : MaxelN 2
parabolicMetricMaxel2 = mkMaxel2 (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)

||| Master Substrate Metric Tensor as MaxelN 2: [[0, 1], [0, 0]], causal arrow.
public export
substrateMetricMaxel2 : MaxelN 2
substrateMetricMaxel2 = mkMaxel2 (intToBoxInt 0) (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0)

||| Computes the 2D Chromatic Quadrance Q(v) = v^T * g * v using MaxelN 2 and VexelN 2.
public export
quadranceMaxelN2 : MaxelN 2 -> VexelN 2 -> BoxInt
quadranceMaxelN2 g (MkVexelN v) =
  let x = index 0 v
      y = index 1 v
      r0 = index 0 (rows g)
      r1 = index 1 (rows g)
      g00 = index 0 r0
      g01 = index 1 r0
      g10 = index 0 r1
      g11 = index 1 r1
      termX = mulBox x (addBox (mulBox g00 x) (mulBox g01 y))
      termY = mulBox y (addBox (mulBox g10 x) (mulBox g11 y))
  in addBox termX termY

||| 2LTT Staged 2D Quadrance evaluation at Stage 1.
public export
stagedQuadrance2D : Lift (MaxelN 2) -> VexelN 2 -> Code BoxInt
stagedQuadrance2D qg v = quote (quadranceMaxelN2 (splice qg) v)

||| Audits that 2D metric quadrances match expected values under MaxelN 2.
public export
auditMetricMaxel2Quadrances : Bool
auditMetricMaxel2Quadrances =
  let qEll = quadranceMaxelN2 ellipticMetricMaxel2 (mkVexel2 (intToBoxInt 3) (intToBoxInt 4))
      qHyp = quadranceMaxelN2 hyperbolicMetricMaxel2 (mkVexel2 (intToBoxInt 5) (intToBoxInt 4))
      qPar = quadranceMaxelN2 parabolicMetricMaxel2 (mkVexel2 (intToBoxInt 3) (intToBoxInt 4))
  in (qEll == intToBoxInt 25) && (qHyp == intToBoxInt 9) && (qPar == intToBoxInt 9)

