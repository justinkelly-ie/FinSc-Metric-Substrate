module Stage1.ProjectiveRotation

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction as UF
import Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. 3D PROJECTIVE ROTATION PROPORTIONS (WILDBERGER SO(3; Q))
------------------------------------------------------------------------

||| A Projective Rotation Proportion (x : t : r : s):
||| Parameterizes an exact 3D rational rotation without continuous angles or square roots.
public export
record ProjectiveProportion where
  constructor MkProjectiveProportion
  xCoord : BoxInt
  tCoord : BoxInt
  rCoord : BoxInt
  sCoord : BoxInt

public export
Eq ProjectiveProportion where
  (MkProjectiveProportion x1 t1 r1 s1) == (MkProjectiveProportion x2 t2 r2 s2) =
    x1 == x2 && t1 == t2 && r1 == r2 && s1 == s2

public export
Show ProjectiveProportion where
  show (MkProjectiveProportion x t r s) =
    "(" ++ show x ++ " : " ++ show t ++ " : " ++ show r ++ " : " ++ show s ++ ")"

||| Extracts the 3D axis vector v = [t, r, s].
public export
proportionAxis : ProjectiveProportion -> Vect 3 BoxInt
proportionAxis p = [p.tCoord, p.rCoord, p.sCoord]

||| Euclidean quadrance of a 3D vector: Q(v) = t^2 + r^2 + s^2.
public export
quadranceEuc3 : Vect 3 BoxInt -> BoxInt
quadranceEuc3 [t, r, s] = (t * t) + (r * r) + (s * s)

||| Exact cross product of two 3D vectors: v1 x v2.
public export
crossProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> Vect 3 BoxInt
crossProduct3 [t1, r1, s1] [t2, r2, s2] =
  [ (r1 * s2) - (s1 * r2)
  , (s1 * t2) - (t1 * s2)
  , (t1 * r2) - (r1 * t2)
  ]

||| Exact dot product of two 3D vectors: <v1, v2>.
public export
dotProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> BoxInt
dotProduct3 [t1, r1, s1] [t2, r2, s2] = (t1 * t2) + (r1 * r2) + (s1 * s2)

||| Denominator Delta = x^2 + Q(v) = x^2 + t^2 + r^2 + s^2.
public export
proportionDenominator : ProjectiveProportion -> BoxInt
proportionDenominator p = (p.xCoord * p.xCoord) + quadranceEuc3 (proportionAxis p)

||| Half-spread token p = Q(v) / (x^2 + Q(v)).
public export
halfSpreadFraction : ProjectiveProportion -> UF.UnixelFraction
halfSpreadFraction p =
  let q = quadranceEuc3 (proportionAxis p)
      den = proportionDenominator p
  in UF.mkUnixelFraction q (boxToNat den)

||| Composition of two projective rotation proportions:
||| (x1 : v1) * (x2 : v2) = (x1 x2 - <v1, v2> : x1 v2 + x2 v1 + v1 x v2).
public export
composeProportion : ProjectiveProportion -> ProjectiveProportion -> ProjectiveProportion
composeProportion p1 p2 =
  let x1 = p1.xCoord
      x2 = p2.xCoord
      v1 = proportionAxis p1
      v2 = proportionAxis p2
      xOut = (x1 * x2) - dotProduct3 v1 v2
      [t1, r1, s1] = v1
      [t2, r2, s2] = v2
      [cx, cy, cz] = crossProduct3 v1 v2
      tOut = (x1 * t2) + (x2 * t1) + cx
      rOut = (x1 * r2) + (x2 * r1) + cy
      sOut = (x1 * s2) + (x2 * s1) + cz
  in MkProjectiveProportion xOut tOut rOut sOut

||| Inverse of a projective rotation proportion: (x : -t : -r : -s).
public export
inverseProportion : ProjectiveProportion -> ProjectiveProportion
inverseProportion (MkProjectiveProportion x t r s) =
  MkProjectiveProportion x (negate t) (negate r) (negate s)

------------------------------------------------------------------------
-- 2. ROTATION MAXEL & MATRIX EVALUATION (DELTA * PHI)
------------------------------------------------------------------------

||| Evaluates the un-normalized 3x3 numerator rotation matrix (Delta * Phi(x : v)):
||| Row 1: [x^2 + t^2 - r^2 - s^2,   2(tr - xs),             2(ts + xr)           ]
||| Row 2: [2(tr + xs),             x^2 - t^2 + r^2 - s^2,   2(rs - xt)           ]
||| Row 3: [2(ts - xr),             2(rs + xt),             x^2 - t^2 - r^2 + s^2 ]
public export
rotationMatrixScaled3 : ProjectiveProportion -> Vect 3 (Vect 3 BoxInt)
rotationMatrixScaled3 (MkProjectiveProportion x t r s) =
  let x2 = x * x
      t2 = t * t
      r2 = r * r
      s2 = s * s
      m00 = x2 + t2 - r2 - s2
      m01 = 2 * ((t * r) - (x * s))
      m02 = 2 * ((t * s) + (x * r))
      m10 = 2 * ((t * r) + (x * s))
      m11 = x2 - t2 + r2 - s2
      m12 = 2 * ((r * s) - (x * t))
      m20 = 2 * ((t * s) - (x * r))
      m21 = 2 * ((r * s) + (x * t))
      m22 = x2 - t2 - r2 + s2
  in [ [m00, m01, m02]
     , [m10, m11, m12]
     , [m20, m21, m22]
     ]

||| Applies the scaled rotation Delta * Phi(x : v) to a 3D vector.
public export
rotateVectorScaled : ProjectiveProportion -> Vect 3 BoxInt -> Vect 3 BoxInt
rotateVectorScaled prop v =
  stagedUnrollMatVec (rotationMatrixScaled3 prop) v

||| Applies rotation to a typed 3D vector VexelN 3.
public export
rotateVexelN3 : ProjectiveProportion -> VexelN 3 -> VexelN 3
rotateVexelN3 prop (MkVexelN v) =
  MkVexelN (rotateVectorScaled prop v)

||| Converts the scaled rotation matrix into an AVL MultisetTree-backed SquareMaxel 3.
public export
rotationMaxelScaled3 : ProjectiveProportion -> SquareMaxel 3
rotationMaxelScaled3 prop =
  maxelNToSquareMaxel (MkMaxelN (rotationMatrixScaled3 prop))

------------------------------------------------------------------------
-- 3. DEFORESTED STREAMING ROTATIONS
------------------------------------------------------------------------

||| Deforested stream transformer rotating a stream of 3D Vexel vectors in O(1) auxiliary memory.
public export
streamRotateVexelN3 : ProjectiveProportion -> FS.FusedStream (VexelN 3) -> FS.FusedStream (VexelN 3)
streamRotateVexelN3 prop =
  FS.mapStream (rotateVexelN3 prop)

||| Recurrence fold accumulating projective rotations along a reaction stream:
||| P_total = p_n * ... * p_2 * p_1.
public export
foldProportionStream : (fuel : Nat) -> FS.FusedStream ProjectiveProportion -> ProjectiveProportion
foldProportionStream fuel =
  FS.foldStreamNat fuel composeProportion (MkProjectiveProportion 1 0 0 0)

------------------------------------------------------------------------
-- 4. TOTALLY CONSTRUCTIVE PHYSICAL INVARIANTS
------------------------------------------------------------------------

||| Audit: The rotation axis v = [t, r, s] is an exact fixed eigenvector:
||| (Delta * Phi) v == Delta * v.
public export
auditAxisIsFixedEigenvector : ProjectiveProportion -> Bool
auditAxisIsFixedEigenvector prop =
  let axis = proportionAxis prop
      rotAxis = rotateVectorScaled prop axis
      delta = proportionDenominator prop
      scaledAxis = map (delta *) axis
  in rotAxis == scaledAxis

||| Audit: Quadrance scaling invariance:
||| Q((Delta * Phi) w) == Delta^2 * Q(w).
public export
auditQuadranceScalingInvariant : ProjectiveProportion -> Vect 3 BoxInt -> Bool
auditQuadranceScalingInvariant prop w =
  let rotW = rotateVectorScaled prop w
      qRot = quadranceEuc3 rotW
      qOrig = quadranceEuc3 w
      delta = proportionDenominator prop
      expectedQ = delta * delta * qOrig
  in qRot == expectedQ
