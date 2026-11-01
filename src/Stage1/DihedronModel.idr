module Stage1.DihedronModel

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.UnixelFraction as UF
import Stage1.ProjectiveRotation as PR
import Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. 2x2 MINKOWSKI DIHEDRON MATRIX CARRIER (WILDBERGER SO(1, 2; Q))
------------------------------------------------------------------------

||| A 2x2 Dihedron matrix in M_2(Q):
||| D(x; t, r, s) = [ x + s,   r - t ]
|||                 [ r + t,   x - s ]
public export
record Dihedron2 where
  constructor MkDihedron2
  d00 : BoxInt
  d01 : BoxInt
  d10 : BoxInt
  d11 : BoxInt

public export
Eq Dihedron2 where
  (MkDihedron2 a00 a01 a10 a11) == (MkDihedron2 b00 b01 b10 b11) =
    a00 == b00 && a01 == b01 && a10 == b10 && a11 == b11

public export
Show Dihedron2 where
  show (MkDihedron2 a00 a01 a10 a11) =
    "Dihedron2[[" ++ show a00 ++ ", " ++ show a01 ++ "], [" ++ show a10 ++ ", " ++ show a11 ++ "]]"

||| Constructs a Dihedron2 from Minkowski proportion components (x; t, r, s).
public export
fromProportionMink : (x : BoxInt) -> (t : BoxInt) -> (r : BoxInt) -> (s : BoxInt) -> Dihedron2
fromProportionMink x t r s =
  MkDihedron2 (x + s) (r - t) (r + t) (x - s)

||| Deconstructs a Dihedron2 into proportion components (x; t, r, s).
public export
toProportionMink : Dihedron2 -> (BoxInt, BoxInt, BoxInt, BoxInt)
toProportionMink (MkDihedron2 d00 d01 d10 d11) =
  let x = (d00 + d11) `divBox` (intToBoxInt 2)
      s = (d00 - d11) `divBox` (intToBoxInt 2)
      r = (d10 + d01) `divBox` (intToBoxInt 2)
      t = (d10 - d01) `divBox` (intToBoxInt 2)
  in (x, t, r, s)

||| Determinant of a Dihedron2:
||| det(D) = (x + s)(x - s) - (r - t)(r + t) = x^2 + t^2 - r^2 - s^2 = x^2 + Q_Mink(v).
public export
detDihedron2 : Dihedron2 -> BoxInt
detDihedron2 (MkDihedron2 d00 d01 d10 d11) =
  (d00 * d11) - (d01 * d10)

||| Trace of a Dihedron2: tr(D) = 2x.
public export
trDihedron2 : Dihedron2 -> BoxInt
trDihedron2 (MkDihedron2 d00 _ _ d11) = d00 + d11

||| Identity dihedron: D(1; 0, 0, 0) = [[1, 0], [0, 1]].
public export
identityDihedron2 : Dihedron2
identityDihedron2 = MkDihedron2 1 0 0 1

||| Multiplication of two Dihedron2 matrices (2x2 matrix product):
||| Corresponds exactly to the dihedron composition groupoid!
public export
mulDihedron2 : Dihedron2 -> Dihedron2 -> Dihedron2
mulDihedron2 (MkDihedron2 a00 a01 a10 a11) (MkDihedron2 b00 b01 b10 b11) =
  MkDihedron2
    ((a00 * b00) + (a01 * b10))
    ((a00 * b01) + (a01 * b11))
    ((a10 * b00) + (a11 * b10))
    ((a10 * b01) + (a11 * b11))

||| Action of a Dihedron2 matrix on a 2D integer vector:
||| D * v = [[d00, d01], [d10, d11]] * [v0, v1] = [(d00*v0 + d01*v1), (d10*v0 + d11*v1)].
public export
actDihedronVect2 : Dihedron2 -> Vect 2 BoxInt -> Vect 2 BoxInt
actDihedronVect2 (MkDihedron2 d00 d01 d10 d11) [v0, v1] =
  [ (d00 * v0) + (d01 * v1)
  , (d10 * v0) + (d11 * v1)
  ]

||| 2LTT Staged Dihedron2 matrix multiplication:
public export
stagedMulDihedron2 : Lift Dihedron2 -> Lift Dihedron2 -> Code Dihedron2
stagedMulDihedron2 qd1 qd2 = quote (mulDihedron2 (splice qd1) (splice qd2))

||| Staged evaluation of Dihedron2 matrix multiplication:
public export
evalStagedMulDihedron2 : Lift Dihedron2 -> Lift Dihedron2 -> Dihedron2
evalStagedMulDihedron2 qd1 qd2 = splice (stagedMulDihedron2 qd1 qd2)

||| QTT 0 Erased Proof Witness: Staged Dihedron Multiplication Invariant
public export
0 prfStagedMulDihedron2 : (d1, d2 : Dihedron2) ->
                          splice (stagedMulDihedron2 (quote d1) (quote d2)) = mulDihedron2 d1 d2
prfStagedMulDihedron2 _ _ = Refl

||| 2LTT Staged Dihedron2 vector action:
public export
stagedActDihedronVect2 : Lift Dihedron2 -> Vect 2 BoxInt -> Code (Vect 2 BoxInt)
stagedActDihedronVect2 qd v = quote (actDihedronVect2 (splice qd) v)

||| Staged evaluation of Dihedron2 vector action:
public export
evalStagedActDihedronVect2 : Lift Dihedron2 -> Vect 2 BoxInt -> Vect 2 BoxInt
evalStagedActDihedronVect2 qd v = splice (stagedActDihedronVect2 qd v)

||| QTT 0 Erased Proof Witness: Staged Dihedron Vector Action Invariant
public export
0 prfStagedActDihedronVect2 : (d : Dihedron2) -> (v : Vect 2 BoxInt) ->
                             splice (stagedActDihedronVect2 (quote d) v) = actDihedronVect2 d v
prfStagedActDihedronVect2 _ _ = Refl

||| Adjugate of Dihedron2 (inverse up to determinant):
||| adj(D) = [[d11, -d01], [-d10, d00]] = D(x; -t, -r, -s).
public export
adjugateDihedron2 : Dihedron2 -> Dihedron2
adjugateDihedron2 (MkDihedron2 d00 d01 d10 d11) =
  MkDihedron2 d11 (negate d01) (negate d10) d00

||| Fast repeated squaring for Dihedron2 in O(log N) multiplications.
public export
fastDihedronPower : (fuel : Nat) -> Dihedron2 -> Nat -> Dihedron2
fastDihedronPower Z _ _ = identityDihedron2
fastDihedronPower (S _) _ Z = identityDihedron2
fastDihedronPower (S _) d (S Z) = d
fastDihedronPower (S f) d exp =
  let (half, isOdd) = natHalfAndOdd exp
      halfD = fastDihedronPower f d half
      squared = mulDihedron2 halfD halfD
  in if isOdd then mulDihedron2 d squared else squared

------------------------------------------------------------------------
-- 2. MINKOWSKI 3D QUADRANCE & RELATIVISTIC TRANSFORMATIONS
------------------------------------------------------------------------

||| Minkowski quadrance: Q_Mink(t, r, s) = t^2 - r^2 - s^2.
public export
quadranceMink3 : Vect 3 BoxInt -> BoxInt
quadranceMink3 [t, r, s] = (t * t) - (r * r) - (s * s)

||| Exact Projective Relativistic Velocity Addition (Wildberger Relativistic Rational Rotations 3):
||| (v, d_v) (+) (u, d_u) = (d_u v + d_v u - v x u, d_v d_u - <v, u>).
||| Preserves exact rational denominators in homogenous coordinates across multi-step composition.
public export
velocityAdditionProjective : (Vect 3 BoxInt, BoxInt) -> (Vect 3 BoxInt, BoxInt) -> (Vect 3 BoxInt, BoxInt)
velocityAdditionProjective (v1, d1) (v2, d2) =
  let [cx, cy, cz] = PR.crossProduct3 v1 v2
      [t1, r1, s1] = v1
      [t2, r2, s2] = v2
      numT = (d2 * t1) + (d1 * t2) - cx
      numR = (d2 * r1) + (d1 * r2) - cy
      numS = (d2 * s1) + (d1 * s2) - cz
      den = (d1 * d2) - PR.dotProduct3 v1 v2
  in ([numT, numR, numS], den)

||| Relativistic Anchor Product Velocity Addition for unit-denominator velocities:
||| v (+) u = (v + u - v x u) / (1 - <v, u>).
public export
velocityAdditionComponents : Vect 3 BoxInt -> Vect 3 BoxInt -> (Vect 3 BoxInt, BoxInt)
velocityAdditionComponents v1 v2 =
  velocityAdditionProjective (v1, intToBoxInt 1) (v2, intToBoxInt 1)

||| 2LTT Staged Projective Relativistic Velocity Addition:
public export
stagedVelocityAdditionProjective : Lift (Vect 3 BoxInt, BoxInt) ->
                                   Lift (Vect 3 BoxInt, BoxInt) ->
                                   Code (Vect 3 BoxInt, BoxInt)
stagedVelocityAdditionProjective qv1 qv2 =
  quote (velocityAdditionProjective (splice qv1) (splice qv2))

||| Staged evaluation of projective velocity addition:
public export
evalStagedVelocityAdditionProjective : Lift (Vect 3 BoxInt, BoxInt) ->
                                      Lift (Vect 3 BoxInt, BoxInt) ->
                                      (Vect 3 BoxInt, BoxInt)
evalStagedVelocityAdditionProjective qv1 qv2 =
  splice (stagedVelocityAdditionProjective qv1 qv2)

||| QTT 0 Erased Proof Witness: Staged Projective Velocity Addition Invariant
public export
0 prfStagedVelocityAdditionProjective : (v1, v2 : (Vect 3 BoxInt, BoxInt)) ->
                                       splice (stagedVelocityAdditionProjective (quote v1) (quote v2)) = velocityAdditionProjective v1 v2
prfStagedVelocityAdditionProjective _ _ = Refl

------------------------------------------------------------------------
-- 3. TOTALLY CONSTRUCTIVE PHYSICAL INVARIANTS
------------------------------------------------------------------------

||| Audit: Multiplicativity of Dihedron determinants:
||| det(D1 * D2) == det(D1) * det(D2).
public export
auditDihedronDeterminantMultiplicative : Dihedron2 -> Dihedron2 -> Bool
auditDihedronDeterminantMultiplicative d1 d2 =
  detDihedron2 (mulDihedron2 d1 d2) == (detDihedron2 d1 * detDihedron2 d2)

||| Audit: Adjugate inverse property:
||| D * adj(D) == det(D) * I.
public export
auditDihedronAdjugateIdentity : Dihedron2 -> Bool
auditDihedronAdjugateIdentity d =
  let prod = mulDihedron2 d (adjugateDihedron2 d)
      det = detDihedron2 d
  in prod == MkDihedron2 det 0 0 det

------------------------------------------------------------------------
-- 4. RELATIVISTIC SPREAD TRANSFER DIHEDRON & STREAM GENERATOR (PHASE 4)
------------------------------------------------------------------------

||| Transpose of a Dihedron2 matrix: D^T = D(x; -t, r, s).
public export
transposeDihedron2 : Dihedron2 -> Dihedron2
transposeDihedron2 (MkDihedron2 d00 d01 d10 d11) =
  MkDihedron2 d00 d10 d01 d11

||| Construct the companion spread transfer Dihedron:
||| M(s) = [[2 - 4s, -1], [1, 0]] = D(1 - 2s; 1, 0, 1 - 2s).
||| Determinant is identically +1 (unimodular Minkowski area preservation).
public export
spreadTransferDihedron : (s : BoxInt) -> Dihedron2
spreadTransferDihedron s =
  let x = intToBoxInt 1 - (intToBoxInt 2 * s)
  in fromProportionMink x (intToBoxInt 1) (intToBoxInt 0) x

||| Generates the deforested stream of successive multiple spreads S_n(s)
||| via Dihedron companion transfer stepping in O(1) memory.
||| Uses state (S_{n-1}, S_n) and affine recurrence:
||| S_{n+1} = (2 - 4s)*S_n - S_{n-1} + 2s.
public export
streamMinkowskiSpreadRecurrence : (fuel : Nat) -> (s : BoxInt) -> FS.FusedStream BoxInt
streamMinkowskiSpreadRecurrence fuel s =
  FS.MkStream {s = (Nat, BoxInt, BoxInt)} next (fuel, intToBoxInt 0, s)
  where
    next : (Nat, BoxInt, BoxInt) -> FS.Step (Nat, BoxInt, BoxInt) BoxInt
    next (Z, _, _) = FS.Done
    next (S k, sPrev, sCurr) =
      let d = spreadTransferDihedron s
          sNext = (d00 d * sCurr) + (d01 d * sPrev) + (intToBoxInt 2 * s)
      in FS.Yield sCurr (k, sCurr, sNext)

||| Audit: Spread transfer Dihedron has determinant +1 for any spread s.
public export
auditSpreadTransferDihedronUnimodular : (s : BoxInt) -> Bool
auditSpreadTransferDihedronUnimodular s =
  detDihedron2 (spreadTransferDihedron s) == intToBoxInt 1

||| Audit: streamMinkowskiSpreadRecurrence produces exact initial terms [s, 4s(1-s)] for s = 1.
public export
auditSpreadRecurrenceOrbitProof : Bool
auditSpreadRecurrenceOrbitProof =
  let s1 = intToBoxInt 1
      strm = streamMinkowskiSpreadRecurrence 2 s1
      orbit = FS.foldStreamNat 2 (\acc, x => acc ++ [x]) [] strm
  in orbit == [intToBoxInt 1, intToBoxInt 0] && auditSpreadTransferDihedronUnimodular s1
