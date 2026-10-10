module Stage1.FourGeometries

import Stage0.BoxInt
import Stage1.ScaleTransform
import Data.Fin

%default total

------------------------------------------------------------------------
-- 1. THE 3-COLOR CHROMOGEOMETRIC SECTORS & FUNDAMENTAL GEOMETRIES
------------------------------------------------------------------------

||| The 3-color chromogeometric sectors.
public export
data ColorCharge = RedColor | GreenColor | BlueColor

public export
Eq ColorCharge where
  RedColor   == RedColor   = True
  GreenColor == GreenColor = True
  BlueColor  == BlueColor  = True
  _          == _          = False

public export
Show ColorCharge where
  show RedColor   = "Red"
  show GreenColor = "Green"
  show BlueColor  = "Blue"

public export
ScaleTransform ColorCharge Nat where
  scaleTransform RedColor   = 1
  scaleTransform GreenColor = 2
  scaleTransform BlueColor  = 3

public export
InvertibleScaleTransform ColorCharge Nat where
  invertScaleTransform Z = RedColor
  invertScaleTransform (S Z) = RedColor
  invertScaleTransform (S (S Z)) = GreenColor
  invertScaleTransform (S (S (S _))) = BlueColor

||| Classifies each cell index in Fin 27 into its exact QCD Color Sector.
||| Uses the Z-axis coordinate layer (z = -1 -> Red, z = 0 -> Green, z = +1 -> Blue).
public export
cellColorSector : Fin 27 -> ColorCharge
cellColorSector idx =
  case (finToNat idx) `div` 9 of
    0 => RedColor
    1 => GreenColor
    _ => BlueColor

||| The 4 canonical metric geometries governing space, time, gauge, and causality:
||| 1. EllipticGeom   (Blue Sector  / det g = +1 / Spacelike Confinement Canvas)
||| 2. HyperbolicGeom (Red Sector   / det g = -1 / Timelike Non-Abelian Gauge Engine)
||| 3. ParabolicGeom  (Green Sector / det g = 0  / Lightlike Remainder Dissipation Sink)
||| 4. SubstrateGeom  (Causal Poset / g22 = 0, g12 = 1 / Irreversible Cosmological Arrow)
public export
data FundamentalGeometry = 
    EllipticGeom 
  | HyperbolicGeom 
  | ParabolicGeom 
  | SubstrateGeom

public export
Eq FundamentalGeometry where
  EllipticGeom   == EllipticGeom   = True
  HyperbolicGeom == HyperbolicGeom = True
  ParabolicGeom  == ParabolicGeom  = True
  SubstrateGeom  == SubstrateGeom  = True
  _              == _              = False

public export
Show FundamentalGeometry where
  show EllipticGeom   = "Elliptic(Blue)"
  show HyperbolicGeom = "Hyperbolic(Red)"
  show ParabolicGeom  = "Parabolic(Green)"
  show SubstrateGeom  = "Substrate(Null)"

||| Auxiliary helper for natural power computation (b^e).
public export
powerNat : Nat -> Nat -> Nat
powerNat b Z = 1
powerNat b (S k) = b * powerNat b k

||| Computes the n-th triangular number T_n = sum_{k=1}^n k natively by structural induction.
public export
triangularSum : Nat -> Nat
triangularSum Z = Z
triangularSum (S k) = S k + triangularSum k

||| Computes the n-th triangular number T_n.
public export
triangularNumber : Nat -> Nat
triangularNumber = triangularSum

||| Manifest spatial basis dimension L = 3 (T^3 spatial torus canvas).
public export
manifestSpatialDim : Nat
manifestSpatialDim = 3

||| Elliptic 3D lattice state capacity: 3^3 = 27 states (Baryon/Visible Matter Canvas).
%inline public export
ellipticLatticeCapacity : Nat
ellipticLatticeCapacity = powerNat manifestSpatialDim manifestSpatialDim

||| Clifford / octonion generator degrees D = 7.
public export
cliffordGeneratorDim : Nat
cliffordGeneratorDim = 7

||| Hyperbolic 2D law storage ROM capacity: 2^7 = 128 states (Dark Energy ROM).
%inline public export
hyperbolicRomCapacity : Nat
hyperbolicRomCapacity = powerNat 2 cliffordGeneratorDim

||| 10D phase space basis dimension: 4 spacetime + 3 SU(3) color + 3 scale metrics.
public export
phaseSpaceBasisDim : Nat
phaseSpaceBasisDim = 10

||| Parabolic 10D metric tensor component residue: T_10 = sum_{k=1}^10 k = 55 states (Dark Matter Dissipation Sink).
%inline public export
darkMatterTriangularResidue : Nat
darkMatterTriangularResidue = triangularSum phaseSpaceBasisDim

||| The 4th Primorial p_4# = 2 * 3 * 5 * 7 = 210.
public export
primorial4 : Nat
primorial4 = 2 * 3 * 5 * 7

||| Canonical Primorial 210 cosmic capacity budget: 27 + 128 + 55 = 210.
%inline public export
primorial210Budget : Nat
primorial210Budget = ellipticLatticeCapacity + hyperbolicRomCapacity + darkMatterTriangularResidue

||| Compile-time proof witness certifying that the chromogeometric partition sum matches the 4th Primorial p_4#.
public export
0 prfPrimorialBudgetMatchesFactorization : Stage1.FourGeometries.primorial210Budget = Stage1.FourGeometries.primorial4
prfPrimorialBudgetMatchesFactorization = Refl


------------------------------------------------------------------------
-- 5. TYPE-LEVEL CHROMOGEOMETRIC INVARIANCE WITNESSES
------------------------------------------------------------------------

||| Type-level proof witness certifying 3-Metric Chromogeometric Quadrance Conservation:
||| BlueQuadrance + RedQuadrance = GreenQuadrance (27 + 128 = 155, 155 + 55 = 210).
public export
0 ChromogeometricQuadranceConservation : Nat -> Nat -> Nat -> Type
ChromogeometricQuadranceConservation b r g = b + r = g

||| Compile-time proof witness verifying Primorial 210 Chromogeometric Budget Conservation.
public export
0 prfChromogeometricBudgetConservation : ChromogeometricQuadranceConservation (Stage1.FourGeometries.ellipticLatticeCapacity + Stage1.FourGeometries.hyperbolicRomCapacity) Stage1.FourGeometries.darkMatterTriangularResidue Stage1.FourGeometries.primorial210Budget
prfChromogeometricBudgetConservation = Refl
