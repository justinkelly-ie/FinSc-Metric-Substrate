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

------------------------------------------------------------------------
-- 2. CARRIER-GROUNDED BASIS MULTISETS & DIMENSIONS
------------------------------------------------------------------------

||| Fundamental color multiset carrier basis [RedColor, GreenColor, BlueColor].
public export
colorBasisList : List ColorCharge
colorBasisList = [RedColor, GreenColor, BlueColor]

||| Manifest spatial basis dimension L = 3 (T^3 spatial torus canvas),
||| grounded definitionally in the color charge multiset carrier cardinality.
public export
manifestSpatialDim : Nat
manifestSpatialDim = length colorBasisList

||| Elliptic 3D lattice state capacity: 3^3 = 27 states (Baryon/Visible Matter Canvas).
%inline public export
ellipticLatticeCapacity : Nat
ellipticLatticeCapacity = powerNat manifestSpatialDim manifestSpatialDim

||| The 7 imaginary octonionic units e_1 ... e_7 generating the Clifford algebra Cl(0, 7).
public export
data OctonionUnit = E1 | E2 | E3 | E4 | E5 | E6 | E7

public export
Eq OctonionUnit where
  E1 == E1 = True
  E2 == E2 = True
  E3 == E3 = True
  E4 == E4 = True
  E5 == E5 = True
  E6 == E6 = True
  E7 == E7 = True
  _  == _  = False

public export
Show OctonionUnit where
  show E1 = "e1"
  show E2 = "e2"
  show E3 = "e3"
  show E4 = "e4"
  show E5 = "e5"
  show E6 = "e6"
  show E7 = "e7"

||| The 7-element imaginary octonionic basis carrier.
public export
octonionBasisList : List OctonionUnit
octonionBasisList = [E1, E2, E3, E4, E5, E6, E7]

||| Clifford / octonion generator degrees D = 7,
||| grounded in the octonion basis multiset cardinality.
public export
cliffordGeneratorDim : Nat
cliffordGeneratorDim = length octonionBasisList

||| Hyperbolic 2D law storage ROM capacity: 2^7 = 128 states (Dark Energy ROM).
%inline public export
hyperbolicRomCapacity : Nat
hyperbolicRomCapacity = powerNat 2 cliffordGeneratorDim

||| 4D spacetime coordinate basis generators (t, x, y, z).
public export
data SpacetimeBasis = Time0 | Space1 | Space2 | Space3

public export
Eq SpacetimeBasis where
  Time0  == Time0  = True
  Space1 == Space1 = True
  Space2 == Space2 = True
  Space3 == Space3 = True
  _      == _      = False

public export
Show SpacetimeBasis where
  show Time0  = "t"
  show Space1 = "x"
  show Space2 = "y"
  show Space3 = "z"

public export
spacetimeBasisList : List SpacetimeBasis
spacetimeBasisList = [Time0, Space1, Space2, Space3]

||| 3-metric scale basis generators (Blue, Red, Green).
public export
data ScaleBasis = ScaleBlue | ScaleRed | ScaleGreen

public export
Eq ScaleBasis where
  ScaleBlue  == ScaleBlue  = True
  ScaleRed   == ScaleRed   = True
  ScaleGreen == ScaleGreen = True
  _          == _          = False

public export
Show ScaleBasis where
  show ScaleBlue  = "s_Blue"
  show ScaleRed   = "s_Red"
  show ScaleGreen = "s_Green"

public export
scaleBasisList : List ScaleBasis
scaleBasisList = [ScaleBlue, ScaleRed, ScaleGreen]

||| 10D phase space basis dimension: direct sum of spacetime (4) + color (3) + scale (3) basis carriers.
public export
phaseSpaceBasisDim : Nat
phaseSpaceBasisDim = length spacetimeBasisList + length colorBasisList + length scaleBasisList

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
