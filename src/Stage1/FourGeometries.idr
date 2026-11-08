module Stage1.FourGeometries

import Stage0.BoxInt
import Stage0.Pixel
import Stage0.StructuralFuel
import Stage1.ScaleTransform
import Stage1.TypeTheory.Smoothness
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

||| The carrier list of all 4 fundamental geometries (Elliptic, Hyperbolic, Parabolic, Substrate).
%inline public export
fundamentalGeometriesList : List FundamentalGeometry
fundamentalGeometriesList = [EllipticGeom, HyperbolicGeom, ParabolicGeom, SubstrateGeom]

||| Fundamental geometry count (4), observed directly from the carrier list cardinality.
%inline public export
fundamentalGeometryCount : Nat
fundamentalGeometryCount = length fundamentalGeometriesList

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

||| Canonical capacity partition across the 4 fundamental geometries (Rule 03 §1 & §2).
public export
geometryCapacity : FundamentalGeometry -> Nat
geometryCapacity EllipticGeom   = 27
geometryCapacity HyperbolicGeom = 128
geometryCapacity ParabolicGeom  = 55
geometryCapacity SubstrateGeom  = 210

||| Canonical token-to-geometry classifier mapping token influx index n (1 .. 210) to its exact geometry:
||| Sector capacity bounds:
||| - Parabolic (DM): 55 tokens (T_10 = 55 metric & dissipation sink)
||| - Elliptic  (VM): 27 tokens (3^3 = 27 visible matter & gluon basis)
||| - Hyperbolic(DE): 128 tokens (2^7 = 128 dark energy spectral register)
||| Total: 55 + 27 + 128 = 210 (Primorial master capacity budget).
public export
geometryAtTokenIndex : Nat -> FundamentalGeometry
geometryAtTokenIndex n =
  if n < 55 then ParabolicGeom
  else if n < 55 + 27 then EllipticGeom
  else HyperbolicGeom

||| Compile-time proof witness certifying exact zero-indexed capacity boundaries:
||| Parabolic [0..54] (55 tokens), Elliptic [55..81] (27 tokens), Hyperbolic [82..209] (128 tokens).
public export
0 prfGeometryAtTokenIndexBoundaries :
  ( geometryAtTokenIndex 0 = ParabolicGeom
  , geometryAtTokenIndex 54 = ParabolicGeom
  , geometryAtTokenIndex 55 = EllipticGeom
  , geometryAtTokenIndex 81 = EllipticGeom
  , geometryAtTokenIndex 82 = HyperbolicGeom
  , geometryAtTokenIndex 209 = HyperbolicGeom
  )
prfGeometryAtTokenIndexBoundaries = (Refl, Refl, Refl, Refl, Refl, Refl)

||| Bidirectional isomorphism: Converts Stage0 Metric to Stage1 FundamentalGeometry.
public export
metricToGeometry : Metric -> FundamentalGeometry
metricToGeometry Blue = EllipticGeom
metricToGeometry Red = HyperbolicGeom
metricToGeometry Green = ParabolicGeom
metricToGeometry Substrate = SubstrateGeom

||| Bidirectional isomorphism: Converts Stage1 FundamentalGeometry to Stage0 Metric.
public export
geometryToMetric : FundamentalGeometry -> Metric
geometryToMetric EllipticGeom = Blue
geometryToMetric HyperbolicGeom = Red
geometryToMetric ParabolicGeom = Green
geometryToMetric SubstrateGeom = Substrate

||| Auxiliary helper for natural power computation (b^e).
public export
powerNat : Nat -> Nat -> Nat
powerNat b Z = 1
powerNat b (S k) = b * powerNat b k

||| Computes the n-th triangular number T_n = sum_{k=1}^n k natively by structural induction.
public export
triangularSum : Nat -> Nat
triangularSum Z = Z
triangularSum (S k) = S k + Stage1.FourGeometries.triangularSum k

||| Computes the n-th triangular number T_n.
public export
triangularNumber : Nat -> Nat
triangularNumber = Stage1.FourGeometries.triangularSum

------------------------------------------------------------------------
-- 2. CARRIER-GROUNDED BASIS MULTISETS & DIMENSIONS
------------------------------------------------------------------------

||| Fundamental color multiset carrier basis [RedColor, GreenColor, BlueColor].
%inline public export
colorBasisList : List ColorCharge
colorBasisList = [RedColor, GreenColor, BlueColor]

||| Manifest spatial basis dimension L = 3 (T^3 spatial torus canvas),
||| grounded definitionally in the color charge multiset carrier cardinality.
%inline public export
manifestSpatialDim : Nat
manifestSpatialDim = length colorBasisList

||| Definitional proof that manifest spatial dimension matches color basis carrier length.
public export
0 prfManifestSpatialDimGrounded : Stage1.FourGeometries.manifestSpatialDim = length Stage1.FourGeometries.colorBasisList
prfManifestSpatialDimGrounded = Refl

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
%inline public export
octonionBasisList : List OctonionUnit
octonionBasisList = [E1, E2, E3, E4, E5, E6, E7]

||| Clifford / octonion generator degrees D = 7,
||| grounded in the octonion basis multiset cardinality.
%inline public export
cliffordGeneratorDim : Nat
cliffordGeneratorDim = length octonionBasisList

||| Definitional proof that Clifford generator dimension matches octonion basis length.
public export
0 prfCliffordGeneratorDimGrounded : Stage1.FourGeometries.cliffordGeneratorDim = length Stage1.FourGeometries.octonionBasisList
prfCliffordGeneratorDimGrounded = Refl

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

%inline public export
spacetimeBasisList : List SpacetimeBasis
spacetimeBasisList = [Time0, Space1, Space2, Space3]

||| 4D spacetime basis dimension (4), observed directly from the spacetime basis carrier list.
%inline public export
spacetimeBasisDim : Nat
spacetimeBasisDim = length spacetimeBasisList

||| Definitional proof that spacetime basis dimension matches spacetime basis list length.
public export
0 prfSpacetimeBasisDimGrounded : Stage1.FourGeometries.spacetimeBasisDim = length Stage1.FourGeometries.spacetimeBasisList
prfSpacetimeBasisDimGrounded = Refl

||| Definitional proof that spacetime dimension equals the number of fundamental geometries:
public export
0 prfSpacetimeDimEqualsGeometries : Stage1.FourGeometries.spacetimeBasisDim = Stage1.FourGeometries.fundamentalGeometryCount
prfSpacetimeDimEqualsGeometries = Refl

||| Definitional proof that spacetime dimension is the successor of manifest spatial dimension (1 temporal + 3 spatial):
public export
0 prfSpacetimeDimEqualsSpacePlusTime : Stage1.FourGeometries.spacetimeBasisDim = S Stage1.FourGeometries.manifestSpatialDim
prfSpacetimeDimEqualsSpacePlusTime = Refl

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

%inline public export
scaleBasisList : List ScaleBasis
scaleBasisList = [ScaleBlue, ScaleRed, ScaleGreen]

||| 3-metric scale basis dimension (3), observed directly from the scale basis carrier list.
%inline public export
scaleBasisDim : Nat
scaleBasisDim = length scaleBasisList

||| Definitional proof that scale basis dimension matches scale basis list length.
public export
0 prfScaleBasisDimGrounded : Stage1.FourGeometries.scaleBasisDim = length Stage1.FourGeometries.scaleBasisList
prfScaleBasisDimGrounded = Refl

||| 10D phase space basis dimension: direct sum of spacetime (4) + color (3) + scale (3) basis carriers.
%inline public export
phaseSpaceBasisDim : Nat
phaseSpaceBasisDim = spacetimeBasisDim + manifestSpatialDim + scaleBasisDim

||| Definitional proof that phase space dimension matches the basis list sum.
public export
0 prfPhaseSpaceBasisDimGrounded : Stage1.FourGeometries.phaseSpaceBasisDim = length Stage1.FourGeometries.spacetimeBasisList + length Stage1.FourGeometries.colorBasisList + length Stage1.FourGeometries.scaleBasisList
prfPhaseSpaceBasisDimGrounded = Refl

||| Parabolic 10D metric tensor component residue: T_10 = sum_{k=1}^10 k = 55 states (Dark Matter Dissipation Sink).
%inline public export
darkMatterTriangularResidue : Nat
darkMatterTriangularResidue = Stage1.FourGeometries.triangularSum phaseSpaceBasisDim

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

------------------------------------------------------------------------
-- 6. CERTIFIED CAPACITY DIMENSIONS (Rule 03)
------------------------------------------------------------------------

||| Certified manifest spatial basis dimension L = 3 (Sigma-pair).
public export
manifestSpatialDimension : CosmicDimension
manifestSpatialDimension = dimManifest

||| Certified Elliptic lattice state capacity: 3^3 = 27 (Sigma-pair).
public export
ellipticDimension : CosmicDimension
ellipticDimension = dimElliptic

||| Certified Hyperbolic ROM storage capacity: 2^7 = 128 (Sigma-pair).
public export
hyperbolicDimension : CosmicDimension
hyperbolicDimension = dimHyperbolic

||| Certified Parabolic dissipation sink residue: T_10 = 55 (Sigma-pair).
public export
darkMatterDimension : CosmicDimension
darkMatterDimension = dimParabolic

||| Certified Primorial 210 cosmic capacity budget: 27 + 128 + 55 = 210 (Sigma-pair).
public export
primorialBudgetDimension : CosmicDimension
primorialBudgetDimension = dimPrimorial

||| Maps each of the 4 fundamental geometries to its certified CosmicDimension Sigma-pair (Rule 03, Item 1 & 7).
public export
geometryDimension : FundamentalGeometry -> CosmicDimension
geometryDimension EllipticGeom   = ellipticDimension
geometryDimension HyperbolicGeom = hyperbolicDimension
geometryDimension ParabolicGeom  = darkMatterDimension
geometryDimension SubstrateGeom  = primorialBudgetDimension

||| Maps each of the 4 fundamental geometries to its certified EmergentCosmicDimension.
public export
geometryEmergentDimension : FundamentalGeometry -> EmergentCosmicDimension
geometryEmergentDimension EllipticGeom   = dimEmergentElliptic
geometryEmergentDimension HyperbolicGeom = dimEmergentHyperbolic
geometryEmergentDimension ParabolicGeom  = dimEmergentParabolic
geometryEmergentDimension SubstrateGeom  = dimEmergentPrimorial

||| Model-indexed GohFuel canonically derived from the certified dimension of the geometry (Rule 04, Item 4).
public export
geometryGohFuel : (geom : FundamentalGeometry) -> GohFuel (fst (geometryDimension geom))
geometryGohFuel geom = gohFuelForDim (geometryDimension geom)

||| Compile-time proof witness certifying capacity grounding for the 4 fundamental geometries:
||| Elliptic = 27, Hyperbolic = 128, Parabolic = 55, Substrate = 210.
public export
0 prfGeometryCapacities : ( fst (geometryDimension EllipticGeom) = 27
                          , fst (geometryDimension HyperbolicGeom) = 128
                          , fst (geometryDimension ParabolicGeom) = 55
                          , fst (geometryDimension SubstrateGeom) = 210
                          )
prfGeometryCapacities = (Refl, Refl, Refl, Refl)
