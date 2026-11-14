module Stage0.Pixel

import Stage0.Multiset
import Stage0.DepMultiset
import public Stage0.Basis.GeometricPixel
import Stage1.Basis.Coordinate
import Stage1.Carrier.CellMultiset

%default total

public export
data Metric = Blue | Red | Green | Substrate

public export
Eq Metric where
  Blue == Blue = True
  Red == Red = True
  Green == Green = True
  Substrate == Substrate = True
  _ == _ = False

public export
metricRank : Metric -> Nat
metricRank Blue      = 0
metricRank Red       = 1
metricRank Green     = 2
metricRank Substrate = 3

public export
Ord Metric where
  compare m1 m2 = compare (metricRank m1) (metricRank m2)

public export
Show Metric where
  show Blue = "Blue"
  show Red = "Red"
  show Green = "Green"
  show Substrate = "Substrate"

||| Canonical isomorphism between chromogeometric Metric and Layer 0A Geometry.
public export
metricToGeometry : Metric -> Geometry
metricToGeometry Blue      = Elliptic
metricToGeometry Red       = Hyperbolic
metricToGeometry Green     = Parabolic
metricToGeometry Substrate = Substrate

public export
geometryToMetric : Geometry -> Metric
geometryToMetric Elliptic   = Blue
geometryToMetric Hyperbolic = Red
geometryToMetric Parabolic  = Green
geometryToMetric Substrate  = Substrate

public export
0 prfMetricGeometryIso : (m : Metric) -> geometryToMetric (metricToGeometry m) = m
prfMetricGeometryIso Blue      = Refl
prfMetricGeometryIso Red       = Refl
prfMetricGeometryIso Green     = Refl
prfMetricGeometryIso Substrate = Refl

public export
0 prfGeometryMetricIso : (g : Geometry) -> metricToGeometry (geometryToMetric g) = g
prfGeometryMetricIso Elliptic   = Refl
prfGeometryMetricIso Hyperbolic = Refl
prfGeometryMetricIso Parabolic  = Refl
prfGeometryMetricIso Substrate  = Refl

||| The core fundamental data structure of the non-linear physics engine.
||| A 2-component coordinate representing a source and target (e.g. x and y).
public export
record Pixel (metric : Metric) (a : Type) where
  constructor MkPixel
  src : a
  tgt : a

||| Canonical unambiguous alias for chromogeometric 4-metric pixels.
public export
MetricPixel : Metric -> Type -> Type
MetricPixel = Pixel

public export
Eq a => Eq (Pixel metric a) where
  (MkPixel s1 t1) == (MkPixel s2 t2) = s1 == s2 && t1 == t2

public export
Ord a => Ord (Pixel metric a) where
  compare (MkPixel s1 t1) (MkPixel s2 t2) =
    case compare s1 s2 of
      EQ => compare t1 t2
      o  => o

public export
Show a => Show (Pixel metric a) where
  show (MkPixel s t) = "(" ++ show s ++ ", " ++ show t ++ ")"

||| Casts a Pixel from one metric index to another (phantom type cast).
public export
castMetric : {0 m2 : Metric} -> Pixel m1 a -> Pixel m2 a
castMetric (MkPixel s t) = MkPixel s t

||| Pixel multiplication in Wildberger's Box Arithmetic.
||| Iff b == c in [a,b] * [c,d] then the product is [a,d]
||| Otherwise, the product is Nothing.
public export
mulPixel : Eq a => Pixel metric a -> Pixel metric a -> Maybe (Pixel metric a)
mulPixel (MkPixel a b) (MkPixel c d) =
  if b == c then Just (MkPixel a d) else Nothing

------------------------------------------------------------------------
-- BRIDGES TO CANONICAL COORDCELL & DEPENDENT MAXELS
------------------------------------------------------------------------

||| Bridge from legacy MetricPixel to canonical CoordCell 2.
public export
metricPixelToCell2 : MetricPixel m Nat -> CoordCell 2
metricPixelToCell2 (MkPixel s t) = mkCell2 s t

||| Bridge from canonical CoordCell 2 to legacy MetricPixel.
public export
cell2ToMetricPixel : {0 m : Metric} -> CoordCell 2 -> MetricPixel m Nat
cell2ToMetricPixel c = MkPixel (pixelRow c) (pixelCol c)

||| A dependently typed Maxel is a DepMultiset of Pixels.
public export
0 DepMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> (contents : Multiset c (Pixel metric a)) -> Type
DepMaxel metric c a contents = DepMultiset c (Pixel metric a) contents

||| Canonical dependently typed Maxel indexed by CellMultiset 2.
public export
0 DepCellMaxel : (contents : CellMultiset 2) -> Type
DepCellMaxel contents = (m : CellMultiset 2 ** m = contents)

