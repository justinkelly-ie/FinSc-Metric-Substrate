module Stage0.Singleton.SBFMset

import Stage0.Multiset
import Stage0.Pixel
import Stage1.Basis.Coordinate
import Stage1.Lenses
import public Stage0.BoxInt
import public Stage0.Bit

%default total

-----------------------------------------------------------------------
-- 1. COORDINATE DOMAIN DEFINITIONS
-----------------------------------------------------------------------

||| Coordinate index for 1D logic wires
public export
0 Coord1D : Type
Coord1D = Nat

public export
Wire : Coord1D
Wire = 0

||| Coordinate index for 2D spatial metrics
public export
0 Coord2D : Type
Coord2D = Nat

public export
X : Coord2D
X = 0

public export
Y : Coord2D
Y = 1

-----------------------------------------------------------------------
-- 2. STATIC SBFMSET METRIC TEMPLATES
-----------------------------------------------------------------------

-- Row 1: Logical Parity Form [ ((Wire, Wire), 1) ] over Bit
public export
row1SBF : Multiset Bit (Pixel Blue Coord1D)
row1SBF = AddM (MkPixel Wire Wire) One ZeroM

-- Row 7: Euclidean Blue Form [ ((X, X), 1), ((Y, Y), 1) ] over BoxInt
public export
blueSBF : Carrier (Pixel Blue Coord2D)
blueSBF = singletonCarrier (MkPixel X X) 1 <+> singletonCarrier (MkPixel Y Y) 1

-- Row 8: Minkowski Red Form [ ((X, X), 1), ((Y, Y), -1) ] over BoxInt
public export
redSBF : Carrier (Pixel Red Coord2D)
redSBF = singletonCarrier (MkPixel X X) 1 <+> singletonCarrier (MkPixel Y Y) (-1)

-- Row 9: Galilean Green Form [ ((X, Y), 1), ((Y, X), 1) ] over BoxInt
public export
greenSBF : Carrier (Pixel Green Coord2D)
greenSBF = singletonCarrier (MkPixel X Y) 1 <+> singletonCarrier (MkPixel Y X) 1

-- Row 10: Master Substrate Form [ ((X, X), 1), ((X, Y), 1), ((Y, X), 1) ] over BoxInt
-- g_11 = 1, g_12 = 1, g_21 = 1, g_22 = 0 (det g = -1, asymmetric causal dissipation arrow, Rule 03 §1)
public export
substrateSBF : Carrier (Pixel Substrate Coord2D)
substrateSBF = singletonCarrier (MkPixel X X) 1
           <+> singletonCarrier (MkPixel X Y) 1
           <+> singletonCarrier (MkPixel Y X) 1

-----------------------------------------------------------------------
-- 3. UNIVERSAL EVALUATION PIPELINE
-----------------------------------------------------------------------

||| Construct the tensor outer product (u ⊗ v) of two input state vectors.
public export
tensorProduct : (Eq (a, b), Num c, Eq c) => Multiset c a -> Multiset c b -> Multiset c (a, b)
tensorProduct ZeroM _ = ZeroM
tensorProduct (AddM x cx xs) ys =
  let row = tensorWith x cx ys
  in addMultiset row (tensorProduct xs ys)
  where
    tensorWith : a -> c -> Multiset c b -> Multiset c (a, b)
    tensorWith _ _ ZeroM = ZeroM
    tensorWith x cx (AddM y cy rest) =
      insertItem (x, y) (cx * cy) (tensorWith x cx rest)

||| Construct the tensor self-product (v ⊗ v) of an input state vector.
public export
tensorSelf : (Eq a, Eq (a, a), Num c, Eq c) => Multiset c a -> Multiset c (a, a)
tensorSelf v = tensorProduct v v


||| The universal bilinear form evaluator.
||| Evaluates Q(v) = Sum( (v ⊗ v) · M ) across any domain and coefficient field.
public export
evalSBFMset : (Eq a, Eq (a, a), Num c, Eq c) => Multiset c (Pixel metric a) -> Multiset c a -> c
evalSBFMset matrix inputVec =
  let tensor = tensorSelf inputVec
  in matchSum matrix tensor
  where
    matchSum : Multiset c (Pixel metric a) -> Multiset c (a, a) -> c
    matchSum ZeroM _ = 0
    matchSum (AddM (MkPixel r c) w rest) t =
      let val = lookupCount (r, c) t
      in (w * val) + matchSum rest t

||| Constructivist Carrier-indexed bilinear form evaluator over `Box (Pixel metric a)`.
||| Evaluates Q(v) = Sum_{(r,c)} M[r,c] * v[r] * v[c] without intermediate tensor allocation.
public export
evalSBFCarrier : DiscreteCoord a => Carrier (Pixel metric a) -> Carrier a -> BoxInt
evalSBFCarrier matrix inputVec =
  foldBoxTreeL (\acc, (MkPixel r c, w) =>
    let vr = lookupBox r inputVec
        vc = lookupBox c inputVec
    in addBox acc (mulBox w (mulBox vr vc))
  ) (intToBoxInt 0) matrix

-----------------------------------------------------------------------
-- 4. CANONICAL CELLMULTISET 2 BILINEAR METRIC FORMS
-----------------------------------------------------------------------

public export
blueCellSBF : CellMultiset 2
blueCellSBF = singletonCell (mkCell2 X X) (intToBoxInt 1) <+> singletonCell (mkCell2 Y Y) (intToBoxInt 1)

public export
redCellSBF : CellMultiset 2
redCellSBF = singletonCell (mkCell2 X X) (intToBoxInt 1) <+> singletonCell (mkCell2 Y Y) (intToBoxInt (-1))

public export
greenCellSBF : CellMultiset 2
greenCellSBF = singletonCell (mkCell2 X Y) (intToBoxInt 1) <+> singletonCell (mkCell2 Y X) (intToBoxInt 1)

public export
substrateCellSBF : CellMultiset 2
substrateCellSBF = singletonCell (mkCell2 X X) (intToBoxInt 1) <+> 
                   singletonCell (mkCell2 X Y) (intToBoxInt 1) <+> 
                   singletonCell (mkCell2 Y X) (intToBoxInt 1)

||| Universal bilinear form evaluator on canonical CellMultiset carriers: Q(v) = v^T · M · v.
||| Evaluates over O(log N) AVL tree carriers with zero intermediate list allocations.
public export
evalCellSBF : CellMultiset 2 -> CellMultiset 1 -> BoxInt
evalCellSBF metric vec =
  foldBoxTreeL (\acc, (p, w) =>
    let (u, v) = pixelSplitUnixels p
        vu = lookupBoxTree u vec
        vv = lookupBoxTree v vec
    in acc + (w * vu * vv)
  ) (intToBoxInt 0) metric

||| Static verification witness: Substrate CellMultiset bilinear form on v = (1, 1) yields 3.
||| (1 * 1^2) + 2 * (1 * 1 * 1) + (0 * 1^2) = 1 + 2 + 0 = 3.
public export
auditSubstrateCellSBFProof : Bool
auditSubstrateCellSBFProof =
  let vec = singletonCell (mkUnixel X) (intToBoxInt 1) <+> singletonCell (mkUnixel Y) (intToBoxInt 1)
  in evalCellSBF substrateCellSBF vec == intToBoxInt 3

||| Canonical aliases connecting legacy SBF names to canonical CellMultiset 2 metrics:
public export
blueSBFCell : CellMultiset 2
blueSBFCell = blueCellSBF

public export
redSBFCell : CellMultiset 2
redSBFCell = redCellSBF

public export
greenSBFCell : CellMultiset 2
greenSBFCell = greenCellSBF

public export
substrateSBFCell : CellMultiset 2
substrateSBFCell = substrateCellSBF




------------------------------------------------------------------------
-- EXTERNAL PHYSICAL LENS BINDINGS (`Stage1.Lenses` over `PureMultiset`)
------------------------------------------------------------------------

||| Maps a Pixel chromogeometry sector to its external `MetricLens` (`Stage1.Lenses`).
public export
sbfMetricToLens : Metric -> MetricLens
sbfMetricToLens Blue      = blueEuclideanLens
sbfMetricToLens Red       = redMinkowskiLens
sbfMetricToLens Green     = greenGalileanLens
sbfMetricToLens Substrate = redMinkowskiLens

||| Canonical external Laurent scale and thermodynamic lenses attached to SBF carriers.
public export
sbfScaleLens : ScaleLens
sbfScaleLens = laurentScaleLens

public export
sbfThermoLens : ThermodynamicLens
sbfThermoLens = defaultThermoLens

||| Evaluates `<u, v>` on `PureMultiset` 3-vectors through the external `MetricLens` for `Metric`.
public export
evalSBFWithLens : Metric -> PureMultiset -> PureMultiset -> BoxInt
evalSBFWithLens m = traceWith (sbfMetricToLens m)

||| Evaluates forward causal precedence `u < v` under the selected sector's `MetricLens`.
public export
sbfMetricCausalPrecedence : Metric -> PureMultiset -> PureMultiset -> Bool
sbfMetricCausalPrecedence m = (sbfMetricToLens m).causallyPrecedes
