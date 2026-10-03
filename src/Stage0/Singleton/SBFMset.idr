module Stage0.Singleton.SBFMset

import Stage0.Multiset
import Stage0.Pixel
import public Stage0.BoxInt
import public Stage0.Singleton.Bit

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
blueSBF : Multiset BoxInt (Pixel Blue Coord2D)
blueSBF = AddM (MkPixel X X) 1 (AddM (MkPixel Y Y) 1 ZeroM)

-- Row 8: Minkowski Red Form [ ((X, X), 1), ((Y, Y), -1) ] over BoxInt
public export
redSBF : Multiset BoxInt (Pixel Red Coord2D)
redSBF = AddM (MkPixel X X) 1 (AddM (MkPixel Y Y) (-1) ZeroM)

-- Row 9: Galilean Green Form [ ((X, Y), 1), ((Y, X), 1) ] over BoxInt
public export
greenSBF : Multiset BoxInt (Pixel Green Coord2D)
greenSBF = AddM (MkPixel X Y) 1 (AddM (MkPixel Y X) 1 ZeroM)

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
