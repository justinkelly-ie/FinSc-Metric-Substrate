module Stage1.VexelStream

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.Basis.Coordinate
import Stage1.ProjectiveRotation as PR
import Stage1.DihedronModel as DM

%default total

------------------------------------------------------------------------
-- 2LTT STREAMING MULTISET VIEWS & BOXNAT CARRIERS
------------------------------------------------------------------------

||| Universal deforested FusedStream view of any CellMultiset dim in O(1) auxiliary registers.
public export
streamCellMultiset : {dim : Nat} -> CellMultiset dim -> FS.FusedStream (CoordCell dim, BoxInt)
streamCellMultiset t = MT.streamBoxMultisetTree t

||| Folds a deforested FusedStream directly into a CellMultiset dim with zero intermediate List allocations.
public export
streamToCellMultiset : {dim : Nat} -> FS.FusedStream (CoordCell dim, BoxInt) -> CellMultiset dim
streamToCellMultiset strm =
  FS.foldStream (\acc, (c, w) =>
    if boxIsZero w then acc
    else setBoxTree c (lookupBoxTree c acc + w) acc
  ) BoxLeaf strm

||| Deforested FusedStream view of a Vexel vector in O(1) auxiliary registers.
public export
streamVexel : Vexel -> FS.FusedStream (Unixel, BoxInt)
streamVexel = streamCellMultiset

||| Deforested FusedStream view of an AVL BoxMultisetTree-backed SquareMaxel matrix.
public export
streamSquareMaxel : SquareMaxel dim -> FS.FusedStream (Pixel, BoxInt)
streamSquareMaxel (MkSquareMaxel t) = streamCellMultiset t

||| Deforested FusedStream view of a Maxel matrix in O(1) auxiliary registers.
public export
streamMaxel : Maxel -> FS.FusedStream (Pixel, BoxInt)
streamMaxel = streamCellMultiset

||| Deforested FusedStream view of a Boxel volume tensor.
public export
streamBoxel : Boxel -> FS.FusedStream (Voxel, BoxInt)
streamBoxel = streamCellMultiset


||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed CellMultiset under BoxNat fuel bounds,
||| with zero intermediate List allocations.
public export
streamToCellMultisetBoxNat : {dim : Nat} -> BoxNat -> FS.FusedStream (CoordCell dim, BoxInt) -> CellMultiset dim
streamToCellMultisetBoxNat fuel strm =
  FS.foldStreamNat (boxNatToNat fuel) (\tree, (c, w) =>
    if boxIsZero w then tree
    else let cur = MT.lookupBoxTree c tree
             newW = cur + w
         in if boxIsZero newW
              then MT.setBoxTree c (intToBoxInt 0) tree
              else MT.setBoxTree c newW tree
  ) MT.BoxLeaf strm

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed SquareMaxel under BoxNat fuel bounds.
public export
streamToSquareMaxelBoxNat : {dim : Nat} -> BoxNat -> FS.FusedStream (Pixel, BoxInt) -> SquareMaxel dim
streamToSquareMaxelBoxNat fuel strm =
  MkSquareMaxel (streamToCellMultisetBoxNat fuel strm)

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed Vexel under BoxNat fuel bounds.
public export
streamToVexelBoxNat : BoxNat -> FS.FusedStream (Unixel, BoxInt) -> Vexel
streamToVexelBoxNat = streamToCellMultisetBoxNat

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed Maxel under BoxNat fuel bounds.
public export
streamToMaxelBoxNat : BoxNat -> FS.FusedStream (Pixel, BoxInt) -> Maxel
streamToMaxelBoxNat = streamToCellMultisetBoxNat

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed Boxel under BoxNat fuel bounds.
public export
streamToBoxelBoxNat : BoxNat -> FS.FusedStream (Voxel, BoxInt) -> Boxel
streamToBoxelBoxNat = streamToCellMultisetBoxNat

------------------------------------------------------------------------
-- WILDBERGER SUPPORT STREAM EXTRACTORS (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Deforested zero-allocation stream extractor for the active support of a Maxel stream.
||| Emits strictly non-zero directed coordinate cells without intermediate list allocations (Rule 04).
public export
supportMaxelStream : FS.FusedStream (Pixel, BoxInt) -> FS.FusedStream Pixel
supportMaxelStream =
  FS.filterMapStream (\(px, w) => if boxIsNonZero w then Just px else Nothing)

||| Deforested zero-allocation stream extractor for the active support of a Vexel stream.
||| Emits strictly non-zero basis Unixels without intermediate list allocations.
public export
supportVexelStream : FS.FusedStream (Unixel, BoxInt) -> FS.FusedStream Unixel
supportVexelStream =
  FS.filterMapStream (\(u, w) => if boxIsNonZero w then Just u else Nothing)

||| Deforested zero-allocation stream extractor for the active support of a Boxel stream.
public export
supportBoxelStream : FS.FusedStream (Voxel, BoxInt) -> FS.FusedStream Voxel
supportBoxelStream =
  FS.filterMapStream (\(vx, w) => if boxIsNonZero w then Just vx else Nothing)

------------------------------------------------------------------------
-- DEFORESTED MATRIX STREAM TRANSFORMERS (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Scales a Maxel pixel stream by a BoxInt scalar with zero intermediate allocations.
public export
scaleMaxelStream : BoxInt -> FS.FusedStream (Pixel, BoxInt) -> FS.FusedStream (Pixel, BoxInt)
scaleMaxelStream s =
  FS.mapStream (\(p, w) => (p, s * w))

||| Scales a Vexel basis stream by a BoxInt scalar with zero intermediate allocations.
public export
scaleVexelStream : BoxInt -> FS.FusedStream (Unixel, BoxInt) -> FS.FusedStream (Unixel, BoxInt)
scaleVexelStream s =
  FS.mapStream (\(u, w) => (u, s * w))

||| Common interface for geometric sparse multiset carriers backed by AVL trees.
public export
interface SparseCarrier c coord | c where
  toTree : c -> BoxMultisetTree coord
  fromTree : BoxMultisetTree coord -> c
  toStream : c -> FS.FusedStream (coord, BoxInt)
  fromStream : BoxNat -> FS.FusedStream (coord, BoxInt) -> c

public export
SparseCarrier Vexel Unixel where
  toTree t = t
  fromTree t = t
  toStream = streamVexel
  fromStream = streamToVexelBoxNat

public export
{dim : Nat} -> SparseCarrier (SquareMaxel dim) Pixel where
  toTree (MkSquareMaxel t) = t
  fromTree t = MkSquareMaxel t
  toStream = streamSquareMaxel
  fromStream = streamToSquareMaxelBoxNat

------------------------------------------------------------------------
-- DEFORESTED PROJECTIVE ROTATION & VELOCITY ADDITION STREAMS (PHASE 3)
------------------------------------------------------------------------

||| Deforested stream transformer rotating a stream of 3D Vexel vectors in O(1) auxiliary registers.
public export
streamRotateVexelN3 : PR.ProjectiveProportion -> FS.FusedStream (VexelN 3) -> FS.FusedStream (VexelN 3)
streamRotateVexelN3 prop =
  FS.mapStream (PR.rotateVexelN3 prop)

||| Deforested stream transformer accumulating relativistic velocities:
||| v_total = v_n (+) ... (+) v_1 using exact Wildberger anchor product addition.
public export
streamAccumulateVelocities : FS.FusedStream (Vect 3 BoxInt) -> FS.FusedStream (Vect 3 BoxInt, BoxInt)
streamAccumulateVelocities strm =
  FS.scanStream (\acc, u =>
    let (v, den) = acc
    in DM.velocityAdditionComponents v u
  ) ([0, 0, 0], 1) strm

