module Stage1.VexelStream

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.Carrier.Vexel
import Stage1.Carrier.Maxel
import Stage1.Carrier.Boxel
import Stage1.Basis.Coordinate
import Stage1.ProjectiveRotation as PR
import Stage1.DihedronModel as DM

%default total

------------------------------------------------------------------------
-- 2LTT STREAMING MULTISET VIEWS & BOXNAT CARRIERS
------------------------------------------------------------------------

||| Deforested FusedStream view of a Vexel vector in O(1) auxiliary registers.
public export
streamVexel : Vexel -> FS.FusedStream (Unixel, BoxInt)
streamVexel t = MT.streamBoxMultisetTree t

||| Deforested FusedStream view of an AVL MultisetTree-backed SparseVexel vector.
public export
streamSparseVexel : SparseVexel -> FS.FusedStream (Unixel, BoxInt)
streamSparseVexel (MkSparseVexel t) =
  FS.mapStream (\pair => let (u, cnt) = pair in (u, natToBoxInt cnt)) (MT.streamMultisetTreeDirect t)

||| Deforested FusedStream view of an AVL MultisetTree-backed SquareMaxel matrix.
public export
streamSquareMaxel : SquareMaxel dim -> FS.FusedStream (Pixel, BoxInt)
streamSquareMaxel (MkSquareMaxel t) =
  FS.mapStream (\pair => let (p, cnt) = pair in (p, natToBoxInt cnt)) (MT.streamMultisetTreeDirect t)

||| Deforested FusedStream view of a Maxel matrix in O(1) auxiliary registers.
public export
streamMaxel : Maxel -> FS.FusedStream (Pixel, BoxInt)
streamMaxel t = MT.streamBoxMultisetTree t

||| Deforested FusedStream view of a Boxel volume tensor.
public export
streamBoxel : Boxel -> FS.FusedStream (Voxel, BoxInt)
streamBoxel t = MT.streamBoxMultisetTree t


||| Folds a FusedStream directly into an AVL MultisetTree-backed SparseVexel under BoxNat fuel bounds,
||| with zero intermediate List allocations.
public export
streamToSparseVexelBoxNat : BoxNat -> FS.FusedStream (Unixel, BoxInt) -> SparseVexel
streamToSparseVexelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (u, w) = pair
            in if boxIsZero w then tree
               else MT.insertTokenTree u (boxToNat w) tree
          ) MT.Leaf strm
  in MkSparseVexel t

||| Folds a FusedStream directly into an AVL MultisetTree-backed SquareMaxel under BoxNat fuel bounds.
public export
streamToSquareMaxelBoxNat : {dim : Nat} -> BoxNat -> FS.FusedStream (Pixel, BoxInt) -> SquareMaxel dim
streamToSquareMaxelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (p, w) = pair
            in if boxIsZero w then tree
               else MT.insertTokenTree p (boxToNat w) tree
          ) MT.Leaf strm
  in MkSquareMaxel t

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed Vexel under BoxNat fuel bounds.
public export
streamToVexelBoxNat : BoxNat -> FS.FusedStream (Unixel, BoxInt) -> Vexel
streamToVexelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (u, w) = pair
            in if boxIsZero w then tree
               else let cur = MT.lookupBoxTree u tree
                        newW = cur + w
                    in if boxIsZero newW
                         then MT.setBoxTree u (intToBoxInt 0) tree
                         else MT.setBoxTree u newW tree
          ) MT.BoxLeaf strm
  in MkVexelTree t

||| Folds a FusedStream directly into an AVL BoxMultisetTree-backed Maxel under BoxNat fuel bounds.
public export
streamToMaxelBoxNat : BoxNat -> FS.FusedStream (Pixel, BoxInt) -> Maxel
streamToMaxelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (p, w) = pair
            in if boxIsZero w then tree
               else let cur = MT.lookupBoxTree p tree
                        newW = cur + w
                    in if boxIsZero newW
                         then MT.setBoxTree p (intToBoxInt 0) tree
                         else MT.setBoxTree p newW tree
          ) MT.BoxLeaf strm
  in MkMaxelTree t

||| Folds a FusedStream into a Boxel under BoxNat fuel bounds.
public export
streamToBoxelBoxNat : BoxNat -> FS.FusedStream (Voxel, BoxInt) -> Boxel
streamToBoxelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, pair => let (v, w) = pair in insertItemBox v w acc) ZeroM strm
  in multisetToBoxel m

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

||| Streams a balanced MaxelTree directly into a FusedStream in O(log N) stack frames.
public export
streamMaxelTreeDirect : MaxelTree -> FS.FusedStream (Pixel, BoxInt)
streamMaxelTreeDirect tree =
  FS.mapStream (\(p, cnt) => (p, natToBoxInt cnt)) (MT.streamMultisetTreeDirect tree)

||| Deforested discrete matrix multiplication stream transformer:
||| Multiplies a left Pixel stream by a right Pixel stream without intermediate list materialization.
public export
mulMaxelStream : FS.FusedStream (Pixel, BoxInt) -> FS.FusedStream (Pixel, BoxInt) -> FS.FusedStream (Pixel, BoxInt)
mulMaxelStream leftStream rightStream =
  FS.flatMapStream (\(p1, w1) =>
    FS.filterMapStream (\(p2, w2) =>
      case mulPixel p1 p2 of
        Just pOut => Just (pOut, w1 * w2)
        Nothing   => Nothing) rightStream) leftStream
------------------------------------------------------------------------
-- UNIFIED SPARSE CARRIER INTERFACE (PHASE 3)
-- Bridges AVL MultisetTree storage and FusedStream pipelines uniformly.
------------------------------------------------------------------------

||| Common interface for geometric sparse multiset carriers backed by AVL trees.
public export
interface SparseCarrier c coord | c where
  toTree : c -> MT.MultisetTree coord
  fromTree : MT.MultisetTree coord -> c
  toStream : c -> FS.FusedStream (coord, BoxInt)
  fromStream : BoxNat -> FS.FusedStream (coord, BoxInt) -> c

public export
SparseCarrier SparseVexel Unixel where
  toTree (MkSparseVexel t) = t
  fromTree t = MkSparseVexel t
  toStream = streamSparseVexel
  fromStream = streamToSparseVexelBoxNat

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

