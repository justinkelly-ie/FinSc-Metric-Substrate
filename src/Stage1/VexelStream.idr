module Stage1.VexelStream

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.VexelMaxel as VM
import Stage1.ProjectiveRotation as PR
import Stage1.DihedronModel as DM

%default total

------------------------------------------------------------------------
-- 2LTT STREAMING MULTISET VIEWS & BOXNAT CARRIERS
------------------------------------------------------------------------

||| Deforested FusedStream view of a Vexel vector.
public export
streamVexel : VM.Vexel -> FS.FusedStream (VM.Unixel, BoxInt)
streamVexel v = FS.multisetToStream (VM.vexelToMultiset v)

||| Deforested FusedStream view of an AVL MultisetTree-backed SparseVexel vector.
public export
streamSparseVexel : VM.SparseVexel -> FS.FusedStream (VM.Unixel, BoxInt)
streamSparseVexel (VM.MkSparseVexel t) =
  FS.mapStream (\pair => let (u, cnt) = pair in (u, natToBoxInt cnt)) (MT.streamMultisetTreeDirect t)

||| Deforested FusedStream view of an AVL MultisetTree-backed SquareMaxel matrix.
public export
streamSquareMaxel : VM.SquareMaxel dim -> FS.FusedStream (VM.Pixel, BoxInt)
streamSquareMaxel (VM.MkSquareMaxel t) =
  FS.mapStream (\pair => let (p, cnt) = pair in (p, natToBoxInt cnt)) (MT.streamMultisetTreeDirect t)

||| Deforested FusedStream view of a Maxel matrix.
public export
streamMaxel : VM.Maxel -> FS.FusedStream (VM.Pixel, BoxInt)
streamMaxel m = FS.multisetToStream (VM.maxelToMultiset m)

||| Deforested FusedStream view of a Boxel volume tensor.
public export
streamBoxel : VM.Boxel -> FS.FusedStream (VM.Voxel, BoxInt)
streamBoxel b = FS.multisetToStream (VM.boxelToMultiset b)

||| Folds a FusedStream directly into an AVL MultisetTree-backed SparseVexel under BoxNat fuel bounds,
||| with zero intermediate List allocations.
public export
streamToSparseVexelBoxNat : BoxNat -> FS.FusedStream (VM.Unixel, BoxInt) -> VM.SparseVexel
streamToSparseVexelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (u, w) = pair
            in if unwrapBox w == 0 then tree
               else MT.insertTokenTree u (boxToNat w) tree
          ) MT.Leaf strm
  in VM.MkSparseVexel t

||| Folds a FusedStream directly into an AVL MultisetTree-backed SquareMaxel under BoxNat fuel bounds.
public export
streamToSquareMaxelBoxNat : {dim : Nat} -> BoxNat -> FS.FusedStream (VM.Pixel, BoxInt) -> VM.SquareMaxel dim
streamToSquareMaxelBoxNat fuel strm =
  let t = FS.foldStreamNat (boxNatToNat fuel) (\tree, pair =>
            let (p, w) = pair
            in if unwrapBox w == 0 then tree
               else MT.insertTokenTree p (boxToNat w) tree
          ) MT.Leaf strm
  in VM.MkSquareMaxel t

||| Folds a FusedStream into a Vexel under BoxNat fuel bounds.
public export
streamToVexelBoxNat : BoxNat -> FS.FusedStream (VM.Unixel, BoxInt) -> VM.Vexel
streamToVexelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, pair => let (u, w) = pair in insertItemBox u w acc) ZeroM strm
  in VM.multisetToVexel m

||| Folds a FusedStream into a Maxel under BoxNat fuel bounds.
public export
streamToMaxelBoxNat : BoxNat -> FS.FusedStream (VM.Pixel, BoxInt) -> VM.Maxel
streamToMaxelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, pair => let (p, w) = pair in insertItemBox p w acc) ZeroM strm
  in VM.multisetToMaxel m

||| Folds a FusedStream into a Boxel under BoxNat fuel bounds.
public export
streamToBoxelBoxNat : BoxNat -> FS.FusedStream (VM.Voxel, BoxInt) -> VM.Boxel
streamToBoxelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, pair => let (v, w) = pair in insertItemBox v w acc) ZeroM strm
  in VM.multisetToBoxel m

------------------------------------------------------------------------
-- WILDBERGER SUPPORT STREAM EXTRACTORS (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Deforested zero-allocation stream extractor for the active support of a Maxel stream.
||| Emits strictly non-zero directed coordinate cells without intermediate list allocations (Rule 04).
public export
supportMaxelStream : FS.FusedStream (VM.Pixel, BoxInt) -> FS.FusedStream VM.Pixel
supportMaxelStream =
  FS.filterMapStream (\(px, w) => if unwrapBox w /= 0 then Just px else Nothing)

||| Deforested zero-allocation stream extractor for the active support of a Vexel stream.
||| Emits strictly non-zero basis Unixels without intermediate list allocations.
public export
supportVexelStream : FS.FusedStream (VM.Unixel, BoxInt) -> FS.FusedStream VM.Unixel
supportVexelStream =
  FS.filterMapStream (\(u, w) => if unwrapBox w /= 0 then Just u else Nothing)

||| Deforested zero-allocation stream extractor for the active support of a Boxel stream.
public export
supportBoxelStream : FS.FusedStream (VM.Voxel, BoxInt) -> FS.FusedStream VM.Voxel
supportBoxelStream =
  FS.filterMapStream (\(vx, w) => if unwrapBox w /= 0 then Just vx else Nothing)

------------------------------------------------------------------------
-- DEFORESTED MATRIX STREAM TRANSFORMERS (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Scales a Maxel pixel stream by a BoxInt scalar with zero intermediate allocations.
public export
scaleMaxelStream : BoxInt -> FS.FusedStream (VM.Pixel, BoxInt) -> FS.FusedStream (VM.Pixel, BoxInt)
scaleMaxelStream s =
  FS.mapStream (\(p, w) => (p, s * w))

||| Scales a Vexel basis stream by a BoxInt scalar with zero intermediate allocations.
public export
scaleVexelStream : BoxInt -> FS.FusedStream (VM.Unixel, BoxInt) -> FS.FusedStream (VM.Unixel, BoxInt)
scaleVexelStream s =
  FS.mapStream (\(u, w) => (u, s * w))

||| Streams a balanced MaxelTree directly into a FusedStream in O(log N) stack frames.
public export
streamMaxelTreeDirect : VM.MaxelTree -> FS.FusedStream (VM.Pixel, BoxInt)
streamMaxelTreeDirect tree =
  FS.mapStream (\(p, cnt) => (p, natToBoxInt cnt)) (MT.streamMultisetTreeDirect tree)

||| Deforested discrete matrix multiplication stream transformer:
||| Multiplies a left Pixel stream by a right Pixel stream without intermediate list materialization.
public export
mulMaxelStream : FS.FusedStream (VM.Pixel, BoxInt) -> FS.FusedStream (VM.Pixel, BoxInt) -> FS.FusedStream (VM.Pixel, BoxInt)
mulMaxelStream leftStream rightStream =
  FS.flatMapStream (\(p1, w1) =>
    FS.filterMapStream (\(p2, w2) =>
      case VM.mulPixel p1 p2 of
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
SparseCarrier VM.SparseVexel VM.Unixel where
  toTree (VM.MkSparseVexel t) = t
  fromTree t = VM.MkSparseVexel t
  toStream = streamSparseVexel
  fromStream = streamToSparseVexelBoxNat

public export
{dim : Nat} -> SparseCarrier (VM.SquareMaxel dim) VM.Pixel where
  toTree (VM.MkSquareMaxel t) = t
  fromTree t = VM.MkSquareMaxel t
  toStream = streamSquareMaxel
  fromStream = streamToSquareMaxelBoxNat

------------------------------------------------------------------------
-- DEFORESTED PROJECTIVE ROTATION & VELOCITY ADDITION STREAMS (PHASE 3)
------------------------------------------------------------------------

||| Deforested stream transformer rotating a stream of 3D Vexel vectors in O(1) auxiliary registers.
public export
streamRotateVexelN3 : PR.ProjectiveProportion -> FS.FusedStream (VM.VexelN 3) -> FS.FusedStream (VM.VexelN 3)
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

