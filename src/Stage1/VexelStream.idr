module Stage1.VexelStream

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree as MT
import Stage1.VexelMaxel as VM

%default total

------------------------------------------------------------------------
-- 2LTT STREAMING MULTISET VIEWS & BOXNAT CARRIERS
------------------------------------------------------------------------

||| Deforested FusedStream view of a Vexel vector.
public export
streamVexel : VM.Vexel -> FS.FusedStream (VM.Unixel, BoxInt)
streamVexel v = FS.multisetToStream (VM.vexelToMultiset v)

||| Deforested FusedStream view of a Maxel matrix.
public export
streamMaxel : VM.Maxel -> FS.FusedStream (VM.Pixel, BoxInt)
streamMaxel m = FS.multisetToStream (VM.maxelToMultiset m)

||| Deforested FusedStream view of a Boxel volume tensor.
public export
streamBoxel : VM.Boxel -> FS.FusedStream (VM.Voxel, BoxInt)
streamBoxel b = FS.multisetToStream (VM.boxelToMultiset b)

||| Folds a FusedStream into a Vexel under BoxNat fuel bounds.
public export
streamToVexelBoxNat : BoxNat -> FS.FusedStream (VM.Unixel, BoxInt) -> VM.Vexel
streamToVexelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, (u, w) => insertItemBox u w acc) ZeroM strm
  in VM.multisetToVexel m

||| Folds a FusedStream into a Maxel under BoxNat fuel bounds.
public export
streamToMaxelBoxNat : BoxNat -> FS.FusedStream (VM.Pixel, BoxInt) -> VM.Maxel
streamToMaxelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, (p, w) => insertItemBox p w acc) ZeroM strm
  in VM.multisetToMaxel m

||| Folds a FusedStream into a Boxel under BoxNat fuel bounds.
public export
streamToBoxelBoxNat : BoxNat -> FS.FusedStream (VM.Voxel, BoxInt) -> VM.Boxel
streamToBoxelBoxNat fuel strm =
  let m = FS.foldStreamNat (boxNatToNat fuel) (\acc, (v, w) => insertItemBox v w acc) ZeroM strm
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




