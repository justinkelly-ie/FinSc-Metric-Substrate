module Stage1.VexelStream

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS
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
