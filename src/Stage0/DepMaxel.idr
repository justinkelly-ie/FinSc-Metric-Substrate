module Stage0.DepMaxel

import Stage0.Multiset
import Stage0.DepMultiset
import public Stage0.Pixel
import Stage1.Carrier.CellMultiset

%default total

||| A dependently typed Maxel is a DepMultiset of Pixels.
public export
0 DepMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> (contents : Multiset c (Pixel metric a)) -> Type
DepMaxel metric c a contents = DepMultiset c (Pixel metric a) contents

||| Canonical dependently typed Maxel indexed by CellMultiset 2.
public export
0 DepCellMaxel : (contents : CellMultiset 2) -> Type
DepCellMaxel contents = (m : CellMultiset 2 ** m = contents)

