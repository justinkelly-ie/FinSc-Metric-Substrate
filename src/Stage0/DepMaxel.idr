module Stage0.DepMaxel

import Stage0.Multiset
import Stage0.DepMultiset
import public Stage0.Pixel

%default total

||| A dependently typed Maxel is a DepMultiset of Pixels.
public export
0 DepMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> (contents : Multiset c (Pixel metric a)) -> Type
DepMaxel metric c a contents = DepMultiset c (Pixel metric a) contents
