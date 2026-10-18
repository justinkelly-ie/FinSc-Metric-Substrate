module Stage1.Spacetime10D

import public Stage0.BoxInt
import public Stage1.VexelMaxel
import public Stage1.TypeTheory.Staging
import public Stage1.SymmetricMetricTensor

%default total

------------------------------------------------------------------------
-- BACKWARD-COMPATIBILITY SHIM FOR Stage1.Spacetime10D
------------------------------------------------------------------------

public export
packMetricIndex10D : (i : Nat) -> (j : Nat) -> Nat
packMetricIndex10D = packMetricIndex

public export
unpackMetricIndex10D : Nat -> (Nat, Nat)
unpackMetricIndex10D = unpackMetricIndex10

public export
allSymmetricPairs10D : List (Nat, Nat)
allSymmetricPairs10D = allSymmetricPairs 10

public export
makeSymmetricMetric10D : List (Nat, BoxInt) -> BoxSquareMaxel 10
makeSymmetricMetric10D weights =
  let MkSymmetricMetricTensor m = makeSymmetricMetric10 weights
  in m

public export
stagedIdentityMetric10D : Code (BoxSquareMaxel 10)
stagedIdentityMetric10D = quote (identityBoxSquareMaxel 10)
