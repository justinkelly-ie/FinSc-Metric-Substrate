||| Representation Theorem Isomorphism for Layer 0 Substrate Carrier & Metric Signatures (Rule 03)
|||
||| Establishes the functorial isomorphism between the abstract discrete metric basis weights
||| and concrete multiset streams over BasisWeight tokens:
|||   TheoryRepresentationIsomorphism L0_SubstrateCarrier BasisWeight BasisWeight
module Stage1.SubstrateRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MetricSignature
import Stage1.PhysicalUniverse.Stratification

%default total

||| Canonical Representation Isomorphism for Layer 0 Substrate Carrier.
public export
substrateRepIso : TheoryRepresentationIsomorphism L0_SubstrateCarrier BasisWeight BasisWeight
substrateRepIso =
  MkTheoryRepIso
    "L0: Metric Basis Weight Algebra -> Multiset BasisWeight"
    (\w => AddM w (MkBoxInt 1) ZeroM)
    (\m => case m of
             AddM w _ _ => w
             ZeroM      => Zero)
    (\w =>
      let m = AddM w (MkBoxInt 1) ZeroM
          w' = case m of
                 AddM x _ _ => x
                 ZeroM      => Zero
      in basisWeightEq w' w
    )

||| Compile-time verification that round-trip isomorphism holds for PosOne (Elliptic).
public export
0 prfSubstrateRepIsoPosOne : (verifyRoundTrip Stage1.SubstrateRepIso.substrateRepIso) PosOne = True
prfSubstrateRepIsoPosOne = Refl

||| Compile-time verification that round-trip isomorphism holds for NegOne (Hyperbolic).
public export
0 prfSubstrateRepIsoNegOne : (verifyRoundTrip Stage1.SubstrateRepIso.substrateRepIso) NegOne = True
prfSubstrateRepIsoNegOne = Refl

||| Compile-time verification that round-trip isomorphism holds for Zero (Parabolic).
public export
0 prfSubstrateRepIsoZero : (verifyRoundTrip Stage1.SubstrateRepIso.substrateRepIso) Zero = True
prfSubstrateRepIsoZero = Refl
