||| Quad-Stream Multiset Architecture & 55-State Substrate Law Ledger
|||
||| Bundles the three 4Geometries manifest streams (Blue Elliptic A_E, Red Hyperbolic A_H,
||| Green Parabolic A_P) with the 4th Dark Matter Substrate Law Stream (55 states)
||| corresponding to the 10D symmetric phase space metric space (10*11/2 = 55).
module Stage1.QuadStream

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage0.Multiset
import Stage1.MultisetTree
import Stage0.OnSeq.FusedStream
import Data.Fuel
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- 1. QUAD-STREAM MULTISET BUNDLE
--------------------------------------------------------------------------------

||| Quad-Stream Multiset Container bundling 3 manifest streams with 1 substrate law stream.
public export
record QuadStreamMultiset (k : Type) where
  constructor MkQuadStream
  ellipticStream   : Carrier k  -- Blue Manifest Stream (A_E, 27 states)
  hyperbolicStream : Carrier k  -- Red Relativistic Causal Stream (A_H, 128 states)
  parabolicStream  : Carrier k  -- Green Classical Dissipative Stream (A_P)
  substrateStream  : Carrier k  -- 4th Stream: Dark Matter Substrate Law Stream (55 states)

public export
(Eq k) => Eq (QuadStreamMultiset k) where
  (MkQuadStream e1 h1 p1 s1) == (MkQuadStream e2 h2 p2 s2) =
    e1 == e2 && h1 == h2 && p1 == p2 && s1 == s2

--------------------------------------------------------------------------------
-- 1b. QUAD-STREAM SECTOR OPTICS & VIEW LENSES
--------------------------------------------------------------------------------

||| Sectors of the Quad-Stream 4-channel payload.
public export
data QuadStreamChannel = EllipticSector | HyperbolicSector | ParabolicSector | SubstrateSector

public export
Eq QuadStreamChannel where
  EllipticSector == EllipticSector = True
  HyperbolicSector == HyperbolicSector = True
  ParabolicSector == ParabolicSector = True
  SubstrateSector == SubstrateSector = True
  _ == _ = False

||| Selects a specific channel carrier from a QuadStreamMultiset bundle.
public export
getQuadChannel : QuadStreamChannel -> QuadStreamMultiset k -> Carrier k
getQuadChannel EllipticSector   qs = qs.ellipticStream
getQuadChannel HyperbolicSector qs = qs.hyperbolicStream
getQuadChannel ParabolicSector  qs = qs.parabolicStream
getQuadChannel SubstrateSector  qs = qs.substrateStream

||| Updates a specific channel carrier inside a QuadStreamMultiset bundle.
public export
setQuadChannel : QuadStreamChannel -> Carrier k -> QuadStreamMultiset k -> QuadStreamMultiset k
setQuadChannel EllipticSector   m qs = { ellipticStream := m } qs
setQuadChannel HyperbolicSector m qs = { hyperbolicStream := m } qs
setQuadChannel ParabolicSector  m qs = { parabolicStream := m } qs
setQuadChannel SubstrateSector  m qs = { substrateStream := m } qs

||| Bidirectional Lens over QuadStreamMultiset sector.
public export
record QuadLens (k : Type) where
  constructor MkQuadLens
  targetChannel : QuadStreamChannel
  viewSector   : QuadStreamMultiset k -> Carrier k
  updateSector : Carrier k -> QuadStreamMultiset k -> QuadStreamMultiset k

||| Creates a QuadLens targeting the specified channel.
public export
makeQuadLens : QuadStreamChannel -> QuadLens k
makeQuadLens ch = MkQuadLens ch (getQuadChannel ch) (setQuadChannel ch)

||| Pre-instantiated QuadLens targeting EllipticSector (27 states - 3D manifest space).
public export
ellipticLens : QuadLens a
ellipticLens = makeQuadLens EllipticSector

||| Pre-instantiated QuadLens targeting HyperbolicSector (128 states - 2D spectral space).
public export
hyperbolicLens : QuadLens a
hyperbolicLens = makeQuadLens HyperbolicSector

||| Pre-instantiated QuadLens targeting ParabolicSector (dissipative channel).
public export
parabolicLens : QuadLens a
parabolicLens = makeQuadLens ParabolicSector

||| Pre-instantiated QuadLens targeting SubstrateSector (55 states - 10D phase space metric law ledger).
public export
substrateLens : QuadLens a
substrateLens = makeQuadLens SubstrateSector

||| Converts a 4-channel QuadStreamMultiset payload into a deforested FusedStream of channel-tagged entries.
public export
quadStreamToStream : QuadStreamMultiset k -> FusedStream (QuadStreamChannel, k, BoxInt)
quadStreamToStream (MkQuadStream e h p s) =
  let eStrm = mapStream (\(x, v) => (EllipticSector, x, v)) (streamBoxMultisetTree e)
      hStrm = mapStream (\(x, v) => (HyperbolicSector, x, v)) (streamBoxMultisetTree h)
      pStrm = mapStream (\(x, v) => (ParabolicSector, x, v)) (streamBoxMultisetTree p)
      sStrm = mapStream (\(x, v) => (SubstrateSector, x, v)) (streamBoxMultisetTree s)
  in eStrm <+> hStrm <+> pStrm <+> sStrm

||| Reconstructs a QuadStreamMultiset payload from a deforested stream using Fuel.
public export
streamToQuadStreamFuel : DiscreteCoord k => Fuel -> FusedStream (QuadStreamChannel, k, BoxInt) -> QuadStreamMultiset k
streamToQuadStreamFuel fuel strm =
  foldStreamFuel fuel (\qs, (ch, x, v) =>
    let lens = makeQuadLens ch
        currentMset = lens.viewSector qs
        newMset = currentMset <+> singletonCarrier x v
    in lens.updateSector newMset qs
  ) (MkQuadStream neutral neutral neutral neutral) strm

||| Reconstructs a QuadStreamMultiset payload from a deforested stream using Nat fuel bound.
public export
streamToQuadStreamNat : DiscreteCoord k => (fuel : Nat) -> FusedStream (QuadStreamChannel, k, BoxInt) -> QuadStreamMultiset k
streamToQuadStreamNat fuel strm =
  foldStreamNat fuel (\qs, (ch, x, v) =>
    let lens = makeQuadLens ch
        currentMset = lens.viewSector qs
        newMset = currentMset <+> singletonCarrier x v
    in lens.updateSector newMset qs
  ) (MkQuadStream neutral neutral neutral neutral) strm

||| Reconstructs a QuadStreamMultiset payload from a deforested stream with standard total fuel bound (1000).
public export
streamToQuadStream : DiscreteCoord k => FusedStream (QuadStreamChannel, k, BoxInt) -> QuadStreamMultiset k
streamToQuadStream = streamToQuadStreamNat 1000

||| Direct stream bundle of 4 distinct cosmological channel streams (Rule 04).
public export
record QuadStreamFusedBundle (a : Type) where
  constructor MkQuadStreamBundle
  ellipticChannel   : FusedStream (a, BoxInt)
  hyperbolicChannel : FusedStream (a, BoxInt)
  parabolicChannel  : FusedStream (a, BoxInt)
  substrateChannel  : FusedStream (a, BoxInt)

||| Flattens a QuadStreamFusedBundle into a single tagged stream without allocations.
public export
fusedBundleToTaggedStream : QuadStreamFusedBundle a -> FusedStream (QuadStreamChannel, a, BoxInt)
fusedBundleToTaggedStream (MkQuadStreamBundle e h p s) =
  let eStrm = mapStream (\(x, v) => (EllipticSector, x, v)) e
      hStrm = mapStream (\(x, v) => (HyperbolicSector, x, v)) h
      pStrm = mapStream (\(x, v) => (ParabolicSector, x, v)) p
      sStrm = mapStream (\(x, v) => (SubstrateSector, x, v)) s
  in eStrm <+> hStrm <+> pStrm <+> sStrm



||| Calculates total integer mass aggregated across all 4 sectors of a QuadStreamMultiset payload.
public export
quadStreamTotalMass : QuadStreamMultiset k -> BoxInt
quadStreamTotalMass (MkQuadStream e h p s) =
  totalMassBox e + totalMassBox h + totalMassBox p + totalMassBox s

||| Generates a QuadStreamMultiset payload directly from integer lattice coordinates (x, y)
||| in O(1) registers, where each carrier stores its respective quadrance at coordinate `1`:
||| - ellipticStream: Q_Blue = x^2 + y^2
||| - hyperbolicStream: Q_Red = x^2 - y^2
||| - parabolicStream: Q_Green = 2xy
||| - substrateStream: Q_Substrate = (Q_Blue + Q_Red + 2*Q_Green) / 2 = x^2 + 2xy.
public export
quadStreamFromLattice : (x, y : BoxInt) -> QuadStreamMultiset BoxInt
quadStreamFromLattice x y =
  let qb = (x * x) + (y * y)
      qr = (x * x) - (y * y)
      qg = intToBoxInt 2 * (x * y)
      qs = (x * x) + intToBoxInt 2 * (x * y)
      eStream = singletonCarrier (intToBoxInt 1) qb
      hStream = singletonCarrier (intToBoxInt 1) qr
      pStream = singletonCarrier (intToBoxInt 1) qg
      sStream = singletonCarrier (intToBoxInt 1) qs
  in MkQuadStream eStream hStream pStream sStream

||| Audits the 4-Geometry completion theorem over the lattice-generated QuadStreamMultiset:
||| 2 * substrate == elliptic + hyperbolic + 2 * parabolic.
public export
auditQuadStreamLatticeCompletion : (x, y : BoxInt) -> Bool
auditQuadStreamLatticeCompletion x y =
  let qs = quadStreamFromLattice x y
      qb = totalMassBox qs.ellipticStream
      qr = totalMassBox qs.hyperbolicStream
      qg = totalMassBox qs.parabolicStream
      qsub = totalMassBox qs.substrateStream
      lhs = intToBoxInt 2 * qsub
      rhs = qb + qr + intToBoxInt 2 * qg
  in lhs == rhs

||| Static compile-time witness verifying lens get-set identity property.
public export
0 verifyQuadLensGetSetIdentity : (qs : QuadStreamMultiset a) -> (ch : QuadStreamChannel) ->
  getQuadChannel ch (setQuadChannel ch (getQuadChannel ch qs) qs) = getQuadChannel ch qs
verifyQuadLensGetSetIdentity (MkQuadStream e h p s) EllipticSector = Refl
verifyQuadLensGetSetIdentity (MkQuadStream e h p s) HyperbolicSector = Refl
verifyQuadLensGetSetIdentity (MkQuadStream e h p s) ParabolicSector = Refl
verifyQuadLensGetSetIdentity (MkQuadStream e h p s) SubstrateSector = Refl

--------------------------------------------------------------------------------
-- 2. 55-STATE SUBSTRATE LAW LEDGER & PRIMORIAL 210 BUDGET
--------------------------------------------------------------------------------

||| Physical Law Ledger storing 55 independent metric law components post-Goh collapse.
public export
record SubstrateLawLedger55 where
  constructor MkSubstrateLawLedger55
  baryonBudget : Nat  -- 27 States (3^3 3D Manifest Space)
  darkBudget   : Nat  -- 55 States (10D Symmetric Phase Space Metric g_μν)
  vacuumBudget : Nat  -- 128 States (2^7 Information Saturation Space)

public export
Eq SubstrateLawLedger55 where
  (MkSubstrateLawLedger55 b1 d1 v1) == (MkSubstrateLawLedger55 b2 d2 v2) =
    b1 == b2 && d1 == d2 && v1 == v2

||| Canonical 55-state Substrate Law Ledger initialized to Primorial 210 capacity bounds.
public export
canonicalSubstrateLawLedger : SubstrateLawLedger55
canonicalSubstrateLawLedger = MkSubstrateLawLedger55 27 55 128

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME BUDGET CLOSURE PROOF WITNESSES
--------------------------------------------------------------------------------

||| Erased compile-time witness verifying Primorial 210 budget closure (27 + 55 + 128 = 210).
public export
0 QuadStreamBudgetWitness : (b : Nat) -> (d : Nat) -> (v : Nat) -> Type
QuadStreamBudgetWitness b d v = (b + d + v) = 210

||| Static compile-time witness proving canonical Quad-Stream budget closure (27 + 55 + 128 = 210).
public export
prfQuadStreamBudgetClosure : QuadStreamBudgetWitness 27 55 128
prfQuadStreamBudgetClosure = Refl

||| Static compile-time proof witness verifying 27 + 55 + 128 = 210.
public export
0 verifyQuadStreamBudgetClosure : (27 + 55 + 128) = 210
verifyQuadStreamBudgetClosure = Refl

||| Audits the Quad-Stream Primorial 210 budget conservation invariant.
public export
auditQuadStreamBudgetProof : SubstrateLawLedger55 -> Bool
auditQuadStreamBudgetProof (MkSubstrateLawLedger55 b d v) =
  (b + d + v) == 210
