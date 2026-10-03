module Stage1.Topology.Boundaries

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.VexelMaxel
import Data.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- MULTISET DISCRETE CELL COMPLEX & BOUNDARY OPERATORS (∂² = 0)
-- 0-Cells (Vertices)   : Unixel / Vexel (Multiset BoxInt Unixel)
-- 1-Cells (Edges)      : Pixel / Maxel  (Multiset BoxInt Pixel)
-- 2-Cells (Plaquettes) : Maxel (Face Edge Loops)
--------------------------------------------------------------------------------

||| Pure Multiset Boundary operator ∂₁ : Multiset BoxInt Pixel -> Multiset BoxInt Unixel
||| mapping an edge multiset (1-cells) to its vertex multiset boundary (0-cells).
||| For each directed edge [u -> v] with weight w, ∂₁([u -> v]) = +w [v] - w [u].
public export
multisetBoundary1To0 : Multiset BoxInt Pixel -> Multiset BoxInt Unixel
multisetBoundary1To0 ZeroM = ZeroM
multisetBoundary1To0 (AddM (MkPixel u v) w rest) =
  insertItemBox (MkUnixel v) w (insertItemBox (MkUnixel u) (negBox w) (multisetBoundary1To0 rest))

||| Canonical Maxel to Vexel boundary operator ∂₁ : Maxel -> Vexel.
public export
boundaryMaxelToVexel : Maxel -> Vexel
boundaryMaxelToVexel m = multisetToVexel (multisetBoundary1To0 (maxelToMultiset m))

||| Pure Multiset Boundary operator ∂₂ : List Pixel -> Multiset BoxInt Pixel
||| mapping a 2-cell (closed edge loop) to its edge multiset boundary (1-cells).
public export
multisetBoundary2To1 : List Pixel -> Multiset BoxInt Pixel
multisetBoundary2To1 [] = ZeroM
multisetBoundary2To1 (p :: rest) = insertItemBox p (intToBoxInt 1) (multisetBoundary2To1 rest)

||| Canonical Plaquette to Maxel boundary operator ∂₂ : List Pixel -> Maxel.
public export
boundaryPlaquetteToMaxel : List Pixel -> Maxel
boundaryPlaquetteToMaxel loopEdges = multisetToMaxel (multisetBoundary2To1 loopEdges)

||| Pure Multiset Second Boundary Operator ∂² mapping a 2-cell closed loop down to 0-cells.
public export
multisetBoundaryChain2To0 : List Pixel -> Multiset BoxInt Unixel
multisetBoundaryChain2To0 loopEdges = multisetBoundary1To0 (multisetBoundary2To1 loopEdges)

||| Canonical Plaquette to Vexel second boundary operator ∂² : List Pixel -> Vexel.
public export
boundaryPlaquetteToVexel : List Pixel -> Vexel
boundaryPlaquetteToVexel loopEdges = multisetToVexel (multisetBoundaryChain2To0 loopEdges)

--------------------------------------------------------------------------------
-- 2. DISCRETE EXTERIOR CALCULUS (DEC) COBOUNDARY OPERATORS (d₀, d₁)
--------------------------------------------------------------------------------

||| Pure Multiset Coboundary operator d₀ : List Pixel -> Multiset BoxInt Unixel -> Multiset BoxInt Pixel
||| mapping a 0-cochain vertex potential Φ to a 1-cochain directed edge field (gradient).
||| For each directed edge [u -> v], (d₀ Φ)[u -> v] = Φ(v) - Φ(u).
public export
multisetCoboundary0To1 : List Pixel -> Multiset BoxInt Unixel -> Multiset BoxInt Pixel
multisetCoboundary0To1 [] _ = ZeroM
multisetCoboundary0To1 (p@(MkPixel u v) :: rest) phi =
  let phiU = lookupCountBox (MkUnixel u) phi
      phiV = lookupCountBox (MkUnixel v) phi
      diff = subBox phiV phiU
  in if unwrapBox diff == 0
        then multisetCoboundary0To1 rest phi
        else insertItemBox p diff (multisetCoboundary0To1 rest phi)

||| Pure Multiset Coboundary operator d₁ : List Pixel -> Multiset BoxInt Pixel -> BoxInt
||| evaluating the circulation (magnetic flux / 2-cochain) of an edge field A around a closed loop.
public export
multisetCoboundary1To2 : List Pixel -> Multiset BoxInt Pixel -> BoxInt
multisetCoboundary1To2 [] _ = intToBoxInt 0
multisetCoboundary1To2 (p :: rest) a =
  addBox (lookupCountBox p a) (multisetCoboundary1To2 rest a)

||| Evaluates discrete Poisson-Laplacian Δ(Φ) = ∂₁ (d₀ Φ) over a given edge lattice.
public export
multisetLaplacian0 : List Pixel -> Multiset BoxInt Unixel -> Multiset BoxInt Unixel
multisetLaplacian0 edges phi = multisetBoundary1To0 (multisetCoboundary0To1 edges phi)

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME HOMOLOGICAL NILPOTENCY & GAUGE INVARIANCE WITNESSES
--------------------------------------------------------------------------------

||| Zero-cost compile-time erased proof witness of Boundary Nilpotency: ∂₁ ∘ ∂₂ (loop) = ZeroM (∂² = 0).
public export
0 NilpotentBoundaryWitness : List Pixel -> Type
NilpotentBoundaryWitness loopEdges = multisetBoundaryChain2To0 loopEdges = ZeroM

||| Zero-cost compile-time erased proof witness of Coboundary Nilpotency (d² = 0 / Stokes' Theorem):
||| The circulation of a gradient field d₀(Φ) around a closed loop boundary vanishes identically.
public export
0 NilpotentCoboundaryWitness : List Pixel -> Multiset BoxInt Unixel -> Type
NilpotentCoboundaryWitness loopEdges phi =
  multisetCoboundary1To2 loopEdges (multisetCoboundary0To1 loopEdges phi) = intToBoxInt 0

||| A Discrete Cell Complex structure equipped with an erased compile-time nilpotency witness (∂² = 0).
public export
record HomologicalCellComplex (loopEdges : List Pixel) where
  constructor MkHomologicalCellComplex
  0 nilpotencyPrf : NilpotentBoundaryWitness loopEdges

||| Constructs a validated HomologicalCellComplex equipped with an erased 0 nilpotencyPrf witness.
public export
makeCellComplex : (loopEdges : List Pixel) ->
                  (0 prf : NilpotentBoundaryWitness loopEdges) ->
                  HomologicalCellComplex loopEdges
makeCellComplex loopEdges prf = MkHomologicalCellComplex prf

||| Static verification witness: constant potential yields ZeroM gradient field.
public export
auditConstantPotentialGradientZero : Bool
auditConstantPotentialGradientZero =
  let edges = [MkPixel 1 2, MkPixel 2 3, MkPixel 3 1]
      phi   = AddM (MkUnixel 1) (intToBoxInt 5)
              (AddM (MkUnixel 2) (intToBoxInt 5)
              (AddM (MkUnixel 3) (intToBoxInt 5) ZeroM))
  in multisetCoboundary0To1 edges phi == ZeroM
