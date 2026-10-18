module Stage1.SpatialStencil

import Data.Vect
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MultisetDuality
import Stage1.TypeTheory.Staging
import Stage1.VexelMaxel
import Stage1.MultisetTree

%default total

--------------------------------------------------------------------------------
-- 1. CONTEXTUAL NEIGHBORHOOD GRID
--------------------------------------------------------------------------------

||| Represents a focused point in discrete space with local neighbor context.
public export
record GridContext a where
  constructor Context
  leftNeighbor  : a
  focusedCell   : a
  rightNeighbor : a

public export
implementation Functor GridContext where
  map f (Context l c r) = Context (f l) (f c) (f r)

--------------------------------------------------------------------------------
-- 2. SPATIAL STENCIL INTERFACE & INSTANCE
--------------------------------------------------------------------------------

||| The defining interface for local spatial neighborhood execution on discrete grids.
||| Replaces abstract category-theoretic comonads with concrete discrete spatial stencils.
public export
interface Functor w => SpatialStencil (0 w : Type -> Type) where
  ||| Extracts the exact discrete token at the current focal coordinate point
  focalToken : w a -> a
  
  ||| Refocuses every cell as the origin of its own local neighborhood window
  neighborhoodShift : w a -> w (w a)
  
  ||| Maps a local neighborhood update rule across the entire universe lattice
  applyStencil : (w a -> b) -> w a -> w b

||| 2LTT Staged Stencil Evaluation: Pre-evaluates local neighborhood convolution at Stage 1.
%inline public export
stagedApplyStencil : SpatialStencil w => Lift (w a -> b) -> Lift (w a) -> w b
stagedApplyStencil qRule qGrid = applyStencil (splice qRule) (splice qGrid)

||| QTT 0 Erased Proof Witness: Staged Stencil Invariant
public export
0 prfStagedApplyStencil : SpatialStencil w => (rule : w a -> b) -> (grid : w a) ->
                          stagedApplyStencil (quote rule) (quote grid) = applyStencil rule grid
prfStagedApplyStencil _ _ = Refl

||| Duality-to-stencil transition: A Multiset Duality (Push ⇋ Pull) generates a local round-trip operator.
public export
dualityToStencil : MultisetDuality l r -> l a -> l a
dualityToStencil dual x = pushToken @{dual} (pullToken @{dual} x)


public export
implementation SpatialStencil GridContext where
  focalToken (Context _ c _) = c
  
  neighborhoodShift (Context l c r) = 
    Context (Context l l c) (Context l c r) (Context c r r)

  applyStencil f = map f . neighborhoodShift

||| Linearly extracts the exact value at the current focal coordinate point
public export
extractLinear : (1 ctx : GridContext a) -> a
extractLinear (Context _ c _) = c

--------------------------------------------------------------------------------
-- 3. PARAMETERIZED N-DIMENSIONAL STENCIL CONTEXT
--------------------------------------------------------------------------------

||| Represents an N-dimensional spatial stencil with explicit focal center and neighbor vectors
public export
record GridStencil (n : Nat) (a : Type) where
  constructor MkStencil
  leftNeighbors  : Vect n a
  focusCell      : a
  rightNeighbors : Vect n a

public export
implementation Functor (GridStencil n) where
  map f (MkStencil ls c rs) = MkStencil (map f ls) (f c) (map f rs)

||| QTT linear extraction of the focal cell from an N-dimensional stencil context
public export
extractStencilLinear : {n : Nat} -> (1 stencil : GridStencil n a) -> a
extractStencilLinear (MkStencil _ c _) = c

--------------------------------------------------------------------------------
-- 4. BOUNDED LOCAL DISSIPATION RULE & INVARIANCE PROOFS
--------------------------------------------------------------------------------

||| Static compiler verification proof validating that our stencil
||| preserves spatial structure and contains zero data-shifting leakage.
public export
0 verifyComonadIdentity : (grid : GridContext a) -> 
                          applyStencil Stage1.SpatialStencil.focalToken grid = grid
verifyComonadIdentity (Context l c r) = Refl

||| Static compiler verification proof for QTT linear N-dimensional stencil focal extraction.
public export
0 verifyStencilComonadIdentity : {n : Nat} -> 
                                (stencil : GridStencil n a) -> 
                                extractStencilLinear stencil = focusCell stencil
verifyStencilComonadIdentity (MkStencil ls c rs) = Refl

--------------------------------------------------------------------------------
-- 5. STAGED BOUNDARY CONDITIONS & 2LTT STENCIL CONVOLUTIONS
--------------------------------------------------------------------------------

||| Formalized Boundary Conditions for Staged Stencil Convolutions.
public export
data StagedBoundary : Type where
  PeriodicBoundary  : StagedBoundary
  DirichletBoundary : BoxInt -> StagedBoundary

||| Looks up a 1D neighbor cell given a boundary condition and coordinate offset.
public export
boundaryLookup1D : {n : Nat} -> StagedBoundary -> Vect n BoxInt -> Integer -> BoxInt
boundaryLookup1D PeriodicBoundary xs idx =
  case n of
    Z => intToBoxInt 0
    (S k) =>
      let nInt = cast {to = Integer} (S k)
          modIdx = ((idx `mod` nInt) + nInt) `mod` nInt
          natIdx = integerToNat modIdx
      in case natToFin natIdx (S k) of
           Just finIdx => index finIdx xs
           Nothing => intToBoxInt 0
boundaryLookup1D (DirichletBoundary defaultVal) xs idx =
  if idx < 0 || idx >= cast {to = Integer} n
     then defaultVal
     else case natToFin (integerToNat idx) n of
            Just finIdx => index finIdx xs
            Nothing => defaultVal

||| Unrolls a 1D 3-point stencil Laplacian (-1, 2, -1) across a VexelN n at Stage 1.
public export
stagedLaplacian1D : {n : Nat} -> StagedBoundary -> VexelN n -> Code (VexelN n)
stagedLaplacian1D bc (MkVexelN comps) =
  quote (MkVexelN (generateComps 0 comps))
  where
    generateComps : Integer -> Vect m BoxInt -> Vect m BoxInt
    generateComps idx [] = []
    generateComps idx (c :: rest) =
      let lVal = boundaryLookup1D bc comps (idx - 1)
          rVal = boundaryLookup1D bc comps (idx + 1)
          lap = subBox (mulBox (intToBoxInt 2) c) (addBox lVal rVal)
      in lap :: generateComps (idx + 1) rest

||| Audit invariant for staged 1D stencil convolution.
public export
auditStagedStencil1D : Bool
auditStagedStencil1D =
  let v = mkVexel4 (intToBoxInt 10) (intToBoxInt 20) (intToBoxInt 30) (intToBoxInt 40)
      res = splice (stagedLaplacian1D PeriodicBoundary v)
  in (index 0 res.components == intToBoxInt (-40)) &&
     (index 1 res.components == intToBoxInt 0) &&
     (index 2 res.components == intToBoxInt 0) &&
     (index 3 res.components == intToBoxInt 40)

--------------------------------------------------------------------------------
-- 6. 2D STAGED BOUNDARIES & 5-POINT LAPLACIAN CONVOLUTIONS
--------------------------------------------------------------------------------

||| 2D Staged Boundary condition bundling horizontal (X) and vertical (Y) boundaries.
public export
record StagedBoundary2D where
  constructor MkBoundary2D
  boundaryX : StagedBoundary
  boundaryY : StagedBoundary

||| Looks up a 2D neighbor in a linearized (m x n) grid given coordinates (row, col) and 2D boundaries.
public export
boundaryLookup2D : {m, n : Nat} -> StagedBoundary2D -> Vect (m * n) BoxInt -> Integer -> Integer -> BoxInt
boundaryLookup2D {m} {n} (MkBoundary2D bx by) grid r c =
  let mInt = cast {to = Integer} m
      nInt = cast {to = Integer} n
  in if mInt <= 0 || nInt <= 0
       then intToBoxInt 0
       else
         let rValid = r >= 0 && r < mInt
             cValid = c >= 0 && c < nInt
         in if rValid && cValid
              then let linIdx = r * nInt + c
                   in case natToFin (integerToNat linIdx) (m * n) of
                        Just finIdx => index finIdx grid
                        Nothing => intToBoxInt 0
              else
                let rEff = case by of
                             PeriodicBoundary => ((r `mod` mInt) + mInt) `mod` mInt
                             DirichletBoundary _ => -1
                    cEff = case bx of
                             PeriodicBoundary => ((c `mod` nInt) + nInt) `mod` nInt
                             DirichletBoundary _ => -1
                in if rEff >= 0 && cEff >= 0
                     then let linIdx = rEff * nInt + cEff
                          in case natToFin (integerToNat linIdx) (m * n) of
                               Just finIdx => index finIdx grid
                               Nothing => intToBoxInt 0
                     else case (bx, by) of
                            (DirichletBoundary dVal, _) => dVal
                            (_, DirichletBoundary dVal) => dVal
                            _ => intToBoxInt 0

||| Unrolls a 2D 5-point discrete Laplacian (4*c - l - r - u - d) on a linearized (m x n) VexelN (m * n).
public export
stagedLaplacian2D : {m, n : Nat} -> StagedBoundary2D -> VexelN (m * n) -> Code (VexelN (m * n))
stagedLaplacian2D {m} {n} bnd (MkVexelN comps) =
  quote (MkVexelN (generateComps 0 comps))
  where
    generateComps : Integer -> Vect k BoxInt -> Vect k BoxInt
    generateComps _ [] = []
    generateComps linIdx (c :: rest) =
      let nInt = cast {to = Integer} n
          r = linIdx `div` (if nInt == 0 then 1 else nInt)
          col = linIdx `mod` (if nInt == 0 then 1 else nInt)
          leftVal  = boundaryLookup2D bnd comps r (col - 1)
          rightVal = boundaryLookup2D bnd comps r (col + 1)
          upVal    = boundaryLookup2D bnd comps (r - 1) col
          downVal  = boundaryLookup2D bnd comps (r + 1) col
          neighborSum = addBox (addBox leftVal rightVal) (addBox upVal downVal)
          lap = subBox (mulBox (intToBoxInt 4) c) neighborSum
      in lap :: generateComps (linIdx + 1) rest

||| Audit invariant for staged 2D 5-point stencil Laplacian with exact Noether flux conservation (sum = 0).
public export
auditStagedStencil2D : Bool
auditStagedStencil2D =
  let v = mkVexel4 (intToBoxInt 10) (intToBoxInt 20) (intToBoxInt 30) (intToBoxInt 40)
      bnd = MkBoundary2D PeriodicBoundary PeriodicBoundary
      res = splice (stagedLaplacian2D {m=2} {n=2} bnd v)
      c0 = index 0 res.components
      c1 = index 1 res.components
      c2 = index 2 res.components
      c3 = index 3 res.components
      totalFlux = addBox (addBox c0 c1) (addBox c2 c3)
  in (c0 == intToBoxInt (-60)) &&
     (c1 == intToBoxInt (-20)) &&
     (c2 == intToBoxInt 20) &&
     (c3 == intToBoxInt 60) &&
     (totalFlux == intToBoxInt 0)

--------------------------------------------------------------------------------
-- 7. FAST MULTISETTREE SPATIAL STENCILS & 2LTT ACTIVE SUPPORT CONVOLUTION
--------------------------------------------------------------------------------

||| Evaluates 1D 3-point Laplacian stencil (-1, 2, -1) over the active multiset support of a tree:
||| lap(x) = 2 * c(x) - c(x-1) - c(x+1).
||| Lookups and insertions run in O(log N) time with zero allocation for vacuum nodes.
public export
laplacianTree1D : BoxMultisetTree BoxInt -> BoxMultisetTree BoxInt
laplacianTree1D tree =
  let candidates = foldBoxTreeR (\x, _, acc => the (List BoxInt) ((x - 1) :: x :: (x + 1) :: acc))
                                (the (List BoxInt) [])
                                tree
  in foldl updatePoint BoxLeaf candidates
  where
    updatePoint : BoxMultisetTree BoxInt -> BoxInt -> BoxMultisetTree BoxInt
    updatePoint acc x =
      let cVal = lookupBoxTree x tree
          lVal = lookupBoxTree (x - 1) tree
          rVal = lookupBoxTree (x + 1) tree
          lap = (intToBoxInt 2 * cVal) - (lVal + rVal)
      in if boxIsZero lap
           then acc
           else setBoxTree x lap acc

||| 2LTT Staged 1D MultisetTree Stencil Convolution.
public export
stagedLaplacianTree1D : Lift (BoxMultisetTree BoxInt) -> Code (BoxMultisetTree BoxInt)
stagedLaplacianTree1D qTree = quote (laplacianTree1D (splice qTree))

||| Evaluates 2D 5-point discrete Laplacian stencil (4*c - l - r - u - d) over 2D BoxMultisetTree.
public export
laplacianTree2D : BoxMultisetTree (BoxInt, BoxInt) -> BoxMultisetTree (BoxInt, BoxInt)
laplacianTree2D tree =
  let candidates = foldBoxTreeR (\(x, y), _, acc =>
                                  the (List (BoxInt, BoxInt))
                                    ((x, y) :: (x - 1, y) :: (x + 1, y) :: (x, y - 1) :: (x, y + 1) :: acc))
                                (the (List (BoxInt, BoxInt)) [])
                                tree
  in foldl updatePoint BoxLeaf candidates
  where
    updatePoint : BoxMultisetTree (BoxInt, BoxInt) -> (BoxInt, BoxInt) -> BoxMultisetTree (BoxInt, BoxInt)
    updatePoint acc pt@(x, y) =
      let cVal = lookupBoxTree pt tree
          lVal = lookupBoxTree (x - 1, y) tree
          rVal = lookupBoxTree (x + 1, y) tree
          uVal = lookupBoxTree (x, y + 1) tree
          dVal = lookupBoxTree (x, y - 1) tree
          lap = (intToBoxInt 4 * cVal) - (lVal + rVal + uVal + dVal)
      in if boxIsZero lap
           then acc
           else setBoxTree pt lap acc

||| Audit invariant for MultisetTree spatial stencils:
||| Tests that a unit excitation at x = 0 produces exact flux: lap(0) = 2, lap(-1) = -1, lap(1) = -1.
||| Net discrete flux sum = 2 - 1 - 1 = 0 (exact flux conservation).
public export
auditTreeStencilProof : Bool
auditTreeStencilProof =
  let t0 : BoxMultisetTree BoxInt = setBoxTree 0 (intToBoxInt 1) BoxLeaf
      res = laplacianTree1D t0
      c0  = lookupBoxTree 0 res
      cm1 = lookupBoxTree (-1) res
      c1  = lookupBoxTree 1 res
      c2  = lookupBoxTree 2 res
      netFlux = c0 + cm1 + c1
  in c0 == intToBoxInt 2 && cm1 == intToBoxInt (-1) && c1 == intToBoxInt (-1) &&
     c2 == intToBoxInt 0 && netFlux == intToBoxInt 0
