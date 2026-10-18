module Stage1.SpatialStencil

import Data.Vect
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MultisetDuality
import Stage1.TypeTheory.Staging
import Stage1.VexelMaxel

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


