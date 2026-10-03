module Stage1.SpatialStencil

import Data.Vect
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MultisetDuality
import Stage1.TypeTheory.Staging
import Stage1.TypeTheory.TwoLevel

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
