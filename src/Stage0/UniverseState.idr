module Stage0.UniverseState

import Data.Vect
import Stage0.BoxInt
import Stage0.HereditaryMSet
import Stage0.OnSeq.FusedStream

%default total

------------------------------------------------------------------------
-- 1. UNIVERSE STATE (PURE STAGE 0 RUNTIME DISCRETE DATA PAYLOAD)
------------------------------------------------------------------------

||| Bounded 3-pool discrete multiset state representation.
||| Dimensions are tracked relationally through dependent parameters.
||| All data slots store exact BoxInt discrete particle/quadrance tokens.
public export
record UniverseState (vmSize : Nat) (deSize : Nat) (dmSize : Nat) where
  constructor MkUniverseState
  visibleMatter : Vect vmSize BoxInt -- Active spatial field lattice
  darkEnergy    : Vect deSize BoxInt -- Background ROM capacity
  darkMatter    : Vect dmSize BoxInt -- Historical error/residue ledger

public export
{vm, de, dm : Nat} -> Eq (UniverseState vm de dm) where
  (MkUniverseState vm1 de1 dm1) == (MkUniverseState vm2 de2 dm2) =
    vm1 == vm2 && de1 == de2 && dm1 == dm2

public export
{vm, de, dm : Nat} -> Show (UniverseState vm de dm) where
  show (MkUniverseState _ _ _) =
    "UniverseState(vm=" ++ show vm ++ ", de=" ++ show de ++ ", dm=" ++ show dm ++ ")"

||| Extracts the residue log as a read-only reference.
public export
dmLog : UniverseState vm de dm -> Vect dm BoxInt
dmLog (MkUniverseState _ _ dmData) = dmData

||| Calculates total active state energy across all memory pools.
public export
totalStateCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
totalStateCapacity {vm} {de} {dm} _ = vm + de + dm

||| Dimension projection for visible matter pool size.
public export
visibleMatterCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
visibleMatterCapacity _ = vm

||| Dimension projection for dark energy pool size.
public export
darkEnergyCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
darkEnergyCapacity _ = de

||| Dimension projection for dark matter residue pool size.
public export
darkMatterCapacity : {vm, de, dm : Nat} -> UniverseState vm de dm -> Nat
darkMatterCapacity _ = dm

||| QTT 0 erased proof witness verifying definitional total capacity of UniverseState.
public export
0 prfUniverseCapacityTotal : {vm, de, dm : Nat} -> (st : UniverseState vm de dm) -> totalStateCapacity st = vm + de + dm
prfUniverseCapacityTotal _ = Refl

||| Canonical Observer Universe State type: 27 VM, 128 DE, 55 DM (Primorial 210).
public export
ObserverUniverseState : Type
ObserverUniverseState = UniverseState 27 128 55

||| Compile-time proof witness auditing ObserverUniverseState total capacity matches Primorial 210.
public export
0 prfObserverUniverseCapacity210 : (st : ObserverUniverseState) -> totalStateCapacity st = 210
prfObserverUniverseCapacity210 _ = Refl

||| Canonical Genesis Vacuum Universe State type: 0 VM, 128 DE, 0 DM (Background 128).
public export
GenesisVacuumUniverseState : Type
GenesisVacuumUniverseState = UniverseState 0 128 0

||| Seed constructor for a vacuum state with 0 values across memory pools.
public export
seedCosmicVacuum : (vm : Nat) -> (de : Nat) -> (dm : Nat) -> UniverseState vm de dm
seedCosmicVacuum vm de dm = MkUniverseState (replicate vm (intToBoxInt 0)) (replicate de (intToBoxInt 0)) (replicate dm (intToBoxInt 0))

||| Linear vector combination appending two Vect states.
public export
linearVectCombine : Vect n a -> Vect m a -> Vect (n + m) a
linearVectCombine [] ys = ys
linearVectCombine (x :: xs) ys = x :: linearVectCombine xs ys

||| Strict QTT linear multiplicity state transition.
public export
stepUniverseLinear : {vm, de, dm, k : Nat} ->
                     (1 state : UniverseState vm de dm) ->
                     (newMatter : Vect k BoxInt) ->
                     UniverseState (vm + k) de (S dm)
stepUniverseLinear (MkUniverseState vm de dm) newMatter =
  let updatedVM = linearVectCombine vm newMatter
      updatedDM = (intToBoxInt 1) :: dm
  in MkUniverseState updatedVM de updatedDM

------------------------------------------------------------------------
-- 2. QTT `1` SINGLE LINEAR UNIVERSE CONTAINER (`UniverseContainer`)
------------------------------------------------------------------------

||| Outermost root universe wrapper enforcing single-owner `QTT 1` consumption
||| over `HereditaryMSet BoxInt` (`PureMultiset`). Intentionally omits `Ord`
||| (and `Eq`) so the root cosmos cannot be cloned, dropped, or embedded as a
||| key inside another multiset container while internal patches remain freely
||| observable via `Stage1.Views` inside scoped transitions.
public export
data UniverseContainer : Type where
  MkUniverseContainer : (rootMSet : HereditaryMSet BoxInt) -> UniverseContainer

||| Seeds the linear universe strictly from the empty vacuum `[]` (`emptyHMSet`).
public export
emptyUniverseContainer : UniverseContainer
emptyUniverseContainer = MkUniverseContainer emptyHMSet

||| Consumes a linear `UniverseContainer` explicitly to extract its final `PureMultiset` relic.
public export
consumeUniverseToMSet : (1 uc : UniverseContainer) -> HereditaryMSet BoxInt
consumeUniverseToMSet (MkUniverseContainer rootMSet) = rootMSet

||| Executes a read-only unrestricted observer query over the internal patch of a
||| linearly threaded `UniverseContainer` without cloning or dropping the root.
public export
observeUniversePatch : (1 uc : UniverseContainer) ->
                       (HereditaryMSet BoxInt -> out) ->
                       LinearStatePair UniverseContainer out
observeUniversePatch (MkUniverseContainer rootMSet) viewFn =
  MkLStatePair (MkUniverseContainer rootMSet) (viewFn rootMSet)

||| Evolves the linear `UniverseContainer` through a scoped transformation and
||| returns an unrestricted observable alongside the updated `1`-quantity root.
public export
stepUniverseContainer : (1 uc : UniverseContainer) ->
                        (HereditaryMSet BoxInt -> (HereditaryMSet BoxInt, out)) ->
                        LinearStatePair UniverseContainer out
stepUniverseContainer (MkUniverseContainer rootMSet) stepFn =
  let (nextRoot, out) = stepFn rootMSet
  in MkLStatePair (MkUniverseContainer nextRoot) out
