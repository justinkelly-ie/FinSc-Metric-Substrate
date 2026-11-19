module Stage1.Cosmology.UniverseBridge

import Data.DPair
import Data.Fin
import Data.Nat
import Data.Vect
import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage0.OnSeq.FusedStream
import public Stage0.UniverseState
import public Stage1.Views

%default total

------------------------------------------------------------------------
-- 1. DIRECT AVL -> VECT PROJECTION (ZERO INTERMEDIATE LIST ALLOCATION)
------------------------------------------------------------------------

public export
data VectFillState : Nat -> Type where
  MkFillState : (nextIdx : Nat) ->
                (vec : Vect n BoxInt) ->
                (overflow : BoxInt) ->
                VectFillState n

public export
insertAtNat : {n : Nat} -> Nat -> BoxInt -> Vect n BoxInt -> BoxInt -> (Vect n BoxInt, BoxInt)
insertAtNat {n} idx w vec ov =
  case natToFin idx n of
    Nothing     => (vec, addBox ov w)
    Just finIdx => (replaceAt finIdx w vec, ov)

||| Projects up to `n` ordered multiplicities directly from a `HereditaryMSet BoxInt`
||| AVL tree into `(Vect n BoxInt, overflowMass)` in true ascending key order without
||| intermediate `List` allocation, preserving mass conservation via `overflow`.
public export
projectHMSetDirect : (n : Nat) -> HereditaryMSet BoxInt -> (Vect n BoxInt, BoxInt)
projectHMSetDirect n (MkHMSet box) =
  let initVec = replicate n (intToBoxInt 0)
      MkFillState _ finalVec ov =
        foldBox
          (\_, w, (MkFillState idx accVec accOv) =>
            let (nextVec, nextOv) = insertAtNat idx w accVec accOv
            in MkFillState (S idx) nextVec nextOv)
          (MkFillState 0 initVec (intToBoxInt 0))
          box
  in (finalVec, ov)

public export
accumulateAtNat : {n : Nat} -> Nat -> BoxInt -> Vect n BoxInt -> BoxInt -> (Vect n BoxInt, BoxInt)
accumulateAtNat {n} idx w vec ov =
  case natToFin idx n of
    Nothing     => (vec, addBox ov w)
    Just finIdx => (replaceAt finIdx (addBox (index finIdx vec) w) vec, ov)

||| Projects a scalar Laurent `HereditaryMSet BoxInt` into `(Vect n BoxInt, overflowMass)`
||| keyed by Laurent degree magnitude `|e|` (accumulating collisions at slot `|e|` and
||| routing `|e| >= n` or nested terms into `overflowMass` for exact mass conservation).
public export
projectLaurentIndexed : (n : Nat) -> HereditaryMSet BoxInt -> (Vect n BoxInt, BoxInt)
projectLaurentIndexed n (MkHMSet box) =
  let initVec = replicate n (intToBoxInt 0)
  in foldBox
       (\k, w, (accVec, accOv) =>
         case classifyLaurentKey unwrapBox k of
           ExponentKey e   => accumulateAtNat (integerToNat (abs e)) w accVec accOv
           NestedTermKey _ => (accVec, addBox accOv w))
       (initVec, intToBoxInt 0)
       box

||| Backward-compatible `Vect n BoxInt` projection (first `n` weights, zero-padded).
public export
projectHMSetToVect : (n : Nat) -> HereditaryMSet BoxInt -> Vect n BoxInt
projectHMSetToVect n m = fst (projectHMSetDirect n m)

------------------------------------------------------------------------
-- 2. POOL CAPACITY RECOGNIZER (`Dec` PER `recognition-rule.md`)
------------------------------------------------------------------------

||| Predicate asserting a `HereditaryMSet BoxInt` support fits within `cap` slots.
public export
data FitsPoolCap : (cap : Nat) -> HereditaryMSet BoxInt -> Type where
  MkFitsPoolCap : {0 b : Stage0.Box.Box BoxInt (HereditaryMSet BoxInt)} ->
                  (prf : LTE (boxNodeCount b) cap) ->
                  FitsPoolCap cap (MkHMSet b)

||| Constructive `Dec` recognizer verifying zero-overflow fit for pool size `cap`.
public export
recognizeFitsPool : (cap : Nat) -> (m : HereditaryMSet BoxInt) -> Dec (FitsPoolCap cap m)
recognizeFitsPool cap (MkHMSet b) =
  case isLTE (boxNodeCount b) cap of
    Yes prf   => Yes (MkFitsPoolCap prf)
    No contra => No (\(MkFitsPoolCap p) => contra p)

------------------------------------------------------------------------
-- 3. DUAL-CHANNEL & LINEAR `UniverseContainer` LOWERING BRIDGE
------------------------------------------------------------------------

||| Full projection outcome including the Primorial 210 `ObserverUniverseState`
||| and any positive/negative overflow mass if active support exceeds `27` or `55`.
public export
record UniverseProjectionReport where
  constructor MkUniverseProjectionReport
  observerState : ObserverUniverseState
  posOverflow   : BoxInt
  negOverflow   : BoxInt
  deOverflow    : BoxInt

||| Lowers a dual-channel `PureMultiset` (`M_+` active matter, `M_-` frozen relic)
||| into the Primorial 210 `ObserverUniverseState` (`27` VM, `128` DE, `55` DM):
||| - `vmVec` (`27`) receives ascending-degree positive matter `M_+` weights (+ `posOverflow`).
||| - `deVec` (`128`) receives signed dark-energy residue `deSeed` (+ `deOverflow`), preserving
|||   signed balance `sum deVec + deOverflow == sumHMSet deSeed`.
||| - `dmVec` (`55`) receives ascending-degree antimatter/binding `M_-` weights (+ `negOverflow`).
public export
lowerToObserverReport : (deSeed : HereditaryMSet BoxInt) ->
                        HereditaryMSet BoxInt ->
                        UniverseProjectionReport
lowerToObserverReport deSeed cosmosMSet =
  let (MkDualChannels posM negM) = splitChannels cosmosMSet
      (vmVec, posOv) = projectHMSetDirect 27 posM
      (deVec, deOv)  = projectHMSetDirect 128 deSeed
      (dmVec, negOv) = projectHMSetDirect 55 negM
  in MkUniverseProjectionReport (MkUniverseState vmVec deVec dmVec) posOv negOv deOv

||| Lowers a dual-channel `PureMultiset` into `ObserverUniverseState`.
public export
lowerToObserverUniverse : (deSeed : HereditaryMSet BoxInt) ->
                          HereditaryMSet BoxInt ->
                          ObserverUniverseState
lowerToObserverUniverse deSeed cosmosMSet =
  (lowerToObserverReport deSeed cosmosMSet).observerState

||| Linear (`QTT 1`) observation bridge over `UniverseContainer`:
||| Extracts a `210`-slot `ObserverUniverseState` snapshot + conservation report
||| while threading the single root `UniverseContainer` strictly once.
public export
observeUniverseLinear : (1 uc : UniverseContainer) ->
                        (deSeed : HereditaryMSet BoxInt) ->
                        LinearStatePair UniverseContainer UniverseProjectionReport
observeUniverseLinear uc deSeed =
  observeUniversePatch uc (lowerToObserverReport deSeed)

||| Linear (`QTT 1`) step + observation bridge over `UniverseContainer`:
||| Evolves the root `PureMultiset`, keeps the single `UniverseContainer` linear,
||| and emits both the user outcome and the `ObserverUniverseState` snapshot.
public export
stepAndObserveUniverse : (1 uc : UniverseContainer) ->
                         (HereditaryMSet BoxInt -> (HereditaryMSet BoxInt, out)) ->
                         (deSeed : HereditaryMSet BoxInt) ->
                         LinearStatePair UniverseContainer (UniverseProjectionReport, out)
stepAndObserveUniverse uc stepFn deSeed =
  case stepUniverseContainer uc stepFn of
    MkLStatePair nextUc out =>
      case observeUniverseLinear nextUc deSeed of
        MkLStatePair finalUc proj => MkLStatePair finalUc (proj, out)
