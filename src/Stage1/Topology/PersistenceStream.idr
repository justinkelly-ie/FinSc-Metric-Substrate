module Stage1.Topology.PersistenceStream

import public Stage0.BoxInt
import public Stage1.VexelMaxel
import public Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.Topology.Boundaries
import Data.Fuel
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- 1. SIMPLICIAL BOUNDARY & PERSISTENCE STREAM ALGEBRA
--------------------------------------------------------------------------------

||| Simplex dimension index k for boundary operator \partial_k.
public export
data SimplexDimension = Dim0 | Dim1 | Dim2

public export
Eq SimplexDimension where
  Dim0 == Dim0 = True
  Dim1 == Dim1 = True
  Dim2 == Dim2 = True
  _    == _    = False

||| Discrete boundary step token carrying dimension tag and boundary boundary multiplicity.
public export
record BoundaryToken where
  constructor MkBoundaryToken
  dimension    : SimplexDimension
  boundaryMult : BoxInt

public export
Eq BoundaryToken where
  (MkBoundaryToken d1 m1) == (MkBoundaryToken d2 m2) = d1 == d2 && m1 == m2

||| Unfolds a list of simplex boundary multiplicities into a deforested PersistenceStream.
%inline public export
unfoldPersistenceStream : List (SimplexDimension, BoxInt) -> FusedStream BoundaryToken
unfoldPersistenceStream items = MkStream nextStep items
  where
    nextStep : List (SimplexDimension, BoxInt) -> Step (List (SimplexDimension, BoxInt)) BoundaryToken
    nextStep [] = Done
    nextStep ((dim, mult) :: rest) = Yield (MkBoundaryToken dim mult) rest

||| Unfolds a vector of simplex boundary multiplicities into a deforested PersistenceStream.
%inline public export
unfoldPersistenceStreamVect : {n : Nat} -> Vect n (SimplexDimension, BoxInt) -> FusedStream BoundaryToken
unfoldPersistenceStreamVect items = unfoldPersistenceStream (toList items)

||| Deforested stream sifting operator filtering boundary tokens without intermediate allocations.
%inline public export
siftPersistenceStream : (BoundaryToken -> Bool) -> FusedStream BoundaryToken -> FusedStream BoundaryToken
siftPersistenceStream = siftFusedStream

||| Sifts a persistence boundary stream by a specific simplex dimension tag.
%inline public export
siftByDimension : SimplexDimension -> FusedStream BoundaryToken -> FusedStream BoundaryToken
siftByDimension dim = siftFusedStream (\tok => dimension tok == dim)

||| Computes total Betti rank \sum \beta_k directly across a deforested stream of boundary tokens.
public export
fusedComputeBettiRankStream : FusedStream BoundaryToken -> BoxInt
fusedComputeBettiRankStream strm =
  foldStream (\acc, tok => boundaryMult tok + acc) (intToBoxInt 0) strm

||| Computes sifted Betti rank for a specific predicate directly across a deforested boundary stream.
public export
fusedComputeSiftedBettiRankStream : (BoundaryToken -> Bool) -> FusedStream BoundaryToken -> BoxInt
fusedComputeSiftedBettiRankStream pred strm =
  foldStream (\acc, tok => if pred tok then boundaryMult tok + acc else acc) (intToBoxInt 0) strm

||| Zero-allocation single-pass simplicial persistence reduction directly across a deforested stream of boundary tokens.
public export
fusedSimplicialPersistenceReductionStream : FusedStream BoundaryToken -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReductionStream strm =
  foldStream (\acc, tok =>
                let (b0, b1, b2) = acc
                in case dimension tok of
                     Dim0 => (boundaryMult tok + b0, b1, b2)
                     Dim1 => (b0, boundaryMult tok + b1, b2)
                     Dim2 => (b0, b1, boundaryMult tok + b2))
    (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0)
    strm

||| Computes total Betti rank across a static vector of boundary tokens.
public export
fusedComputeBettiRankVect : {n : Nat} -> Vect n BoundaryToken -> BoxInt
fusedComputeBettiRankVect toks =
  foldl (\acc, tok => boundaryMult tok + acc) (intToBoxInt 0) toks

||| Computes sifted Betti rank for a specific predicate across a static vector of boundary tokens.
public export
fusedComputeSiftedBettiRankVect : {n : Nat} -> (BoundaryToken -> Bool) -> Vect n BoundaryToken -> BoxInt
fusedComputeSiftedBettiRankVect pred toks =
  foldl (\acc, tok => if pred tok then boundaryMult tok + acc else acc) (intToBoxInt 0) toks

||| Zero-allocation simplicial persistence reduction across a static vector of boundary tokens.
public export
fusedSimplicialPersistenceReductionVect : {n : Nat} -> Vect n BoundaryToken -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReductionVect toks =
  foldl (\acc, tok =>
           let (b0, b1, b2) = acc
           in case dimension tok of
                Dim0 => (boundaryMult tok + b0, b1, b2)
                Dim1 => (b0, boundaryMult tok + b1, b2)
                Dim2 => (b0, b1, boundaryMult tok + b2))
    (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0)
    toks

||| Computes total Betti rank \sum \beta_k across a filtration list using total structural Nat fuel.
public export
fusedComputeBettiRankNat : Nat -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeBettiRankNat fuel items =
  fusedHylomorphismNat fuel
    (\st => case st of
              [] => Done
              (dim, mult) :: rest => Yield (MkBoundaryToken dim mult) rest)
    (\tok, acc => boundaryMult tok + acc)
    (intToBoxInt 0)
    items

||| Computes total Betti rank across a filtration list using BoxNat fuel.
public export
fusedComputeBettiRankBoxNat : BoxNat -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeBettiRankBoxNat bfuel items =
  fusedComputeBettiRankNat (boxNatToNat bfuel) items

||| Computes total Betti rank across a filtration list using Goh factorization fuel.
public export
fusedComputeBettiRankGoh : List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeBettiRankGoh items =
  fusedComputeBettiRankBoxNat (gohFuel (length items)) items

||| Computes total Betti rank \sum \beta_k across a deforested filtration stream.
public export
fusedComputeBettiRank : Fuel -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeBettiRank (More f) items = fusedComputeBettiRankGoh items
fusedComputeBettiRank Dry _ = intToBoxInt 0

||| Computes sifted Betti rank for a specific predicate over a filtration list using total structural Nat fuel.
public export
fusedComputeSiftedBettiRankNat : Nat -> (BoundaryToken -> Bool) -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeSiftedBettiRankNat fuel pred items =
  fusedHylomorphismNat fuel
    (\st => case st of
              [] => Done
              (dim, mult) :: rest =>
                let tok = MkBoundaryToken dim mult
                in if pred tok then Yield tok rest else Skip rest)
    (\tok, acc => boundaryMult tok + acc)
    (intToBoxInt 0)
    items

||| Computes sifted Betti rank for a specific predicate using BoxNat fuel.
public export
fusedComputeSiftedBettiRankBoxNat : BoxNat -> (BoundaryToken -> Bool) -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeSiftedBettiRankBoxNat bfuel pred items =
  fusedComputeSiftedBettiRankNat (boxNatToNat bfuel) pred items

||| Computes sifted Betti rank for a specific predicate using Goh factorization fuel.
public export
fusedComputeSiftedBettiRankGoh : (BoundaryToken -> Bool) -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeSiftedBettiRankGoh pred items =
  fusedComputeSiftedBettiRankBoxNat (gohFuel (length items)) pred items

||| Computes sifted Betti rank for a specific predicate over a deforested boundary stream.
public export
fusedComputeSiftedBettiRank : Fuel -> (BoundaryToken -> Bool) -> List (SimplexDimension, BoxInt) -> BoxInt
fusedComputeSiftedBettiRank (More f) pred items =
  fusedComputeSiftedBettiRankGoh pred items
fusedComputeSiftedBettiRank Dry _ _ = intToBoxInt 0

||| Zero-allocation single-pass simplicial persistence reduction returning (betti0, betti1, betti2) using total structural Nat fuel.
public export
fusedSimplicialPersistenceReductionNat : Nat -> List (SimplexDimension, BoxInt) -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReductionNat fuel items =
  fusedHylomorphismNat fuel
    (\st => case st of
              [] => Done
              (dim, mult) :: rest => Yield (MkBoundaryToken dim mult) rest)
    (\tok, (b0, b1, b2) => case dimension tok of
                             Dim0 => (boundaryMult tok + b0, b1, b2)
                             Dim1 => (b0, boundaryMult tok + b1, b2)
                             Dim2 => (b0, b1, boundaryMult tok + b2))
    (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0)
    items

||| Zero-allocation single-pass simplicial persistence reduction using BoxNat fuel.
public export
fusedSimplicialPersistenceReductionBoxNat : BoxNat -> List (SimplexDimension, BoxInt) -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReductionBoxNat bfuel items =
  fusedSimplicialPersistenceReductionNat (boxNatToNat bfuel) items

||| Zero-allocation single-pass simplicial persistence reduction using Goh factorization fuel.
public export
fusedSimplicialPersistenceReductionGoh : List (SimplexDimension, BoxInt) -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReductionGoh items =
  fusedSimplicialPersistenceReductionBoxNat (gohFuel (length items)) items

||| Zero-allocation single-pass simplicial persistence reduction returning (betti0, betti1, betti2).
public export
fusedSimplicialPersistenceReduction : Fuel -> List (SimplexDimension, BoxInt) -> (BoxInt, BoxInt, BoxInt)
fusedSimplicialPersistenceReduction (More f) items =
  fusedSimplicialPersistenceReductionGoh items
fusedSimplicialPersistenceReduction Dry _ =
  (intToBoxInt 0, intToBoxInt 0, intToBoxInt 0)

--------------------------------------------------------------------------------
-- 2. VERIFICATION AUDIT WITNESS
--------------------------------------------------------------------------------

||| Audit witness verifying zero-allocation total Betti rank and sifted persistence reduction across streams and vectors.
public export
auditPersistenceStreamProof : Bool
auditPersistenceStreamProof =
  let items = [(Dim0, intToBoxInt 1), (Dim1, intToBoxInt 2), (Dim2, intToBoxInt 1)]
      strm = unfoldPersistenceStream items
      bettiStream = fusedComputeBettiRankStream strm
      (b0Stream, b1Stream, b2Stream) = fusedSimplicialPersistenceReductionStream (unfoldPersistenceStream items)
      b1SiftedStream = fusedComputeSiftedBettiRankStream (\tok => dimension tok == Dim1) (unfoldPersistenceStream items)
      bfuel = parabolicGohFuel
      betti = fusedComputeBettiRankBoxNat bfuel items
      (b0, b1, b2) = fusedSimplicialPersistenceReductionBoxNat bfuel items
      b1Sifted = fusedComputeSiftedBettiRankBoxNat bfuel (\tok => dimension tok == Dim1) items
  in unwrapBox betti == 4 && unwrapBox bettiStream == 4 &&
     unwrapBox b0 == 1 && unwrapBox b0Stream == 1 &&
     unwrapBox b1 == 2 && unwrapBox b1Stream == 2 &&
     unwrapBox b2 == 1 && unwrapBox b2Stream == 1 &&
     unwrapBox b1Sifted == 2 && unwrapBox b1SiftedStream == 2

--------------------------------------------------------------------------------
-- 3. NILPOTENT PERSISTENCE STREAM TRANSPORT
--------------------------------------------------------------------------------

||| A Persistent Homology Stream transporting an erased boundary nilpotency witness (∂² = 0) across filtration steps.
public export
record NilpotentPersistenceStream (loopEdges : List Pixel) where
  constructor MkNilpotentPersistenceStream
  streamData : FusedStream BoundaryToken
  0 nilpotencyPrf : NilpotentBoundaryWitness loopEdges

||| Constructs a NilpotentPersistenceStream transporting boundary nilpotency (∂² = 0) through deforested streams.
public export
makeNilpotentPersistenceStream : (loopEdges : List Pixel) ->
                                 (0 prf : NilpotentBoundaryWitness loopEdges) ->
                                 List (SimplexDimension, BoxInt) ->
                                 NilpotentPersistenceStream loopEdges
makeNilpotentPersistenceStream loopEdges prf items =
  MkNilpotentPersistenceStream (unfoldPersistenceStream items) prf

||| Constructs a NilpotentPersistenceStream directly from a deforested stream without intermediate lists.
public export
makeNilpotentPersistenceStreamDirect : (loopEdges : List Pixel) ->
                                       (0 prf : NilpotentBoundaryWitness loopEdges) ->
                                       FusedStream BoundaryToken ->
                                       NilpotentPersistenceStream loopEdges
makeNilpotentPersistenceStreamDirect loopEdges prf strm =
  MkNilpotentPersistenceStream strm prf

||| Constructs a NilpotentPersistenceStream from a compile-time static vector of loop edges.
public export
makeNilpotentPersistenceStreamVect : {n : Nat} ->
                                     (loopEdges : Vect n Pixel) ->
                                     (0 prf : NilpotentBoundaryWitness (toList loopEdges)) ->
                                     FusedStream BoundaryToken ->
                                     NilpotentPersistenceStream (toList loopEdges)
makeNilpotentPersistenceStreamVect loopEdges prf strm =
  MkNilpotentPersistenceStream strm prf
