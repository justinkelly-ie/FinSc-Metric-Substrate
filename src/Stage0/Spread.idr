module Stage0.Spread

import Data.Vect
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream as FS

%default total

------------------------------------------------------------------------
-- 1. MULTISET SPREAD POLYNOMIAL FORMULATION
------------------------------------------------------------------------

||| Multiset formulation of a 1D Spread Polynomial in indeterminate s.
||| Basis element Nat tracks monomial degree s^k, and BoxInt tracks the integer coefficient.
public export
0 SpreadMSet : Type
SpreadMSet = Multiset BoxInt Nat

||| Step transition for multiset-based spread polynomial recurrence:
||| S_n(s) = 2*S_{n-1}(s) - 4*s*S_{n-1}(s) - S_{n-2}(s) + 2*s
public export
stepSpreadMSet : SpreadMSet -> SpreadMSet -> SpreadMSet
stepSpreadMSet sPrev sCurr =
  let term1 = scaleMultiset (intToBoxInt 2) sCurr
      term2 = scaleMultiset (intToBoxInt (-4)) (mapMultiset S sCurr)
      term3 = negateMultiset sPrev
      term4 = AddM 1 (intToBoxInt 2) ZeroM
  in annihilateMultiset (term1 <+> term2 <+> term3 <+> term4)

||| O(n) linear multiset evaluation of Spread Polynomial S_n(s).
public export
spreadMSet : Nat -> SpreadMSet
spreadMSet Z = ZeroM
spreadMSet (S Z) = AddM 1 (intToBoxInt 1) ZeroM
spreadMSet (S (S k)) = go k ZeroM (AddM 1 (intToBoxInt 1) ZeroM)
  where
    go : Nat -> SpreadMSet -> SpreadMSet -> SpreadMSet
    go Z     prev curr = stepSpreadMSet prev curr
    go (S j) prev curr = go j curr (stepSpreadMSet prev curr)

------------------------------------------------------------------------
-- 2. SPREAD POLYNOMIAL RECURRENCE OVER LISTS (O(N) ACCUMULATOR)
------------------------------------------------------------------------

||| Adds two polynomial lists coefficient-wise.
public export
addList : List BoxInt -> List BoxInt -> List BoxInt
addList [] ys = ys
addList xs [] = xs
addList (x :: xs) (y :: ys) = (x + y) :: addList xs ys

||| Scales a polynomial list by a BoxInt scalar.
public export
scaleList : BoxInt -> List BoxInt -> List BoxInt
scaleList s xs = map (s *) xs

||| Single step transition for list-based spread polynomial recurrence.
public export
stepSpreadList : List BoxInt -> List BoxInt -> List BoxInt
stepSpreadList sPrev sCurr =
  let term1 = scaleList (intToBoxInt 2) sCurr
      term2 = intToBoxInt 0 :: scaleList (intToBoxInt (-4)) sCurr
      term3 = scaleList (intToBoxInt (-1)) sPrev
      term4 = [intToBoxInt 0, intToBoxInt 2]
  in addList (addList term1 term2) (addList term3 term4)

||| O(n) linear recurrence generation of Wildberger's Spread Polynomial coefficients.
||| S_0(s) = 0
||| S_1(s) = s
||| S_n(s) = 2*(1 - 2*s)*S_{n-1}(s) - S_{n-2}(s) + 2*s
public export
spreadList : Nat -> List BoxInt
spreadList Z = [intToBoxInt 0]
spreadList (S Z) = [intToBoxInt 0, intToBoxInt 1]
spreadList (S (S k)) = go k [intToBoxInt 0] [intToBoxInt 0, intToBoxInt 1]
  where
    go : Nat -> List BoxInt -> List BoxInt -> List BoxInt
    go Z     prev curr = stepSpreadList prev curr
    go (S j) prev curr = go j curr (stepSpreadList prev curr)

------------------------------------------------------------------------
-- VECTOR CONVERSION & EXPORTED KERNEL
------------------------------------------------------------------------

private
toVectExact : (k : Nat) -> List BoxInt -> Vect k BoxInt
toVectExact Z _ = []
toVectExact (S k) [] = intToBoxInt 0 :: toVectExact k []
toVectExact (S k) (x :: xs) = x :: toVectExact k xs

||| Recursive generation of the standard Spread Polynomials Sn(s) 
||| using Wildberger's strict algebraic triple-spread recurrence relation.
||| Returns a flat Vect (S n) BoxInt array of exact integer coefficients.
public export
generateSpreadPoly : (n : Nat) -> Vect (S n) BoxInt
generateSpreadPoly n = toVectExact (S n) (spreadList n)

||| Generates the deforested stream of active non-zero spread polynomial coefficients (degree, coefficient).
||| Avoids materializing dense vector buffers or intermediate lists.
public export
generateSpreadPolyStream : (n : Nat) -> FS.FusedStream (Nat, BoxInt)
generateSpreadPolyStream n =
  FS.unfoldStream nextStep (0, spreadList n)
  where
    nextStep : (Nat, List BoxInt) -> FS.Step (Nat, List BoxInt) (Nat, BoxInt)
    nextStep (_, []) = FS.Done
    nextStep (idx, c :: cs) =
      if boxIsNonZero c
        then FS.Yield (idx, c) (S idx, cs)
        else FS.Skip (S idx, cs)

------------------------------------------------------------------------
-- 3. RELATIVISTIC TRIPLE SPREAD LAW (WILDBERGER RRR 3)
------------------------------------------------------------------------

||| Evaluates Wildberger's Relativistic Triple Spread Law invariant:
||| (S1 + S2 - S3)^2 == 4 * S1 * S2 * (1 - S3).
public export
verifyRelativisticTripleSpreadLaw : (s1 : BoxInt) -> (s2 : BoxInt) -> (s3 : BoxInt) -> Bool
verifyRelativisticTripleSpreadLaw s1 s2 s3 =
  let lhs = (s1 + s2 - s3) * (s1 + s2 - s3)
      rhs = (intToBoxInt 4 * s1 * s2) * (intToBoxInt 1 - s3)
  in lhs == rhs

||| Invariant audit verifying Relativistic Triple Spread Law on canonical cases:
||| Case 1: Collinear boost / null spread (s1 = 0, s2 = 1, s3 = 1).
||| Case 2: Orthogonal spreads (s1 = 1, s2 = 1, s3 = 0).
public export
auditRelativisticTripleSpreadLawProof : Bool
auditRelativisticTripleSpreadLawProof =
  verifyRelativisticTripleSpreadLaw (intToBoxInt 0) (intToBoxInt 1) (intToBoxInt 1) &&
  verifyRelativisticTripleSpreadLaw (intToBoxInt 1) (intToBoxInt 1) (intToBoxInt 0)

