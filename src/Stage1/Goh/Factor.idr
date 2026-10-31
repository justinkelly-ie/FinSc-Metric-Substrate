module Stage1.Goh.Factor

import public Stage0.PrimeMultiset
import public Stage1.TypeTheory.Smoothness
import Stage0.BoxInt
import Stage0.StreamPolynumber
import Stage0.OnSeq.FusedStream as FS
import Stage1.UnixelFraction
import Stage1.FourGeometries
import Stage1.Basis.Coordinate
import Stage1.VexelStream as VS
import Stage1.MultisetTree
import Data.Vect
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVIST GOH PRIME SPECTRUM & POLYNOMIAL DEGREE
------------------------------------------------------------------------

||| Determines the exact algebraic degree of the cyclotomic factor Phi_p(x).
public export
gohDegree : (p : Nat) -> Nat
gohDegree 2  = 1
gohDegree 3  = 2
gohDegree 5  = 4
gohDegree 7  = 6
gohDegree 11 = 10
gohDegree 13 = 12
gohDegree (S n) = n
gohDegree Z  = Z

||| Auxiliary UnixelFraction constructor for exact integer scalars.
private
fracInt : Integer -> UnixelFraction
fracInt n = mkUnixelFraction (intToBoxInt n) 1

------------------------------------------------------------------------
-- 2. DEPENDENTLY TYPED GOH PRIME FACTOR RECORD
------------------------------------------------------------------------

||| Dependently typed Goh Prime Factor parameterized by its exact prime number p.
||| Statically guarantees that the coefficient vector length matches the cyclotomic degree S (gohDegree p).
public export
record GohFactor (p : Nat) where
  constructor MkGohFactor
  0 primeWitness   : GohPrime p
  coefficients     : Vect (S (gohDegree p)) UnixelFraction
  geometrySector   : FundamentalGeometry
  vacuumQuadrance  : BoxInt
  domainRole       : String

public export
{p : Nat} -> Show (GohFactor p) where
  show (MkGohFactor _ _ geom q role) =
    "GohFactor(" ++ show p ++ " | " ++ show geom ++ " | Q=" ++ show q ++ " | " ++ role ++ ")"

||| Projects a dependently typed GohFactor into the canonical CosmicDimension Sigma-pair.
public export
0 gohFactorDimension : GohFactor p -> CosmicDimension
gohFactorDimension (MkGohFactor prf _ _ _ _) = (p ** gohPrimeWitness prf)

------------------------------------------------------------------------
-- 3. CANONICAL CONSTRUCTIVE FACTOR INSTANCES ACROSS THE 4 GEOMETRIES
-- (Cigler & Herbig, Ars Combinatoria 2026)
------------------------------------------------------------------------

||| Canonical dependently typed GohFactor constructor indexed by physical prime p.
||| Canonical static Constant Applicative Forms (CAFs) allocated once at program initialization (Rule 04 §8).
public export
rawFactor2 : GohFactor 2
rawFactor2 =
  MkGohFactor
    Prime2
    [fracInt 4, fracInt (-1)]
    HyperbolicGeom
    (intToBoxInt 4)
    "Dyadic DE ROM & Toric Parity"

public export
rawFactor3 : GohFactor 3
rawFactor3 =
  MkGohFactor
    Prime3
    [fracInt 9, fracInt (-6), fracInt 1]
    EllipticGeom
    (intToBoxInt 9)
    "3D Manifest Spatial Grid & Triplet"

public export
rawFactor5 : GohFactor 5
rawFactor5 =
  MkGohFactor
    Prime5
    [fracInt 25, fracInt (-50), fracInt 35, fracInt (-10), fracInt 1]
    ParabolicGeom
    (intToBoxInt 25)
    "Blue Spread Hypotenuse & Pentose"

public export
rawFactor7 : GohFactor 7
rawFactor7 =
  MkGohFactor
    Prime7
    [fracInt 49, fracInt (-98), fracInt 70, fracInt (-28), fracInt 7, fracInt (-1), fracInt 1]
    SubstrateGeom
    (intToBoxInt 49)
    "Substrate Causal Arrow & Primorial 210"

public export
rawFactor11 : GohFactor 11
rawFactor11 =
  MkGohFactor
    Prime11
    (replicate 11 (fracInt 1))
    ParabolicGeom
    (intToBoxInt 55)
    "Phase Space Boundary & DM T_10 Residue"

public export
rawFactor13 : GohFactor 13
rawFactor13 =
  MkGohFactor
    Prime13
    (replicate 13 (fracInt 1))
    EllipticGeom
    (intToBoxInt 39)
    "13-Smooth Gate-Purity & Observer Epoch"

||| Canonical dependently typed GohFactor constructor indexed by physical prime p.
||| Statically verifies primality at compile time via auto-implicit GohPrime witness.
||| Projects pre-allocated static CAFs with zero runtime heap allocation (Rule 04 §8).
public export
gohFactor : (p : Nat) -> {auto 0 prf : GohPrime p} -> GohFactor p
gohFactor 2 {prf = Prime2} = rawFactor2
gohFactor 3 {prf = Prime3} = rawFactor3
gohFactor 5 {prf = Prime5} = rawFactor5
gohFactor 7 {prf = Prime7} = rawFactor7
gohFactor 11 {prf = Prime11} = rawFactor11
gohFactor 13 {prf = Prime13} = rawFactor13

||| Canonical association mapping each fundamental geometry to its primary constructivist Goh factor (Rule 03, Item 1 & 7):
||| - Elliptic: Manifest Spatial Dimension L = 3 (Factor 3, Blue)
||| - Hyperbolic: Dyadic ROM Storage Unit p = 2 (Factor 2, Red)
||| - Parabolic: Blue Spread Hypotenuse & Pentose p = 5 (Factor 5, Green)
||| - Substrate: Primorial Causal Arrow p = 7 (Factor 7, Master)
public export
geometryPrimaryFactor : FundamentalGeometry -> (p : Nat ** GohFactor p)
geometryPrimaryFactor EllipticGeom   = (3 ** gohFactor 3)
geometryPrimaryFactor HyperbolicGeom = (2 ** gohFactor 2)
geometryPrimaryFactor ParabolicGeom  = (5 ** gohFactor 5)
geometryPrimaryFactor SubstrateGeom  = (7 ** gohFactor 7)

------------------------------------------------------------------------
-- 3B. CONSTRUCTIVE COMPOSITE GOH COUPLINGS (35, 55, 39)
------------------------------------------------------------------------

||| Constructive Composite Goh Coupling Record:
||| Bundles two constituent Goh primes and their composite product dimension.
public export
record GohCompositeCoupling (p : Nat) (q : Nat) (prod : Nat) where
  constructor MkGohCompositeCoupling
  constituentP      : GohFactor p
  constituentQ      : GohFactor q
  0 productWitness  : GohPrimeProduct p q prod
  couplingName      : String

||| Composite Coupling 35 (Parabolic-Substrate Ground Coupling):
||| p = 5 (Parabolic Blue Spread) * q = 7 (Substrate Causal Arrow) = 35.
||| Coupled with (2 * 3 = 6) yields the Primorial 210 Ground State: 6 * 35 = 210.
public export
coupling35ParabolicSubstrate : GohCompositeCoupling 5 7 35
coupling35ParabolicSubstrate =
  MkGohCompositeCoupling (gohFactor 5) (gohFactor 7) gohPrimeProduct5_7 "Parabolic-Substrate Ground Coupling"

||| Composite Coupling 55 (Parabolic Dark Matter Capacity & Triangular Residue):
||| p = 5 (Parabolic) * q = 11 (Residue Boundary) = 55.
||| Identically matches the 10th triangular number T_10 = (10 * 11) / 2 = 55.
public export
coupling55ParabolicDarkMatter : GohCompositeCoupling 5 11 55
coupling55ParabolicDarkMatter =
  MkGohCompositeCoupling (gohFactor 5) (gohFactor 11) gohPrimeProduct5_11 "Parabolic Dark Matter Capacity (T_10)"

||| Composite Coupling 39 (Observer Epoch Dual-Branch Emergence):
||| p = 3 (Manifest 3D Grid) * q = 13 (Cosmic Smooth Horizon) = 39.
||| Matches scale step n = 39 at observer epoch k = 38.
public export
coupling39ObserverEpoch : GohCompositeCoupling 3 13 39
coupling39ObserverEpoch =
  MkGohCompositeCoupling (gohFactor 3) (gohFactor 13) gohPrimeProduct3_13 "Observer Epoch Dual-Branch Emergence"

||| Invariant witness: Parabolic-Substrate coupling 35 with (2 * 3 = 6) saturates the Primorial 210 ground state.
public export
0 prfCoupling35SaturatesPrimorial210 : (the Nat (6 * 35)) = 210
prfCoupling35SaturatesPrimorial210 = Refl

||| Invariant witness: Parabolic Dark Matter capacity 55 satisfies the triangular relation 2 * 55 = 10 * 11.
public export
0 prfCoupling55TriangularResidue : (the Nat (2 * 55)) = (the Nat (10 * 11))
prfCoupling55TriangularResidue = Refl

||| Invariant witness: Observer Epoch composite scale 39 matches successor of k = 38.
public export
0 prfCoupling39ObserverEpochSuccessor : S 38 = 39
prfCoupling39ObserverEpochSuccessor = Refl


------------------------------------------------------------------------
-- 4. POLYNOMIAL HORNER EVALUATION & DEFINITIONAL THEOREMS
------------------------------------------------------------------------

||| Pure integer Horner polynomial evaluation over integer coefficient vector.
public export
evalHornerInteger : List Integer -> Integer -> Integer
evalHornerInteger [] _ = 0
evalHornerInteger (c :: cs) x = c + x * (evalHornerInteger cs x)

||| Evaluates factor 2: Psi_2(x) = 4 - x.
public export
evalFactor2 : Integer -> Integer
evalFactor2 x = 4 - x

||| Evaluates factor 3: Psi_3(x) = 9 - 6x + x^2.
public export
evalFactor3 : Integer -> Integer
evalFactor3 x = 9 - 6 * x + x * x

||| Invariant witness: Psi_2 fixed point at x = 2 is 2.
public export
0 prfFactor2FixedPoint : evalFactor2 2 = 2
prfFactor2FixedPoint = Refl

||| Invariant witness: Psi_3 root at manifest spatial dimension x = 3 is 0.
public export
0 prfFactor3RootAt3 : evalFactor3 3 = 0
prfFactor3RootAt3 = Refl

||| Invariant witness: Factor 2 and 3 vacuum quadrance sum matches Factor 5 vacuum root:
||| Q(2) + Q(3) = 4 + 9 = 13 (13-smooth prime).
public export
0 prfVacuumQuadranceSumIs13 : addBox (vacuumQuadrance (gohFactor 2)) (vacuumQuadrance (gohFactor 3)) = intToBoxInt 13
prfVacuumQuadranceSumIs13 = Refl

||| Invariant witness: Dyadic Factor 2 vacuum quadrance Q(2) = 4 embodies the 2 + 2 factorisation:
||| Q(2) = 2^2 = 2 + 2 = 4.
public export
0 prfFactor2QuadranceIs4 : vacuumQuadrance (gohFactor 2) = intToBoxInt 4
prfFactor2QuadranceIs4 = Refl

------------------------------------------------------------------------
-- 5. GOH FACTOR TO STREAMPOLYNUMBER & COMPANION MULTISETTREE BRIDGE
------------------------------------------------------------------------

||| Extracts the exact integer BoxInt numerator vector from a GohFactor.
public export
gohFactorCoeffsBoxInt : {p : Nat} -> GohFactor p -> Vect (S (gohDegree p)) BoxInt
gohFactorCoeffsBoxInt f = map num f.coefficients

||| Takes the lower d coefficients from a Vect (S d) a without constraint solving.
public export
takeLower : (d : Nat) -> Vect (S d) a -> Vect d a
takeLower Z (_ :: _) = []
takeLower (S k) (x :: xs) = x :: takeLower k xs

||| Derives the feedback coefficient vector for a monic companion matrix from a GohFactor.
||| For Factor 2: returns [4] (root 4).
||| For Factor p (p >= 3): returns the negated lower coefficients [-a_0, -a_1, ...].
public export
gohFactorFeedbackCoeffs : (p : Nat) -> GohFactor p -> Vect (gohDegree p) BoxInt
gohFactorFeedbackCoeffs 2 _ = [intToBoxInt 4]
gohFactorFeedbackCoeffs p f =
  map (\c => subBox (intToBoxInt 0) c.num) (takeLower (gohDegree p) f.coefficients)

||| Streams a Vect paired with its natural index in O(1) auxiliary registers.
public export
streamVectWithIndex : {k : Nat} -> Nat -> Vect k a -> FS.FusedStream (Nat, a)
streamVectWithIndex {k} base v =
  FS.unfoldStream step (base, (k ** v))
  where
    step : (Nat, (n : Nat ** Vect n a)) -> FS.Step (Nat, (n : Nat ** Vect n a)) (Nat, a)
    step (_, (Z ** [])) = FS.Done
    step (i, (S n ** y :: ys)) = FS.Yield (i, y) (S i, (n ** ys))

||| Converts an irreducible GohFactor directly into a deforested StreamPolynumber.
||| Emits strictly non-zero terms in O(1) auxiliary registers without intermediate lists.
public export
gohFactorToStreamPoly : {p : Nat} -> GohFactor p -> StreamPolynumber
gohFactorToStreamPoly f =
  FS.filterMapStream (\(deg, frac) =>
    if boxIsNonZero frac.num then Just (deg, frac.num) else Nothing)
    (streamVectWithIndex 0 f.coefficients)

||| Canonical static AVL MultisetTree of active 1D degrees for Factor 2 (degrees 0, 1).
public export
factor2PolySupportTree : MultisetTree Nat
factor2PolySupportTree = Node 2 Leaf 0 1 (Node 1 Leaf 1 1 Leaf)

||| Canonical static AVL MultisetTree of active 1D degrees for Factor 3 (degrees 0, 1, 2).
public export
factor3PolySupportTree : MultisetTree Nat
factor3PolySupportTree =
  Node 2 (Node 1 Leaf 0 1 Leaf) 1 1 (Node 1 Leaf 2 1 Leaf)

||| Canonical static AVL MultisetTree of active 1D degrees for Factor 5 (degrees 0, 1, 2, 3, 4).
public export
factor5PolySupportTree : MultisetTree Nat
factor5PolySupportTree =
  Node 3 (Node 2 (Node 1 Leaf 0 1 Leaf) 1 1 Leaf)
         2 1
         (Node 2 (Node 1 Leaf 3 1 Leaf) 4 1 Leaf)

||| Canonical static AVL MultisetTree of active 1D degrees for Factor 7 (degrees 0, 1, 2, 3, 4, 5, 6).
public export
factor7PolySupportTree : MultisetTree Nat
factor7PolySupportTree =
  Node 3 (Node 2 (Node 1 Leaf 0 1 Leaf) 1 1 (Node 1 Leaf 2 1 Leaf))
         3 1
         (Node 2 (Node 1 Leaf 4 1 Leaf) 5 1 (Node 1 Leaf 6 1 Leaf))

||| O(log N) AVL MultisetTree of active 1D degrees for an irreducible GohFactor.
public export
gohFactorPolySupportTree : {p : Nat} -> GohFactor p -> MultisetTree Nat
gohFactorPolySupportTree {p = 2} _ = factor2PolySupportTree
gohFactorPolySupportTree {p = 3} _ = factor3PolySupportTree
gohFactorPolySupportTree {p = 5} _ = factor5PolySupportTree
gohFactorPolySupportTree {p = 7} _ = factor7PolySupportTree
gohFactorPolySupportTree _ = Leaf

||| Deforested stream of active 1D degrees unfolded from the MultisetTree in O(log N) stack frames.
public export
gohFactorPolySupportStream : {p : Nat} -> GohFactor p -> FS.FusedStream Nat
gohFactorPolySupportStream f =
  FS.mapStream fst (streamMultisetTreeDirect (gohFactorPolySupportTree f))

||| Canonical static AVL MultisetTree of active 2D coordinate support pixels for Factor 2 (dim 1).
public export
factor2SupportTree : MultisetTree Pixel
factor2SupportTree = Node 1 Leaf (mkPixel 1 1) 1 Leaf

||| Canonical static AVL MultisetTree of active 2D coordinate support pixels for Factor 3 (dim 2).
public export
factor3SupportTree : MultisetTree Pixel
factor3SupportTree =
  Node 2 (Node 1 Leaf (mkPixel 1 2) 1 Leaf)
         (mkPixel 2 1) 1
         (Node 1 Leaf (mkPixel 2 2) 1 Leaf)

||| Canonical static AVL MultisetTree of active 2D coordinate support pixels for Factor 5 (dim 4).
public export
factor5SupportTree : MultisetTree Pixel
factor5SupportTree =
  let leftSub = Node 2 (Node 1 Leaf (mkPixel 1 4) 1 Leaf)
                       (mkPixel 2 1) 1
                       (Node 1 Leaf (mkPixel 2 4) 1 Leaf)
      rightSub = Node 2 (Node 1 Leaf (mkPixel 3 4) 1 Leaf)
                        (mkPixel 4 3) 1
                        (Node 1 Leaf (mkPixel 4 4) 1 Leaf)
  in Node 3 leftSub (mkPixel 3 2) 1 rightSub

||| Canonical static AVL MultisetTree of active 2D coordinate support pixels for Factor 7 (dim 6).
||| Contains 5 subdiagonal entries and 6 column feedback entries (total 11 active pixels).
public export
factor7SupportTree : MultisetTree Pixel
factor7SupportTree =
  let leftL  = Node 2 (Node 1 Leaf (mkPixel 1 6) 1 Leaf) (mkPixel 2 1) 1 Leaf
      leftR  = Node 2 (Node 1 Leaf (mkPixel 3 2) 1 Leaf) (mkPixel 3 6) 1 Leaf
      left   = Node 3 leftL (mkPixel 2 6) 1 leftR
      rightL = Node 2 (Node 1 Leaf (mkPixel 4 6) 1 Leaf) (mkPixel 5 4) 1 Leaf
      rightR = Node 2 (Node 1 Leaf (mkPixel 6 5) 1 Leaf) (mkPixel 6 6) 1 Leaf
      right  = Node 3 rightL (mkPixel 5 6) 1 rightR
  in Node 4 left (mkPixel 4 3) 1 right

||| O(log N) AVL MultisetTree representation of the active 2D coordinate support for a GohFactor.
public export
gohFactorSupportTree : {p : Nat} -> GohFactor p -> MultisetTree Pixel
gohFactorSupportTree {p = 2} _ = factor2SupportTree
gohFactorSupportTree {p = 3} _ = factor3SupportTree
gohFactorSupportTree {p = 5} _ = factor5SupportTree
gohFactorSupportTree {p = 7} _ = factor7SupportTree
gohFactorSupportTree _ = Leaf

||| Streams the active 2D coordinate support pixels of an irreducible GohFactor in O(1) registers
||| directly from its balanced MultisetTree without intermediate list allocation.
public export
gohFactorSupportStream : {p : Nat} -> GohFactor p -> FS.FusedStream Pixel
gohFactorSupportStream f =
  FS.mapStream fst (streamMultisetTreeDirect (gohFactorSupportTree f))

||| Discrete 2D companion support graph cardinality for a Goh prime.
public export
gohFactorSupportSize : (p : Nat) -> Nat
gohFactorSupportSize 2 = 1
gohFactorSupportSize 3 = 3
gohFactorSupportSize 5 = 7
gohFactorSupportSize 7 = 11
gohFactorSupportSize _ = 0

||| Discrete 1D polynomial term support cardinality for a Goh prime.
public export
gohFactorPolySupportSize : (p : Nat) -> Nat
gohFactorPolySupportSize 2 = 2
gohFactorPolySupportSize 3 = 3
gohFactorPolySupportSize 5 = 5
gohFactorPolySupportSize 7 = 7
gohFactorPolySupportSize _ = 0

------------------------------------------------------------------------
-- 5B. FACTOR ADDITION & COMPOSITE DIRECT SUM ALGEBRA (RULE 03 & 04)
------------------------------------------------------------------------

||| Shifts coordinate pixels by an offset (d, d) along the diagonal for block-diagonal direct sum:
public export
shiftPixelByDim : Nat -> Pixel -> Pixel
shiftPixelByDim offset px =
  mkPixel (pixelRow px + offset) (pixelCol px + offset)

||| Shifts an entire MultisetTree of pixels by a diagonal dimension offset:
public export
shiftSupportTree : (dimOffset : Nat) -> MultisetTree Pixel -> MultisetTree Pixel
shiftSupportTree Z tree = tree
shiftSupportTree offset Leaf = Leaf
shiftSupportTree offset (Node h l x c r) =
  Node h (shiftSupportTree offset l) (shiftPixelByDim offset x) c (shiftSupportTree offset r)

||| Orthogonal direct sum of two GohFactor companion support trees (dim = d1 + d2):
||| Shifts the second tree's coordinates by gohDegree p, modeling block-diagonal companion matrices.
public export
gohFactorDirectSumTree : {p, q : Nat} -> GohFactor p -> GohFactor q -> MultisetTree Pixel
gohFactorDirectSumTree {p} fp fq =
  gohFactorSupportTree fp <+> shiftSupportTree (gohDegree p) (gohFactorSupportTree fq)

||| Companion support tree of a composite coupling (e.g. coupling39ObserverEpoch for 3 x 13):
public export
gohCompositeSupportTree : {p, q : Nat} -> GohCompositeCoupling p q prod -> MultisetTree Pixel
gohCompositeSupportTree {p} {q} (MkGohCompositeCoupling fp fq _ _) =
  gohFactorDirectSumTree fp fq

||| Generates the subdiagonal shift entries directly in multiset tree space.
public export
makeSubDiagTree : (count : Nat) -> (idx : Nat) -> Maxel -> Maxel
makeSubDiagTree Z _ acc = acc
makeSubDiagTree (S n) idx acc =
  makeSubDiagTree n (S idx) (singletonCell (mkPixel (idx + 1) idx) (intToBoxInt 1) <+> acc)

||| Generates the column feedback entries directly in multiset tree space.
public export
makeColEntriesTree : (dim : Nat) -> (idx : Nat) -> Vect k BoxInt -> Maxel -> Maxel
makeColEntriesTree _ _ [] acc = acc
makeColEntriesTree dim idx (c :: cs) acc =
  let next = if boxIsNonZero c then singletonCell (mkPixel idx dim) c <+> acc else acc
  in makeColEntriesTree dim (S idx) cs next

||| Constructs an N-dimensional companion Maxel matrix from feedback coefficients.
public export
companionMaxelFromFeedback : (dim : Nat) -> Vect dim BoxInt -> Maxel
companionMaxelFromFeedback Z [] = neutral
companionMaxelFromFeedback 1 [c0] =
  if boxIsZero c0 then neutral else singletonCell (mkPixel 1 1) c0
companionMaxelFromFeedback (S (S k)) coeffs =
  let dim = S (S k)
      subDiag = makeSubDiagTree (S k) 1 neutral
  in makeColEntriesTree dim 1 coeffs subDiag

||| Constructs the canonical 2D companion Maxel directly from an irreducible GohFactor.
public export
gohFactorToCompanionMaxel : {p : Nat} -> GohFactor p -> Maxel
gohFactorToCompanionMaxel {p} f =
  companionMaxelFromFeedback (gohDegree p) (gohFactorFeedbackCoeffs p f)

||| Constructs a dimension-indexed companion SquareMaxel directly from feedback coefficients.
public export
companionSquareMaxelFromFeedback : (dim : Nat) -> Vect dim BoxInt -> SquareMaxel dim
companionSquareMaxelFromFeedback dim coeffs =
  maxelToSquareMaxel dim (companionMaxelFromFeedback dim coeffs)

||| Constructs a dimension-indexed companion SquareMaxel from an irreducible GohFactor.
public export
gohFactorToCompanionSquareMaxel : {p : Nat} -> GohFactor p -> SquareMaxel (gohDegree p)
gohFactorToCompanionSquareMaxel {p} f =
  companionSquareMaxelFromFeedback (gohDegree p) (gohFactorFeedbackCoeffs p f)

------------------------------------------------------------------------
-- 6. COMPILE-TIME SUPPORT COMMUTATION PROOFS VIA MULTISETTREE (RULE 01)
------------------------------------------------------------------------

||| Formal compile-time witness: Factor 2 companion support tree has 1 active pixel ([1, 1]).
public export
0 prfFactor2TreeSupportSize : treeElementCount (gohFactorSupportTree (gohFactor 2)) = 1
prfFactor2TreeSupportSize = Refl

||| Formal compile-time witness: Factor 3 companion support tree has 3 active pixels ([2, 1], [1, 2], [2, 2]).
public export
0 prfFactor3TreeSupportSize : treeElementCount (gohFactorSupportTree (gohFactor 3)) = 3
prfFactor3TreeSupportSize = Refl

||| Formal compile-time witness: Factor 5 companion support tree has 7 active pixels (3 subdiagonal + 4 feedback).
public export
0 prfFactor5TreeSupportSize : treeElementCount (gohFactorSupportTree (gohFactor 5)) = 7
prfFactor5TreeSupportSize = Refl

||| Formal compile-time witness: Factor 2 1D polynomial support tree has 2 terms (degrees 0, 1).
public export
0 prfFactor2PolySupportSize : treeElementCount (gohFactorPolySupportTree (gohFactor 2)) = 2
prfFactor2PolySupportSize = Refl

||| Formal compile-time witness: Factor 3 1D polynomial support tree has 3 terms (degrees 0, 1, 2).
public export
0 prfFactor3PolySupportSize : treeElementCount (gohFactorPolySupportTree (gohFactor 3)) = 3
prfFactor3PolySupportSize = Refl

||| Formal compile-time witness: Factor 5 1D polynomial support tree has 5 terms (degrees 0, 1, 2, 3, 4).
public export
0 prfFactor5PolySupportSize : treeElementCount (gohFactorPolySupportTree (gohFactor 5)) = 5
prfFactor5PolySupportSize = Refl

||| Formal compile-time witness: Factor 7 companion support tree has 11 active pixels.
public export
0 prfFactor7TreeSupportSize : treeElementCount (gohFactorSupportTree (gohFactor 7)) = 11
prfFactor7TreeSupportSize = Refl

||| Formal compile-time witness: Factor 7 1D polynomial support tree has 7 terms (degrees 0..6).
public export
0 prfFactor7PolySupportSize : treeElementCount (gohFactorPolySupportTree (gohFactor 7)) = 7
prfFactor7PolySupportSize = Refl

||| Formal compile-time witness: Shifting Factor 2 companion support by 1 yields 1 active pixel ([2, 2]).
public export
0 prfShiftFactor2SupportSize :
  treeElementCount (shiftSupportTree 1 (gohFactorSupportTree (gohFactor 2))) = 1
prfShiftFactor2SupportSize = Refl

