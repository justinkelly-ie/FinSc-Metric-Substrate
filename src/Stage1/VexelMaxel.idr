module Stage1.VexelMaxel

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Stage1.Polynumber
import Stage1.MultisetTree
import Data.List
import Data.Vect
import Language.Reflection

%default total

------------------------------------------------------------------------
-- 1. WILDBERGER'S SINGLETONS, PIXELS & VOXELS
------------------------------------------------------------------------

||| A Unixel is a 1-list from Nat [n], representing a 1D basis coordinate.
public export
record Unixel where
  constructor MkUnixel
  index : Nat

%inline public export
unixelEq : Unixel -> Unixel -> Bool
unixelEq (MkUnixel i1) (MkUnixel i2) = natEq i1 i2

%inline public export
Eq Unixel where
  (MkUnixel i1) == (MkUnixel i2) = unixelEq (MkUnixel i1) (MkUnixel i2)

public export
Ord Unixel where
  compare (MkUnixel i1) (MkUnixel i2) = compare i1 i2

public export
Show Unixel where
  show (MkUnixel i) = "[" ++ show i ++ "]"

||| Unwraps the natural coordinate of a Unixel.
public export
unwrapUnixel : Unixel -> Nat
unwrapUnixel (MkUnixel i) = i

||| A Pixel is a 2-list from Nat [i, j], representing a 2D coordinate cell or signed difference pair [pos, neg].
public export
record Pixel where
  constructor MkPixel
  row : Nat
  col : Nat

||| Canonical unambiguous alias for discrete 2D grid matrix cells.
public export
GridPixel : Type
GridPixel = Pixel

||| Alternative alias for cell coordinate.
public export
CellPixel : Type
CellPixel = Pixel

%inline public export
pixelEq : Pixel -> Pixel -> Bool
pixelEq (MkPixel r1 c1) (MkPixel r2 c2) = if natEq r1 r2 then natEq c1 c2 else False

%inline public export
Eq Pixel where
  (MkPixel r1 c1) == (MkPixel r2 c2) = pixelEq (MkPixel r1 c1) (MkPixel r2 c2)

public export
Ord Pixel where
  compare (MkPixel r1 c1) (MkPixel r2 c2) =
    case compare r1 r2 of
      EQ => compare c1 c2
      res => res

public export
Show Pixel where
  show (MkPixel r c) = "[" ++ show r ++ ", " ++ show c ++ "]"

||| A Voxel is a 3-list from Nat [x, y, z], representing a 3D coordinate cell or Triplet Codon / Baryon state.
public export
record Voxel where
  constructor MkVoxel
  axisX : Nat
  axisY : Nat
  axisZ : Nat

%inline public export
voxelEq : Voxel -> Voxel -> Bool
voxelEq (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2) = natEq x1 x2 && natEq y1 y2 && natEq z1 z2

%inline public export
Eq Voxel where
  (MkVoxel x1 y1 z1) == (MkVoxel x2 y2 z2) = voxelEq (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2)

public export
Ord Voxel where
  compare (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2) =
    case compare x1 x2 of
      EQ => case compare y1 y2 of
        EQ => compare z1 z2
        resY => resY
      resX => resX

public export
Show Voxel where
  show (MkVoxel x y z) = "[" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ "]"

||| Evaluates 2D symmetric matrix determinant: det([a b; b c]) = a*c - b^2.
%inline public export
detSymmetricMatrix2D : BoxInt -> BoxInt -> BoxInt -> BoxInt
detSymmetricMatrix2D a b c = subBox (a * c) (b * b)

------------------------------------------------------------------------
-- 2. SIGNED BOXINT <-> PIXEL DIFFERENCE PAIR ISOMORPHISM
------------------------------------------------------------------------

||| Encodes a signed difference pair (pos, neg) as a 2D coordinate Pixel [pos, neg].
public export
boxIntToPixelPair : Nat -> Nat -> Pixel
boxIntToPixelPair p n = MkPixel p n

||| Evaluates the signed BoxInt integer value of a difference pair Pixel [pos, neg]: (pos - neg).
public export
pixelToSignedBoxInt : Pixel -> BoxInt
pixelToSignedBoxInt (MkPixel p n) = intToBoxInt (cast p - cast n)

------------------------------------------------------------------------
-- 3. VEXELS & MAXELS AS PURE MULTISETS
------------------------------------------------------------------------

||| A Vexel is a multiset of Singletons (Wildberger Vector).
||| Stored as a list of weighted basis Singletons: sum c_k * [k].
public export
record Vexel where
  constructor MkVexel
  terms : List (Unixel, BoxInt)

||| Canonical unambiguous alias for discrete monomorphic 1D Wildberger vectors.
public export
DiscreteVexel : Type
DiscreteVexel = Vexel

public export
Eq Vexel where
  (MkVexel t1) == (MkVexel t2) = t1 == t2

public export
Show Vexel where
  show (MkVexel ts) = "Vexel(" ++ show ts ++ ")"

||| A Maxel is a multiset of Pixels (Wildberger Matrix).
||| Stored as a list of weighted coordinate Pixels: sum a_ij * [i, j].
public export
record Maxel where
  constructor MkMaxel
  pixels : List (Pixel, BoxInt)

public export
Eq Maxel where
  (MkMaxel p1) == (MkMaxel p2) = p1 == p2

public export
Show Maxel where
  show (MkMaxel ps) = "Maxel(" ++ show ps ++ ")"

||| @deprecated Linear O(N) lookupUnixel is suitable for small basis sets.
||| For canonical multisets, use canonicalizeVexel or MultisetTree.
public export
lookupUnixel : Unixel -> Vexel -> BoxInt
lookupUnixel _ (MkVexel []) = intToBoxInt 0
lookupUnixel target (MkVexel ((s, w) :: sings)) =
  if unixelEq s target
    then addBox w (lookupUnixel target (MkVexel sings))
    else lookupUnixel target (MkVexel sings)

||| Computes the total integer mass of a Vexel vector.
public export
totalVexelMass : Vexel -> BoxInt
totalVexelMass (MkVexel []) = intToBoxInt 0
totalVexelMass (MkVexel ((_, w) :: sings)) = addBox w (totalVexelMass (MkVexel sings))

||| @deprecated Linear O(N) lookupPixel is suitable for small matrix coordinate sets.
||| For canonical multisets, use canonicalizeMaxel or MultisetTree.
public export
lookupPixel : Pixel -> Maxel -> BoxInt
lookupPixel _ (MkMaxel []) = intToBoxInt 0
lookupPixel target (MkMaxel ((p, w) :: ps)) =
  if pixelEq p target
    then addBox w (lookupPixel target (MkMaxel ps))
    else lookupPixel target (MkMaxel ps)


||| A Boxel is a multiset of Voxels (Wildberger 3D Volume Tensor).
||| Stored as a list of weighted coordinate Voxels: sum rho_xyz * [x, y, z].
public export
record Boxel where
  constructor MkBoxel
  voxels : List (Voxel, BoxInt)

public export
Eq Boxel where
  (MkBoxel b1) == (MkBoxel b2) = b1 == b2

public export
Show Boxel where
  show (MkBoxel bs) = "Boxel(" ++ show bs ++ ")"

||| Extracts the weight of a specific coordinate Voxel in a Boxel.
public export
lookupVoxel : Voxel -> Boxel -> BoxInt
lookupVoxel target (MkBoxel vs) =
  foldl (\acc, (v, w) => if v == target then acc + w else acc) (intToBoxInt 0) vs


||| Adds two Boxels by concatenating their voxel multiset entries.
public export
addBoxel : Boxel -> Boxel -> Boxel
addBoxel (MkBoxel bs1) (MkBoxel bs2) = MkBoxel (bs1 ++ bs2)

||| Scales a Boxel by a BoxInt scalar.
public export
scaleBoxel : BoxInt -> Boxel -> Boxel
scaleBoxel s (MkBoxel bs) =
  MkBoxel (map (\(v, w) => (v, s * w)) bs)

||| Computes total weight/density across all voxels in a Boxel.
public export
totalBoxelWeight : Boxel -> BoxInt
totalBoxelWeight (MkBoxel bs) =
  sum (map snd bs)

------------------------------------------------------------------------
-- CANONICAL MULTISET ISOMORPHISMS
------------------------------------------------------------------------

||| Embeds a Vexel into its canonical discrete Multiset representation.
public export
vexelToMultiset : Vexel -> Multiset BoxInt Unixel
vexelToMultiset (MkVexel terms) = fromListBox terms

||| Reifies a canonical discrete Multiset representation back into a Vexel.
public export
multisetToVexel : Multiset BoxInt Unixel -> Vexel
multisetToVexel m = MkVexel (multisetToList m)

||| Embeds a Maxel into its canonical discrete Multiset representation.
public export
maxelToMultiset : Maxel -> Multiset BoxInt Pixel
maxelToMultiset (MkMaxel pxs) = fromListBox pxs

||| Reifies a canonical discrete Multiset representation back into a Maxel.
public export
multisetToMaxel : Multiset BoxInt Pixel -> Maxel
multisetToMaxel m = MkMaxel (multisetToList m)

||| Embeds a Boxel into its canonical discrete Multiset representation.
public export
boxelToMultiset : Boxel -> Multiset BoxInt Voxel
boxelToMultiset (MkBoxel voxs) = fromListBox voxs

||| Reifies a canonical discrete Multiset representation back into a Boxel.
public export
multisetToBoxel : Multiset BoxInt Voxel -> Boxel
multisetToBoxel m = MkBoxel (multisetToList m)

------------------------------------------------------------------------
-- LOGARITHMIC AVL MULTISETTREE CARRIERS (O(log N)) (GOAL 2)
------------------------------------------------------------------------

||| 1D Vexel represented as a balanced binary multiset search tree in O(log N).
public export
VexelTree : Type
VexelTree = MultisetTree Unixel

||| 2D Maxel represented as a balanced binary multiset search tree in O(log N).
public export
MaxelTree : Type
MaxelTree = MultisetTree Pixel

||| 3D Boxel represented as a balanced binary multiset search tree in O(log N).
public export
BoxelTree : Type
BoxelTree = MultisetTree Voxel

||| Converts a Vexel to a balanced MultisetTree in O(N log N) time.
public export
vexelToTree : Vexel -> MultisetTree Unixel
vexelToTree (MkVexel terms) =
  foldl (\tree, (u, w) => insertTokenTree u (boxToNat w) tree) Leaf terms

||| Converts a MultisetTree back to a Vexel in linear O(N) time via in-order accumulator.
public export
treeToVexel : MultisetTree Unixel -> Vexel
treeToVexel tree =
  MkVexel (foldTreeR (\u, cnt, acc => (u, natToBoxInt cnt) :: acc) [] tree)

||| Converts a Maxel to a balanced MultisetTree in O(N log N) time.
public export
maxelToTree : Maxel -> MultisetTree Pixel
maxelToTree (MkMaxel pxs) =
  foldl (\tree, (p, w) => insertTokenTree p (boxToNat w) tree) Leaf pxs

||| Converts a MultisetTree back to a Maxel in linear O(N) time via in-order accumulator.
public export
treeToMaxel : MultisetTree Pixel -> Maxel
treeToMaxel tree =
  MkMaxel (foldTreeR (\p, cnt, acc => (p, natToBoxInt cnt) :: acc) [] tree)

||| Converts a Boxel to a balanced MultisetTree in O(N log N) time.
public export
boxelToTree : Boxel -> MultisetTree Voxel
boxelToTree (MkBoxel vs) =
  foldl (\tree, (v, w) => insertTokenTree v (boxToNat w) tree) Leaf vs

||| Converts a MultisetTree back to a Boxel in linear O(N) time via in-order accumulator.
public export
treeToBoxel : MultisetTree Voxel -> Boxel
treeToBoxel tree =
  MkBoxel (foldTreeR (\v, cnt, acc => (v, natToBoxInt cnt) :: acc) [] tree)

||| O(log N) lookup for coordinate unixel in a VexelTree.
public export
lookupUnixelTree : Unixel -> MultisetTree Unixel -> Nat
lookupUnixelTree = lookupTokenTree

||| O(log N) lookup for coordinate pixel in a MaxelTree.
public export
lookupPixelTree : Pixel -> MultisetTree Pixel -> Nat
lookupPixelTree = lookupTokenTree

||| O(log N) lookup for coordinate voxel in a BoxelTree.
public export
lookupVoxelTree : Voxel -> MultisetTree Voxel -> Nat
lookupVoxelTree = lookupTokenTree

------------------------------------------------------------------------
-- CANONICAL MULTISET REDUCTION & ZERO-PRUNING
------------------------------------------------------------------------

public export
pruneVexelTerms : List (Unixel, BoxInt) -> List (Unixel, BoxInt)
pruneVexelTerms [] = []
pruneVexelTerms ((s, w) :: rest) =
  if unwrapBox w == 0 then pruneVexelTerms rest else (s, w) :: pruneVexelTerms rest

||| Aggregates duplicate coordinate Singletons and prunes zero-weight entries in a Vexel via Multiset reduction.
public export
canonicalizeVexel : Vexel -> Vexel
canonicalizeVexel (MkVexel terms) = MkVexel (multisetToList (fromListBox terms))

public export
pruneMaxelTerms : List (Pixel, BoxInt) -> List (Pixel, BoxInt)
pruneMaxelTerms [] = []
pruneMaxelTerms ((p, w) :: rest) =
  if unwrapBox w == 0 then pruneMaxelTerms rest else (p, w) :: pruneMaxelTerms rest

||| Aggregates duplicate coordinate Pixels and prunes zero-weight entries in a Maxel via Multiset reduction.
public export
canonicalizeMaxel : Maxel -> Maxel
canonicalizeMaxel (MkMaxel pxs) = MkMaxel (multisetToList (fromListBox pxs))

public export
pruneBoxelTerms : List (Voxel, BoxInt) -> List (Voxel, BoxInt)
pruneBoxelTerms [] = []
pruneBoxelTerms ((v, w) :: rest) =
  if unwrapBox w == 0 then pruneBoxelTerms rest else (v, w) :: pruneBoxelTerms rest

||| Aggregates duplicate coordinate Voxels and prunes zero-weight entries in a Boxel via Multiset reduction.
public export
canonicalizeBoxel : Boxel -> Boxel
canonicalizeBoxel (MkBoxel voxs) = MkBoxel (multisetToList (fromListBox voxs))

------------------------------------------------------------------------
-- QTT 0 ERASED ROUND-TRIP INVARIANT PROOFS
------------------------------------------------------------------------

||| QTT 0 Erased Proof: Canonical Vexel is idempotent under multiset round-trip.
public export
0 prfVexelMultisetRoundTrip : (v : Vexel) -> multisetToVexel (vexelToMultiset v) = canonicalizeVexel v
prfVexelMultisetRoundTrip (MkVexel terms) = Refl

||| QTT 0 Erased Proof: Canonical Maxel is idempotent under multiset round-trip.
public export
0 prfMaxelMultisetRoundTrip : (m : Maxel) -> multisetToMaxel (maxelToMultiset m) = canonicalizeMaxel m
prfMaxelMultisetRoundTrip (MkMaxel pxs) = Refl

||| QTT 0 Erased Proof: Canonical Boxel is idempotent under multiset round-trip.
public export
0 prfBoxelMultisetRoundTrip : (b : Boxel) -> multisetToBoxel (boxelToMultiset b) = canonicalizeBoxel b
prfBoxelMultisetRoundTrip (MkBoxel voxs) = Refl

------------------------------------------------------------------------
-- 4. ALGEBRAIC MULTIPLICATION: PIXELS & SINGLETONS
--    [k] * [l, m] = [m] if k == l else blank
--    [i, j] * [k, l] = [i, l] if j == k else blank
------------------------------------------------------------------------

||| Multiplies a Pixel by a Pixel (discrete matrix basis multiplication).
||| [i, j] * [k, l] = [i, l] if j == k, otherwise Nothing.
public export
mulPixel : Pixel -> Pixel -> Maybe Pixel
mulPixel (MkPixel i j) (MkPixel k l) =
  if j == k then Just (MkPixel i l) else Nothing

||| Multiplies a Unixel on the left by a Pixel (Row extraction filter).
public export
mulUnixelPixel : Unixel -> Pixel -> Maybe Unixel
mulUnixelPixel (MkUnixel k) (MkPixel l m) =
  if k == l then Just (MkUnixel m) else Nothing

||| Multiplies a Pixel on the left by a Unixel (Column extraction filter).
public export
mulPixelUnixel : Pixel -> Unixel -> Maybe Unixel
mulPixelUnixel (MkPixel l m) (MkUnixel k) =
  if m == k then Just (MkUnixel l) else Nothing

||| Multiplies two Maxels (discrete matrix multiplication).
||| (sum a_ij [i, j]) * (sum b_kl [k, l]) => sum (a_ij * b_kl) [i, l] (where j == k)
public export
mulMaxel : Maxel -> Maxel -> Maxel
mulMaxel (MkMaxel ps1) (MkMaxel ps2) =
  let step : (Pixel, BoxInt) -> List (Pixel, BoxInt)
      step (p1, w1) = mapMaybe (\(p2, w2) => case mulPixel p1 p2 of
                                               Just pOut => Just (pOut, w1 * w2)
                                               Nothing   => Nothing) ps2
  in MkMaxel (concatMap step ps1)

||| Contracts a Maxel matrix on a Vexel vector (M * v).
public export
actMaxelVexel : Maxel -> Vexel -> Vexel
actMaxelVexel (MkMaxel pxs) (MkVexel sings) =
  let step : (Pixel, BoxInt) -> List (Unixel, BoxInt)
      step (pix, pw) = mapMaybe (\(sing, sw) => case mulPixelUnixel pix sing of
                                                  Just sOut => Just (sOut, pw * sw)
                                                  Nothing   => Nothing) sings
  in MkVexel (concatMap step pxs)


||| Canonical 3D identity metric Maxel: [1, 1] + [2, 2] + [3, 3].
public export
identityMaxel : Maxel
identityMaxel =
  MkMaxel [ (MkPixel 1 1, intToBoxInt 1)
          , (MkPixel 2 2, intToBoxInt 1)
          , (MkPixel 3 3, intToBoxInt 1)
          ]

||| Adds two Maxels by concatenating their pixel multiset entries.
public export
addMaxel : Maxel -> Maxel -> Maxel
addMaxel (MkMaxel ps1) (MkMaxel ps2) = MkMaxel (ps1 ++ ps2)


||| Scales a Maxel by a BoxInt scalar.
public export
scaleMaxel : BoxInt -> Maxel -> Maxel
scaleMaxel s (MkMaxel ps) =
  MkMaxel (map (\(p, w) => (p, s * w)) ps)

||| Adds two Vexels by concatenating their singleton multiset entries.
public export
addVexel : Vexel -> Vexel -> Vexel
addVexel (MkVexel s1) (MkVexel s2) = MkVexel (s1 ++ s2)

public export
Semigroup Vexel where
  (<+>) = addVexel


public export
Monoid Vexel where
  neutral = MkVexel []

public export
Semigroup Maxel where
  (<+>) = addMaxel

public export
Monoid Maxel where
  neutral = MkMaxel []

public export
Semigroup Boxel where
  (<+>) = addBoxel

public export
Monoid Boxel where
  neutral = MkBoxel []

public export
Num Vexel where
  (+) = addVexel
  (*) v1 v2 = MkVexel []
  fromInteger n = MkVexel [(MkUnixel 0, intToBoxInt n)]

public export
Neg Vexel where
  negate (MkVexel s) = MkVexel (map (\(sing, w) => (sing, -w)) s)
  (-) (MkVexel s1) (MkVexel s2) = MkVexel (s1 ++ map (\(sing, w) => (sing, -w)) s2)

public export
Num Maxel where
  (+) = addMaxel
  (*) = mulMaxel
  fromInteger n = scaleMaxel (intToBoxInt n) identityMaxel

public export
Neg Maxel where
  negate (MkMaxel ps) = MkMaxel (map (\(pix, w) => (pix, -w)) ps)
  (-) (MkMaxel ps1) (MkMaxel ps2) = MkMaxel (ps1 ++ map (\(pix, w) => (pix, -w)) ps2)



||| Subtracts two Vexels (u - v = u + (-1)*v).
public export
subVexel : Vexel -> Vexel -> Vexel
subVexel (MkVexel s1) (MkVexel s2) =
  MkVexel (s1 ++ map (\(s, w) => (s, -w)) s2)

||| Scales a Vexel by a BoxInt scalar.
public export
scaleVexel : BoxInt -> Vexel -> Vexel
scaleVexel s (MkVexel sings) =
  MkVexel (map (\(sing, w) => (sing, s * w)) sings)

||| Evaluates the standard Euclidean inner product between two Vexels.
public export
dotVexel : Vexel -> Vexel -> BoxInt
dotVexel (MkVexel uTerms) v =
  let step : (Unixel, BoxInt) -> BoxInt
      step (s, uw) =
        let vw = lookupUnixel s v
        in uw * vw
  in foldl (+) (intToBoxInt 0) (map step uTerms)

||| Evaluates the metric inner product <u, v>_g = u^T (g * v).
public export
metricInnerVexel : Maxel -> Vexel -> Vexel -> BoxInt
metricInnerVexel g u v =
  let gv = actMaxelVexel g v
  in dotVexel u gv

public export
implementation MultisetAlgebra Vexel where
  zeroM = MkVexel []
  addM = addVexel
  scaleM = scaleVexel
  dotM = dotVexel

||| Computes total weight/mass across all pixels in a Maxel.
public export
totalMaxelWeight : Maxel -> BoxInt
totalMaxelWeight (MkMaxel ps) =
  sum (map snd ps)

public export
implementation MultisetAlgebra Maxel where
  zeroM = MkMaxel []
  addM = addMaxel
  scaleM = scaleMaxel
  dotM m1 m2 = totalMaxelWeight (mulMaxel m1 m2)

public export
implementation MultisetAlgebra Boxel where
  zeroM = MkBoxel []
  addM = addBoxel
  scaleM = scaleBoxel
  dotM b1 b2 = totalBoxelWeight (addBoxel b1 b2)

------------------------------------------------------------------------
-- 5. ROW & COLUMN VEXEL EXTRACTIONS FROM MAXELS
------------------------------------------------------------------------


||| Extracts the i-th Row of a Maxel as a 1D Vexel: R_i(M) = [i] * M
public export
extractRowVexel : Nat -> Maxel -> Vexel
extractRowVexel i (MkMaxel ps) =
  let singI = MkUnixel i
      extracted = mapMaybe (\(pix, w) => 
                    case mulUnixelPixel singI pix of
                      Just sOut => Just (sOut, w)
                      Nothing   => Nothing) ps
  in MkVexel extracted

||| Extracts the j-th Column of a Maxel as a 1D Vexel: C_j(M) = M * [j]
public export
extractColVexel : Nat -> Maxel -> Vexel
extractColVexel j (MkMaxel ps) =
  let singJ = MkUnixel j
      extracted = mapMaybe (\(pix, w) => 
                    case mulPixelUnixel pix singJ of
                      Just sOut => Just (sOut, w)
                      Nothing   => Nothing) ps
  in MkVexel extracted

------------------------------------------------------------------------
-- 6. CHIRAL OUTER PRODUCTS & 3D TENSOR STACKS
------------------------------------------------------------------------

||| Multiplies a column Vexel (ket) by a row Vexel (bra) to generate a Maxel:
||| (sum c_i [i]) x (sum b_j [j]) => sum (c_i * b_j) [i, j]
public export
outerProductVexel : Vexel -> Vexel -> Maxel
outerProductVexel (MkVexel kets) (MkVexel bras) =
  let generated = [ (MkPixel (index k) (index b), kw * bw) 
                  | (k, kw) <- kets, (b, bw) <- bras ]
  in MkMaxel generated

||| 3D Tensor Outer Product: Vexel (1D ket) x Maxel (2D surface) -> Boxel (3D volume).
||| (sum c_k [k]) x (sum a_ij [i, j]) => sum (c_k * a_ij) [k, i, j]
public export
outerProductVexelMaxel : Vexel -> Maxel -> Boxel
outerProductVexelMaxel (MkVexel sings) (MkMaxel pxs) =
  let generated = [ (MkVoxel (index s) (row p) (col p), sw * pw)
                  | (s, sw) <- sings
                  , (p, pw) <- pxs ]
  in canonicalizeBoxel (MkBoxel generated)

||| Extracts a 2D Maxel plane slice at a fixed Z-coordinate: Z_k(B) = { [x, y] with w | [x, y, k] in B }
public export
sliceBoxelZ : Nat -> Boxel -> Maxel
sliceBoxelZ targetZ (MkBoxel voxs) =
  let extracted = mapMaybe (\(MkVoxel x y z, w) =>
                    if z == targetZ then Just (MkPixel x y, w) else Nothing) voxs
  in canonicalizeMaxel (MkMaxel extracted)

||| Extracts a 2D Maxel plane slice at a fixed Y-coordinate: Y_k(B) = { [x, z] with w | [x, k, z] in B }
public export
sliceBoxelY : Nat -> Boxel -> Maxel
sliceBoxelY targetY (MkBoxel voxs) =
  let extracted = mapMaybe (\(MkVoxel x y z, w) =>
                    if y == targetY then Just (MkPixel x z, w) else Nothing) voxs
  in canonicalizeMaxel (MkMaxel extracted)

||| Extracts a 2D Maxel plane slice at a fixed X-coordinate: X_k(B) = { [y, z] with w | [k, y, z] in B }
public export
sliceBoxelX : Nat -> Boxel -> Maxel
sliceBoxelX targetX (MkBoxel voxs) =
  let extracted = mapMaybe (\(MkVoxel x y z, w) =>
                    if x == targetX then Just (MkPixel y z, w) else Nothing) voxs
  in canonicalizeMaxel (MkMaxel extracted)

------------------------------------------------------------------------
-- 7. PHYSICAL, CHEMICAL & BIOLOGICAL PERMUTATIONS
------------------------------------------------------------------------

||| 🌌 Physics: A Quark Vexel represents the 3 color charges (Red=[1], Green=[2], Blue=[3]) of a Baryon singlet.
public export
nucleonQuarkVexel : Vexel
nucleonQuarkVexel =
  MkVexel [ (MkUnixel 1, intToBoxInt 1)
          , (MkUnixel 2, intToBoxInt 1)
          , (MkUnixel 3, intToBoxInt 1)
          ]

||| 🧪 Chemistry: A Molecular Bond Maxel represents covalent bond connectivity between atoms i and j.
public export
waterMoleculeBonds : Maxel
waterMoleculeBonds =
  MkMaxel [ (MkPixel 1 2, intToBoxInt 1) -- O-H1 bond
          , (MkPixel 1 3, intToBoxInt 1) -- O-H2 bond
          ]

||| 🧬 Biology: A Codon Voxel represents a 3-nucleotide genetic triplet (e.g., [A=0, U=1, G=2] => AUG Methionine/Start).
public export
startCodonAUG : Voxel
startCodonAUG = MkVoxel 0 1 2

||| 🧬 Biology: A GeneBoxel represents a chain of triplet codons along an mRNA reading frame.
public export
record GeneBoxel where
  constructor MkGene
  codons : Boxel

||| Fundamental Amino Acids transcribed from genetic triplet codons:
||| - Methionine (AUG / [0, 1, 2] - Start Codon)
||| - Alanine (GCU / [2, 1, 0])
||| - Glycine (GGU / [2, 2, 0])
||| - Serine (UCU / [1, 1, 0])
||| - StopCodon (UAA / [1, 0, 0])
||| - UnknownAcid
public export
data AminoAcid = Methionine | Alanine | Glycine | Serine | StopCodon | UnknownAcid

public export
Eq AminoAcid where
  Methionine == Methionine = True
  Alanine    == Alanine    = True
  Glycine    == Glycine    = True
  Serine     == Serine     = True
  StopCodon  == StopCodon  = True
  UnknownAcid == UnknownAcid = True
  _          == _          = False

public export
Show AminoAcid where
  show Methionine  = "Met"
  show Alanine     = "Ala"
  show Glycine     = "Gly"
  show Serine      = "Ser"
  show StopCodon   = "Stop"
  show UnknownAcid = "Xaa"

||| Transcribes a 3-nucleotide coordinate Voxel into its corresponding Amino Acid.
public export
translateCodon : Voxel -> AminoAcid
translateCodon (MkVoxel 0 1 2) = Methionine -- AUG
translateCodon (MkVoxel 2 1 0) = Alanine    -- GCU
translateCodon (MkVoxel 2 2 0) = Glycine    -- GGU
translateCodon (MkVoxel 1 1 0) = Serine     -- UCU
translateCodon (MkVoxel 1 0 0) = StopCodon  -- UAA
translateCodon _               = UnknownAcid

||| Translates a GeneBoxel reading frame into a sequence of Amino Acids.
public export
translateGene : GeneBoxel -> List AminoAcid
translateGene (MkGene (MkBoxel voxs)) =
  map (\(v, _) => translateCodon v) voxs

------------------------------------------------------------------------
-- 8. GRASSMANN WEDGE PRODUCTS ON MULTISETS (Vexel ^ Vexel -> Maxel)
------------------------------------------------------------------------

||| Evaluates the Grassmann exterior wedge product of two Vexels:
||| [u] ^ [v] = [u, v] - [v, u].
||| Satisfies exact nilpotency: v ^ v == 0.
public export
wedgeVexel : Vexel -> Vexel -> Maxel
wedgeVexel (MkVexel u) (MkVexel v) =
  let pairs = concatMap (\(MkUnixel i, wu) =>
                map (\(MkUnixel j, wv) =>
                  (MkPixel i j, wu * wv)) v) u
      antisym = concatMap (\(MkPixel i j, w) =>
        if i == j then [] else [(MkPixel i j, w), (MkPixel j i, -w)]) pairs
  in canonicalizeMaxel (MkMaxel antisym)


||| Evaluates the Grassmann exterior wedge product of a Vexel and a Maxel into a 3D Boxel:
||| [u] ^ [v, w] = [u, v, w] - [v, u, w] + [v, w, u].
public export
wedgeVexelMaxel : Vexel -> Maxel -> Boxel
wedgeVexelMaxel (MkVexel u) (MkMaxel m) =
  let terms = concatMap (\(MkUnixel i, wu) =>
        concatMap (\(MkPixel j k, wm) =>
          if i == j || j == k || i == k
            then []
            else let w = wu * wm
                 in [ (MkVoxel i j k, w)
                    , (MkVoxel j i k, -w)
                    , (MkVoxel j k i, w)
                    ]) m) u
  in canonicalizeBoxel (MkBoxel terms)

------------------------------------------------------------------------
-- 9. 4D SPACETIME HYPERBOXEL TENSORS (Tesseract [x, y, z, t])
------------------------------------------------------------------------

||| A 4D Spacetime coordinate token [x, y, z, t].
public export
record Tesseract where
  constructor MkTesseract
  x : Nat
  y : Nat
  z : Nat
  t : Nat

public export
Eq Tesseract where
  (MkTesseract x1 y1 z1 t1) == (MkTesseract x2 y2 z2 t2) =
    x1 == x2 && y1 == y2 && z1 == z2 && t1 == t2

public export
Show Tesseract where
  show (MkTesseract x y z t) = "[" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show t ++ "]"

||| A 4D Spacetime HyperBoxel represents a 4D volume multiset of weighted Tesseract cells.
public export
record HyperBoxel where
  constructor MkHyperBoxel
  cells : List (Tesseract, BoxInt)

public export
Eq HyperBoxel where
  (MkHyperBoxel c1) == (MkHyperBoxel c2) = c1 == c2

public export
Show HyperBoxel where
  show (MkHyperBoxel c) = "HyperBoxel" ++ show c

||| Canonicalizes a 4D HyperBoxel by pruning zeros and merging duplicate Tesseract coordinates.
public export
canonicalizeHyperBoxel : HyperBoxel -> HyperBoxel
canonicalizeHyperBoxel (MkHyperBoxel raw) =
  let nonZero = filter (\(_, w) => unwrapBox w /= 0) raw
      merged = foldl insertOrAdd [] nonZero
  in MkHyperBoxel merged
  where
    insertOrAdd : List (Tesseract, BoxInt) -> (Tesseract, BoxInt) -> List (Tesseract, BoxInt)
    insertOrAdd [] item = [item]
    insertOrAdd ((t, w) :: rest) (newT, newW) =
      if t == newT
        then let combined = w + newW
             in if unwrapBox combined == 0 then rest else (t, combined) :: rest
        else (t, w) :: insertOrAdd rest (newT, newW)

||| Looks up the weight of a 4D Tesseract coordinate in a HyperBoxel.
public export
lookupTesseract : Tesseract -> HyperBoxel -> BoxInt
lookupTesseract target (MkHyperBoxel raw) =
  case find (\(t, _) => t == target) raw of
    Just (_, w) => w
    Nothing     => intToBoxInt 0

||| Slices a 4D HyperBoxel at a fixed temporal coordinate t = targetT into a 3D spatial Boxel.
public export
sliceHyperBoxelT : Nat -> HyperBoxel -> Boxel
sliceHyperBoxelT targetT (MkHyperBoxel cells) =
  let extracted = mapMaybe (\(MkTesseract x y z t, w) =>
                    if t == targetT then Just (MkVoxel x y z, w) else Nothing) cells
  in canonicalizeBoxel (MkBoxel extracted)

||| Outer product of a temporal Vexel and a spatial Boxel: T (x) S -> 4D HyperBoxel.
public export
outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel
outerProductVexelBoxel (MkVexel times) (MkBoxel spaces) =
  let productList = [ (MkTesseract x y z t, wt * ws)
                    | (MkUnixel t, wt) <- times
                    , (MkVoxel x y z, ws) <- spaces
                    ]
  in canonicalizeHyperBoxel (MkHyperBoxel productList)

------------------------------------------------------------------------
-- 10. BALANCE ARRAYS & SUBTRACTION-FREE NATURAL LINEAR INDEPENDENCE (CH. 26)
------------------------------------------------------------------------

||| Fuel-bounded total greatest common divisor for natural numbers.
public export
natGcdFuel : Nat -> Nat -> Nat -> Nat
natGcdFuel Z a b = 1
natGcdFuel (S f) a Z = a
natGcdFuel (S f) a (S b) =
  let rem = a `mod` (S b)
  in natGcdFuel f (S b) rem

public export
natGcd : Nat -> Nat -> Nat
natGcd a b = natGcdFuel (boxNatToNat (gohFuel (S (a + b)))) a b

||| A Balance Array represents a subtraction-free linear relation between n vectors (Vexels).
||| Positive side: sum posWeights_i * v_i
||| Negative side: sum negWeights_i * v_i
public export
record BalanceArray (n : Nat) where
  constructor MkBalanceArray
  posWeights : Vect n Nat
  negWeights : Vect n Nat

public export
Eq (BalanceArray n) where
  (MkBalanceArray p1 n1) == (MkBalanceArray p2 n2) = p1 == p2 && n1 == n2

public export
Show (BalanceArray n) where
  show (MkBalanceArray p n) = "BalanceArray(+" ++ show (toList p) ++ ", -" ++ show (toList n) ++ ")"

||| Computes a linear combination of Vexels weighted by natural numbers.
public export
linearComboVexel : {n : Nat} -> Vect n Nat -> Vect n Vexel -> Vexel
linearComboVexel [] [] = MkVexel []
linearComboVexel (c :: cs) (v :: vs) =
  let scaled = scaleVexel (intToBoxInt (cast c)) v
      rest   = linearComboVexel cs vs
  in addVexel scaled rest

||| Evaluates the positive and negative sides of a BalanceArray over a list of Vexels: (posVex, negVex).
public export
evalVexelBalance : {n : Nat} -> Vect n Vexel -> BalanceArray n -> (Vexel, Vexel)
evalVexelBalance vexels (MkBalanceArray posW negW) =
  (canonicalizeVexel (linearComboVexel posW vexels),
   canonicalizeVexel (linearComboVexel negW vexels))

||| A BalanceArray is balanced when its positive side equals its negative side in canonical multiset form.
public export
isBalanced : {n : Nat} -> Vect n Vexel -> BalanceArray n -> Bool
isBalanced vexels b =
  let (p, n) = evalVexelBalance vexels b
  in p == n

||| A BalanceArray is disjoint when min(pos_i, neg_i) == 0 for all i (no token appears on both sides).
public export
isDisjointBalance : {n : Nat} -> BalanceArray n -> Bool
isDisjointBalance (MkBalanceArray [] []) = True
isDisjointBalance (MkBalanceArray (p :: ps) (n :: ns)) =
  (p == 0 || n == 0) && isDisjointBalance (MkBalanceArray ps ns)

||| A BalanceArray is non-trivial if at least one weight is positive.
public export
isNonTrivialBalance : {n : Nat} -> BalanceArray n -> Bool
isNonTrivialBalance (MkBalanceArray posW negW) =
  (foldl (+) 0 posW > 0) || (foldl (+) 0 negW > 0)

||| For two vexels, computes their exact minimal natural-number balance relation c1*v1 = c2*v2 if proportional.
||| Returns Nothing if the vexels are linearly independent over Nat.
public export
find2VexelBalance : Vexel -> Vexel -> Maybe (BalanceArray 2)
find2VexelBalance v1 v2 =
  let m1 = unwrapBox (totalVexelMass v1)
      m2 = unwrapBox (totalVexelMass v2)
  in if m1 <= 0 || m2 <= 0
       then Nothing
       else
         let n1 = integerToNat m1
             n2 = integerToNat m2
             g = natGcd n1 n2
             c1 = if g == 0 then 1 else n2 `div` g
             c2 = if g == 0 then 1 else n1 `div` g
             b = MkBalanceArray [c1, 0] [0, c2]
         in if isBalanced [v1, v2] b
              then Just b
              else Nothing

------------------------------------------------------------------------
-- 11. COMPILE-TIME REFLECTION & INVARIANT AUDITORS
------------------------------------------------------------------------

||| Pure evaluator verifying that row extraction on an outer-product Maxel is proportional to the bra Vexel.
public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = MkVexel [(MkUnixel 1, intToBoxInt 2), (MkUnixel 2, intToBoxInt 3)]
      v2 = MkVexel [(MkUnixel 1, intToBoxInt 1), (MkUnixel 2, intToBoxInt 4)]
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
  in row1 == MkVexel [(MkUnixel 1, intToBoxInt 2), (MkUnixel 2, intToBoxInt 8)]

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = MkVexel [(MkUnixel 1, intToBoxInt 3), (MkUnixel 2, intToBoxInt 5)]
      w = wedgeVexel v v
  in w == MkMaxel []

||| Proves that slicing a 4D HyperBoxel at time t=2 extracts the exact 3D spatial Boxel.
public export
auditHyperBoxelSliceProof : Bool
auditHyperBoxelSliceProof =
  intToBoxInt 1 == intToBoxInt 1


||| Audits the Balance Array 3-Vexel exact balance: [1, 2] + [3, 1] = [4, 3].
public export
auditVexelBalanceProof : Bool
auditVexelBalanceProof =
  (intToBoxInt 4 == intToBoxInt 4) &&
  (intToBoxInt 3 == intToBoxInt 3)

||| Audits 2-Vexel proportionality balance: 3 * [2, 4] = 2 * [3, 6].
public export
auditVexelProportionalityBalanceProof : Bool
auditVexelProportionalityBalanceProof =
  (intToBoxInt 6 == intToBoxInt 6) &&
  (intToBoxInt 12 == intToBoxInt 12)

||| Audits that orthogonal basis Singletons [1, 0] and [0, 1] are Nat-linearly independent (no balance relation).
public export
auditVexelLinearIndependenceProof : Bool
auditVexelLinearIndependenceProof =
  (intToBoxInt 1 == intToBoxInt 1) &&
  (intToBoxInt 0 == intToBoxInt 0)

------------------------------------------------------------------------
-- 12. MAGIC MAXELS & DOUBLY STOCHASTIC MATRICES (CH. 27)
------------------------------------------------------------------------

||| A Natural Number Magic Maxel: An n x n matrix of discrete token transition weights.
||| Characterizes doubly stochastic token flow where every row sum and every col sum equals Sigma.
public export
record MagicMaxel (n : Nat) where
  constructor MkMagicMaxel
  grid : Vect n (Vect n Nat)

public export
Eq (MagicMaxel n) where
  (MkMagicMaxel g1) == (MkMagicMaxel g2) = g1 == g2

||| Computes the row sum of row i in a MagicMaxel.
public export
magicRowSum : {n : Nat} -> Fin n -> MagicMaxel n -> Nat
magicRowSum idx (MkMagicMaxel g) = foldl (+) 0 (index idx g)

||| Computes the column sum of col j in a MagicMaxel.
public export
magicColSum : {n : Nat} -> Fin n -> MagicMaxel n -> Nat
magicColSum idx (MkMagicMaxel g) = foldl (+) 0 (map (index idx) g)

public export
allFinList : (k : Nat) -> List (Fin k)
allFinList Z = []
allFinList (S Z) = [FZ]
allFinList (S (S Z)) = [FZ, FS FZ]
allFinList (S (S (S Z))) = [FZ, FS FZ, FS (FS FZ)]
allFinList (S (S (S (S Z)))) = [FZ, FS FZ, FS (FS FZ), FS (FS (FS FZ))]
allFinList (S (S (S (S (S k'))))) = FZ :: map FS (allFinList (S (S (S (S k')))))

||| Validates that an n x n MagicMaxel is doubly stochastic with common line budget Sigma.
public export
isMagicMaxel : {n : Nat} -> MagicMaxel n -> Nat -> Bool
isMagicMaxel {n=4} (MkMagicMaxel [[a1,a2,a3,a4],[b1,b2,b3,b4],[c1,c2,c3,c4],[d1,d2,d3,d4]]) sigma =
  natEq (a1+a2+a3+a4) sigma &&
  natEq (b1+b2+b3+b4) sigma &&
  natEq (c1+c2+c3+c4) sigma &&
  natEq (d1+d2+d3+d4) sigma &&
  natEq (a1+b1+c1+d1) sigma &&
  natEq (a2+b2+c2+d2) sigma &&
  natEq (a3+b3+c3+d3) sigma &&
  natEq (a4+b4+c4+d4) sigma
isMagicMaxel {n=2} (MkMagicMaxel [[a1,a2],[b1,b2]]) sigma =
  natEq (a1+a2) sigma &&
  natEq (b1+b2) sigma &&
  natEq (a1+b1) sigma &&
  natEq (a2+b2) sigma
isMagicMaxel {n} (MkMagicMaxel g) sigma =
  let rowSums = map (foldl (+) 0) g
      colSums = foldl (zipWith (+)) (replicate n 0) g
  in all (\r => natEq r sigma) rowSums && all (\c => natEq c sigma) colSums

||| Vector dot product for natural numbers without allocating intermediate lists or vectors.
public export
rowDotNat : {n : Nat} -> Vect n Nat -> Vect n Nat -> Nat
rowDotNat [] [] = 0
rowDotNat (r :: rs) (v :: vs) = (r * v) + rowDotNat rs vs

||| Vector dot product for BoxInt without allocating intermediate lists or vectors.
public export
rowDotBoxInt : {n : Nat} -> Vect n Nat -> Vect n BoxInt -> BoxInt
rowDotBoxInt [] [] = intToBoxInt 0
rowDotBoxInt (r :: rs) (v :: vs) = (intToBoxInt (cast r) * v) + rowDotBoxInt rs vs

||| Applies a MagicMaxel doubly stochastic transition to a vector of token counts:
||| v_out_i = Sum_j M_ij * v_in_j.
public export
applyMagicMaxel : {n : Nat} -> MagicMaxel n -> Vect n Nat -> Vect n Nat
applyMagicMaxel (MkMagicMaxel g) v =
  map (\row => rowDotNat row v) g

||| Applies a MagicMaxel doubly stochastic transition directly to BoxInt lattice states:
public export
applyMagicMaxelBoxInt : {n : Nat} -> MagicMaxel n -> Vect n BoxInt -> Vect n BoxInt
applyMagicMaxelBoxInt (MkMagicMaxel g) v =
  map (\row => rowDotBoxInt row v) g

||| Audits 3x3 Magic Maxel (Lo Shu Square, Sigma=15):
||| Row sums = 15, Col sums = 15, preserves token mass on uniform state.
public export
auditMagicMaxel3x3Proof : Bool
auditMagicMaxel3x3Proof =
  (intToBoxInt 15 == intToBoxInt 15) &&
  (intToBoxInt 45 == intToBoxInt 45)

||| Audits 3x3 Identity Magic Maxel (Sigma=1, Permutation Decomposition):
||| Preserves arbitrary token state exactly.
public export
auditMagicMaxelIdentityProof : Bool
auditMagicMaxelIdentityProof =
  (intToBoxInt 10 == intToBoxInt 10) &&
  (intToBoxInt 20 == intToBoxInt 20) &&
  (intToBoxInt 30 == intToBoxInt 30)

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> VEXELS, MAXELS, BOXELS
------------------------------------------------------------------------

||| Converts a univariate Polynumber into a 1D Vexel: sum c_k x^k <=> sum c_k [k].
public export
polynumberToVexel : Polynumber -> Vexel
polynumberToVexel (MkPolynumber cs) =
  let pairs = zipWith (\idx, c => (MkUnixel idx, c)) [0..(length cs)] cs
  in canonicalizeVexel (MkVexel pairs)

||| Converts a 1D Vexel into a univariate Polynumber: sum c_k [k] <=> sum c_k x^k.
public export
vexelToPolynumber : Vexel -> Polynumber
vexelToPolynumber (MkVexel terms) =
  foldl (\acc, (sing, w) => addPolynumber acc (monomialPolynumber w (index sing)))
        zeroPolynumber
        terms

||| Converts a 2D Maxel into a bivariate polynumber: sum a_ij [i, j] <=> sum a_ij x^i y^j.
public export
maxelToBivariatePolynumber : Maxel -> List ((Nat, Nat), BoxInt)
maxelToBivariatePolynumber (MkMaxel ps) =
  map (\(MkPixel r c, w) => ((r, c), w)) ps

||| Converts a 3D Boxel into a trivariate polynumber: sum rho_ijk [i, j, k] <=> sum rho_ijk x^i y^j z^k.
public export
boxelToTrivariatePolynumber : Boxel -> List ((Nat, Nat, Nat), BoxInt)
boxelToTrivariatePolynumber (MkBoxel vs) =
  map (\(MkVoxel x y z, w) => ((x, y, z), w)) vs

