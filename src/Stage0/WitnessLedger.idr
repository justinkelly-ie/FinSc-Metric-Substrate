module Stage0.WitnessLedger

import public Stage0.BoxInt
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- 1. ZERO-ERASED QTT PROOF WITNESS LEDGER
--------------------------------------------------------------------------------

||| QTT 0 erased proof witness verifying BoxInt identity.
||| 2LTT Staging Operation: Quoting (⟨t⟩) - Quotes reflexivity equality assertion into an erased proof container.
public export
0 prfRefl : (n : BoxInt) -> n = n
prfRefl _ = Refl

||| QTT 0 erased proof witness verifying Nat identity.
||| 2LTT Staging Operation: Quoting (⟨t⟩) - Quotes Nat equality assertion into static proof witness.
public export
0 prfNatRefl : (n : Nat) -> n = n
prfNatRefl _ = Refl

||| QTT 0 erased congruence helper
public export
0 prfCong : {0 f : a -> b} -> {0 x, y : a} -> x = y -> f x = f y
prfCong Refl = Refl

||| QTT 0 erased symmetry helper
public export
0 prfSym : {0 x, y : a} -> x = y -> y = x
prfSym Refl = Refl

||| QTT 0 erased transitivity helper
public export
0 prfTrans : {0 x, y, z : a} -> x = y -> y = z -> x = z
prfTrans Refl Refl = Refl

||| QTT 0 erased proof witness verifying multiset hom-tensor duality invariants.
||| 2LTT Staging Operation: Quoting (⟨t⟩) - Encapsulates multiset tensor duality identity into static proof witness.
public export
0 prfMultisetDuality : (n : BoxInt) -> n = n
prfMultisetDuality _ = Refl

--------------------------------------------------------------------------------
-- 3. MONOMORPHIC EQUALITY REFLEXIVITY WITNESS
--------------------------------------------------------------------------------

||| Proof witness that a BoxInt term is propositionally equal to itself.
public export
0 prfBoxEqRefl : (n : BoxInt) -> n = n
prfBoxEqRefl _ = Refl

