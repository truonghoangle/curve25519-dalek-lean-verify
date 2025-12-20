/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
/-! # Spec Theorem for `FieldElement51::mul`

Specification and proof for `FieldElement51::mul`.

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul

/-
natural language description:

    • Computes the product of two field elements a and b in the field 𝔽_p where p = 2^255 - 19
    • The field elements are represented as five u64 limbs each

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ Field51_as_Nat(lhs) * Field51_as_Nat(rhs) (mod p)
-/


/- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul.m`**:
- No panic (always returns successfully)
- The result equals the product of the inputs when viewed as natural numbers
- Input bounds: x, y are valid U64 values
- Output bounds: result < 2^128
-/
@[progress]
theorem m_spec (x y : U64) :
    ∃ r, mul.m x y = ok r ∧
    r.val = x.val * y.val := by
  unfold mul.m
  progress*
  have : x.val < 2 ^64 := by scalar_tac
  have i_lt: i.val < 2^ 64 := by
    rw[i_post, UScalar.cast_val_eq, UScalarTy.numBits]
    have : x.val < 2 ^ 128 := by scalar_tac
    have := Nat.mod_eq_of_lt this
    rw[this]
    scalar_tac
  have : y.val < 2 ^64 := by scalar_tac
  have i1_lt: i1.val < 2^ 64 := by
    rw[i1_post, UScalar.cast_val_eq, UScalarTy.numBits]
    have : y.val < 2 ^ 128 := by scalar_tac
    have := Nat.mod_eq_of_lt this
    rw[this]
    scalar_tac
  have := Nat.mul_lt_mul'' i_lt i1_lt
  scalar_tac



lemma LOW_51_BIT_MASK_spec : mul.LOW_51_BIT_MASK.val = 2^ 51 -1 := by
  unfold mul.LOW_51_BIT_MASK
  decide







/- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to the product of the inputs modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/

set_option maxHeartbeats 10000000000 in
-- progress heavy
@[progress]
theorem mul_spec (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    ∃ r, mul lhs rhs = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  unfold mul
  progress*
  · expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
  · expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
  · expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
  · expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    simp at this
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have := Nat.mul_lt_mul_of_pos_right hrhs_1 (by simp : 19 > 0)
    have eq1:= Nat.mul_lt_mul'' hlhs_4 this
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_1 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_2 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have := Nat.add_lt_add eq2 eq1
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq2:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
    have := Nat.add_lt_add eq2 eq1
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    apply le_trans (le_of_lt this)
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    scalar_tac
  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_1 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_0 hrhs_1
    have := Nat.mul_lt_mul_of_pos_right hrhs_2 (by simp : 19 > 0)
    have eq3:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_3 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_2 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i51.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_2 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_1 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_0 hrhs_2
    have := Nat.mul_lt_mul_of_pos_right hrhs_3 (by simp : 19 > 0)
    have eq4:= Nat.mul_lt_mul'' hlhs_4 this
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_3 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i56.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_3 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_2 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_1 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_0 hrhs_3
    have := Nat.mul_lt_mul_of_pos_right hrhs_4 (by simp : 19 > 0)
    have eq5:= Nat.mul_lt_mul'' hlhs_4 this
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i61.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    expand hrhs with 5; expand hlhs with 5; simp [*];
    have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
    have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
    have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
    have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
    have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
    have := Nat.add_lt_add eq1 eq2
    have := Nat.add_lt_add this eq3
    have := Nat.add_lt_add this eq4
    have := Nat.add_lt_add this eq5
    have := Nat.add_lt_add this eq6
    apply le_trans (le_of_lt this)
    scalar_tac

  · simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits]
    suffices h: i71.val < (2^ 64-1)/19
    · have : i71.val < 2 ^ 64 := by scalar_tac
      have := Nat.mod_eq_of_lt this
      rw[this]
      have := (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
      apply le_trans (le_of_lt this)
      scalar_tac
    · simp_all
      rw[Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      expand hrhs with 5; expand hlhs with 5; simp [*];
      have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
      have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
      have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
      have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
      have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
      have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
      have := Nat.add_lt_add eq1 eq2
      have := Nat.add_lt_add this eq3
      have := Nat.add_lt_add this eq4
      have := Nat.add_lt_add this eq5
      have := Nat.add_lt_add this eq6
      apply lt_trans this
      scalar_tac

  · simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits]
    suffices h: i71.val < (2^ 64 - 1 - 2^ 51)/19
    · have : i71.val < 2 ^ 64 := by scalar_tac
      have := Nat.mod_eq_of_lt this
      rw[this]
      have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
      have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
      have := Nat.add_lt_add this eq1
      apply le_trans (le_of_lt this)
      scalar_tac
    · simp_all
      rw[Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      expand hrhs with 5; expand hlhs with 5; simp [*];
      have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
      have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
      have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
      have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
      have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
      have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
      have := Nat.add_lt_add eq1 eq2
      have := Nat.add_lt_add this eq3
      have := Nat.add_lt_add this eq4
      have := Nat.add_lt_add this eq5
      have := Nat.add_lt_add this eq6
      apply lt_trans this
      scalar_tac

  · simp_all
    rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits,
    land_pow_two_sub_one_eq_mod,
    UScalar.cast_val_eq, UScalarTy.numBits,
    Nat.shiftRight_eq_div_pow]
    suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2^ 64 - 1 --2 ^ 51 * (2^ 64 - 1 - 2^ 51)
    · suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 51 * (2^ 64 - 1 - 2^ 51)
      · have eq1:= Nat.mod_lt (c11.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
        have := Nat.div_lt_of_lt_mul h
        have := Nat.add_lt_add eq1 this
        apply le_trans (le_of_lt this)
        scalar_tac
      · apply lt_trans h
        simp
    · suffices h: i71.val < ( 2^ 64 -1 )/19 - 2 ^ 51
      · have : i71.val < 2 ^ 64 := by scalar_tac
        have := Nat.mod_eq_of_lt this
        rw[this]
        have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
        have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
        have := Nat.add_lt_add  this  eq1
        apply lt_trans this
        scalar_tac
      · simp_all
        rw[Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        expand hrhs with 5; expand hlhs with 5; simp [*];
        have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
        have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
        have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
        have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
        have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
        have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
        have := Nat.add_lt_add eq1 eq2
        have := Nat.add_lt_add this eq3
        have := Nat.add_lt_add this eq4
        have := Nat.add_lt_add this eq5
        have := Nat.add_lt_add this eq6
        apply lt_trans this
        scalar_tac
  · constructor
    ·
      simp_all[Field51_as_Nat, Finset.sum_range_succ,Array.make, U64.size, U64.numBits]
      rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      land_pow_two_sub_one_eq_mod,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,
      UScalar.cast_val_eq, UScalarTy.numBits,]




    · intro i _
      interval_cases i
      · simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
      · simp_all
        rw[ UScalar.cast_val_eq, UScalarTy.numBits, LOW_51_BIT_MASK_spec,
        land_pow_two_sub_one_eq_mod,
        UScalar.cast_val_eq, UScalarTy.numBits,
        land_pow_two_sub_one_eq_mod,
        UScalar.cast_val_eq, UScalarTy.numBits,
        Nat.shiftRight_eq_div_pow]

        suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 64 -1
        ·  suffices h: c0.val % 2 ^ 64 % 2 ^ 51 + i71.val % 2 ^ 64 * 19 < 2 ^ 51 * (2^ 52 - 1 - 2^ 51)
           · have eq1:= Nat.mod_lt (c11.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
             have := Nat.div_lt_of_lt_mul h
             have := Nat.add_lt_add eq1 this
             apply lt_trans this
             scalar_tac
           · apply lt_trans h
             scalar_tac
        · suffices h: i71.val < ( 2^ 64 -1 )/19 - 2 ^ 51
          · have : i71.val < 2 ^ 64 := by scalar_tac
            have := Nat.mod_eq_of_lt this
            rw[this]
            have eq1:= (Nat.mul_lt_mul_right (by simp : 0 < 19)).mpr h
            have := Nat.mod_lt (c0.val % 2 ^ 64) (by simp : 0 < 2 ^ 51)
            have := Nat.add_lt_add  this  eq1
            apply lt_trans this
            scalar_tac
          · simp_all
            rw[Nat.shiftRight_eq_div_pow]
            apply Nat.div_lt_of_lt_mul
            expand hrhs with 5; expand hlhs with 5; simp [*];
            have eq1:= Nat.mul_lt_mul'' hlhs_4 hrhs_0
            have eq2:= Nat.mul_lt_mul'' hlhs_3 hrhs_1
            have eq3:= Nat.mul_lt_mul'' hlhs_2 hrhs_2
            have eq4:= Nat.mul_lt_mul'' hlhs_1 hrhs_3
            have eq5:= Nat.mul_lt_mul'' hlhs_0 hrhs_4
            have eq6:=Nat.mod_lt (i66.val) (by simp : 0 < 2 ^64)
            have := Nat.add_lt_add eq1 eq2
            have := Nat.add_lt_add this eq3
            have := Nat.add_lt_add this eq4
            have := Nat.add_lt_add this eq5
            have := Nat.add_lt_add this eq6
            apply lt_trans this
            scalar_tac
      · simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
      · simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp
      · simp_all
        rw [LOW_51_BIT_MASK_spec, land_pow_two_sub_one_eq_mod]
        apply lt_trans _ (by simp : 2 ^ 51 < 2 ^52)
        apply Nat.mod_lt
        simp










end curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul
