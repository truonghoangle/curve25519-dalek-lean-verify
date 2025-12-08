/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/


set_option diagnostics.threshold 1000000
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

/-! ## Spec for `pow2k.m` (inner limb multiplication)

This is the small helper used inside `pow2k` to multiply two 64-bit limbs
as 128-bit numbers.

- Inputs: two U64 values x and y
- Behavior: cast both to U128 and multiply, returning a U128
- No panic: multiplication in U128 never overflows
- Arithmetic correctness: the returned U128 encodes the product x.val * y.val
-/
@[progress]
theorem pow2k_m_spec (x y : U64) :
    ∃ prod, pow2k.m x y = ok prod ∧ prod.val = x.val * y.val := by
  unfold pow2k.m
  progress*
  simp_all
  have hx: x.val < 2^64:= by scalar_tac
  have hy: y.val < 2^64:= by scalar_tac
  have :=Nat.le_pred_of_lt hy
  have le1:= Nat.mul_le_mul_left (x.val) this
  have := Nat.le_pred_of_lt hx
  have le2:= Nat.mul_le_mul_right ((2 ^ 64).pred) this
  have := le_trans le1 le2
  apply le_trans this
  simp
  scalar_tac


theorem bound_two (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a * (19 * b) + c * (19 * d) ≤  2* (2 ^ n).pred * (19 * (2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    have : ∀(a:ℕ), a + a = 2 * a := by scalar_tac
    rw[this,← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc] at re
    rw[← mul_assoc, ← mul_assoc, ← mul_assoc]
    exact re



theorem bound_twoI (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a * b + c * (19 * d) ≤   (2 ^ n).pred *  (2 ^ n).pred +(2 ^ n).pred * (19 * (2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a this
    have := Nat.mul_le_mul_right ((2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c (Nat.mul_le_mul_left 19 this)
    have := Nat.mul_le_mul_right (19 * (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    simp[← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc] at re
    rw[← mul_assoc, ← mul_assoc]
    exact re





theorem bound_twoII (a b c d n : ℕ)
  (ha : a < 2 ^ n)
  (hb : b < 2 ^ n)
  (hc : c < 2 ^ n)
  (hd : d < 2 ^ n) :
  a *  b + c *  d ≤  2* (2 ^ n).pred * ((2 ^ n).pred):= by
    have := Nat.le_pred_of_lt hb
    have a_le1:= Nat.mul_le_mul_left a this
    have := Nat.mul_le_mul_right ((2 ^ n).pred) (Nat.le_pred_of_lt ha)
    have hab:=le_trans a_le1 this
    have := Nat.le_pred_of_lt hd
    have a_le1:= Nat.mul_le_mul_left c this
    have := Nat.mul_le_mul_right ( (2 ^ n).pred) (Nat.le_pred_of_lt hc)
    have hcd:=le_trans a_le1 this
    have re:= add_le_add hab hcd
    have : ∀(a:ℕ), a + a = 2 * a := by scalar_tac
    rw[this,← mul_assoc] at re
    exact re






/-
natural language description:

    • Computes the 2^k-th power of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs
    • This generalizes the square operation: applying pow2k(a, k) computes a^(2^k)

natural language specs:

    • The function always succeeds (no panic) when k > 0
    • Field51_as_Nat(result) ≡ Field51_as_Nat(a)^(2^k) (mod p)
    • Each limb of the result is bounded: result[i] < 2^51 for all i < 5
-/

/- **Spec and proof concerning the recursive loop `backend.serial.u64.field.FieldElement51.pow2k_loop`**:
- Runs exactly k iterations of “square-and-reduce” when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Input bounds: each input limb < 2^54 (as required by the underlying square routine)
- Output bounds after each iteration: each limb < 2^52

This mirrors the style used for other loop specifications (e.g. `square2_loop_spec`),
but adapts the mathematical statement to repeated squaring.
-/

set_option maxHeartbeats 100000000000 in
-- progress* heavy

@[progress]
theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize)
    (hk : 0 < k.val)
    (h_bounds : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k_loop k a = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  /-
  Outline of proof (left as TODO):
  • Unfold `pow2k_loop`.
  • One body execution computes a single square of `a` together with the standard 51-bit carry
    propagation and the final “carry*19” wrap-around; this is the same algebra as in `square_spec`.
  • If k = 1, the function returns after that single square, yielding the required statement with
    exponent 2^1.
  • If k > 1, it recurses with (k-1) on the freshly squared-and-reduced array; an induction on k
    shows the exponent becomes 2^(k-1) on the new base, hence overall 2^k on the original base.
  • Throughout, limb bounds follow from masking with LOW_51_BIT_MASK and the small carry sizes,
    as used in related proofs (Square/Mul/Reduce specs).
  -/
  have a0_bound:= h_bounds 0 (by simp)
  have a1_bound:= h_bounds 1 (by simp)
  have a2_bound:= h_bounds 2 (by simp)
  have a3_bound:= h_bounds 3 (by simp)
  have a4_bound:= h_bounds 4 (by simp)
  have a1423:= bound_two (a[1]!.val) (a[4]!.val) (a[2]!.val) (a[3]!.val) 54
     (a1_bound) (a4_bound) (a2_bound) (a3_bound)
  have a0124:= bound_twoI (a[0]!.val) (a[1]!.val) (a[2]!.val) (a[4]!.val) 54
     (a0_bound) (a1_bound) (a2_bound) (a4_bound)
  have a0243:= bound_twoI (a[0]!.val) (a[2]!.val) (a[4]!.val) (a[3]!.val) 54
     (a0_bound) (a2_bound) (a4_bound) (a3_bound)
  have a0312:= bound_twoII (a[0]!.val) (a[3]!.val) (a[1]!.val) (a[2]!.val) 54
     (a0_bound) (a3_bound) (a1_bound) (a2_bound)
  have a0413:= bound_twoII (a[0]!.val) (a[4]!.val) (a[1]!.val) (a[3]!.val) 54
     (a0_bound) (a4_bound) (a1_bound) (a3_bound)

  have := le_of_lt a2_bound
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0413 (by simp : 0 ≤  2)
  have a0413I:= add_le_add aa this

  have a_le:= le_of_lt a4_bound
  have := Nat.le_pred_of_lt a4_bound
  have := Nat.mul_le_mul_left 19 this
  have aa:= mul_le_mul a_le this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0312 (by simp : 0 ≤  2)
  have a0312I:= add_le_add aa this

  have := le_of_lt a1_bound
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0243 (by simp : 0 ≤  2)
  have a0243I:= add_le_add aa this

  have a3_le:= le_of_lt a3_bound
  have := Nat.le_pred_of_lt a3_bound
  have := Nat.mul_le_mul_left 19 this
  have aa:= mul_le_mul a3_le this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a0124 (by simp : 0 ≤  2)
  have a0124I:= add_le_add aa this

  have := le_of_lt a0_bound
  have aa:= mul_le_mul this this (Nat.zero_le _) (Nat.zero_le _)
  have := mul_le_mul_of_nonneg_left a1423 (by simp : 0 ≤  2)
  have a1423I:= add_le_add aa this

  unfold pow2k_loop
  progress*
  · simp_all
    apply le_trans a1423
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a1423 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a1423I
    scalar_tac
  · simp_all
    apply le_trans a0124
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a0124 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a0124I
    scalar_tac
  · simp_all
    apply le_trans a0243
    scalar_tac
  · simp_all
    have := mul_le_mul_of_nonneg_left a0243 (by simp : 0 ≤  2)
    apply le_trans this
    scalar_tac
  · simp_all
    apply le_trans a0243I
    scalar_tac
  · simp_all
    apply le_trans a0312I
    scalar_tac
  · suffices h : carry.val ≤  2^ 64 / 19
    · have := Nat.mul_le_mul_right 19 h
      apply le_trans this
      scalar_tac
    · rw[carry_post, UScalar.cast_val_eq, UScalarTy.numBits]
      suffices h : i51.val ≤  2^ 64 / 19
      · have i51_mod: i51.val % 2 ^ 64 = i51.val := by
          apply Nat.mod_eq_of_lt
          have : i51.val ≤  2^64-1 := by
            apply le_trans h
            simp
          apply Nat.lt_of_le_pred (by simp) h
        rw[i51_mod]
        apply h
      · rw[i51_post_1, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[c41_post]
        set con := 2 ^ 54 * 2 ^ 54 + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
        have : c4.val ≤ con := by simp_all
        suffices h : i48.val ≤  2^ 64 / 19 - con
        · have := add_le_add this h
          scalar_tac
        · rw[i48_post, UScalar.cast_val_eq, UScalarTy.numBits]
          suffices h : i47.val ≤  2^ 64 / 19 - con
          · have : i47.val % 2 ^ 128 = i47.val := by
             apply Nat.mod_eq_of_lt
             have : i47.val ≤  2^128-1 := by
              apply le_trans h
              simp[hcon]
             apply Nat.lt_of_le_pred (by simp) this
            rw[this]
            exact h
          · rw[i47_post, UScalar.cast_val_eq, UScalarTy.numBits]
            suffices h : i46.val ≤  2^ 64 / 19 - con
            · have : i46.val % 2 ^ 64 = i46.val := by
                apply Nat.mod_eq_of_lt
                have : i46.val ≤  2^64-1 := by
                  apply le_trans h
                  simp[hcon]
                apply Nat.lt_of_le_pred (by simp) this
              rw[this]
              exact h
            · rw[i46_post_1, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[c31_post]
              set con1 := 2 ^ 54 * 2 ^ 54 + 2 * (2 * (2 ^ 54).pred * (2 ^ 54).pred) with hcon
              have : c31.val ≤ con := by simp_all
              suffices h : i48.val ≤  2^ 64 / 19 - con
              sorry
  sorry
  sorry

























/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.pow2k`**:
- No panic (always returns successfully) when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/


@[progress]
theorem pow2k_spec (a : Array U64 5#usize) (k : U32) (hk : 0 < k.val)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k a k = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52)
    := by
  -- This can be proved from `pow2k_loop_spec` by unfolding and discharging the precondition k > 0.
  -- We keep it as TODO for now to focus this file on the new loop specification.
  unfold pow2k
  progress*
  simp_all


end curve25519_dalek.backend.serial.u64.field.FieldElement51
