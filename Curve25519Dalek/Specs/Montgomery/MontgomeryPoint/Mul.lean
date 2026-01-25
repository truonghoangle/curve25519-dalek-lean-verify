/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Mathlib.Data.BitVec

import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.CtEq
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Identity
/-! # Spec Theorem for `MontgomeryPoint::mul`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::montgomery::MontgomeryPoint), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::scalar::Scalar)}::mul`.

This function implements scalar multiplication of a MontgomeryPoint by delegating to the
corresponding MontgomeryPoint * Scalar implementation (the Montgomery ladder in the backend).

**Source**: curve25519-dalek/src/montgomery.rs, lines 462:4-464:5

## TODO
- Complete proof
-/

open Aeneas.Std Result

/-! ## Spec Theorem for `MontgomeryPoint::mul` (loop 0)

Specification and proof for the Montgomery ladder loop used in
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::montgomery::MontgomeryPoint)}::mul`.

This loop walks the scalar bits from high to low, conditionally swapping the
accumulators and performing one differential add-and-double step per iteration.

**Source**: curve25519-dalek/src/montgomery.rs, lines 428:14-433:56

## TODO
- Complete proof
-/



namespace Aeneas.Std

open Result Error Arith ScalarElab

lemma three_lt_platform_numBits : 3 < System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all

@[progress]
 theorem UScalar.IScalar_ShiftRight_spec {ty0 ty1} (x : IScalar ty0) (y : IScalar ty1)
  (hy0 : 0 ≤ y.val) (hy1 : y.val < ty0.numBits) :
  ∃ z, x >>> y = ok z ∧ z.val = x.toNat >>> y.toNat ∧ z.bv = x.toNat >>> y.toNat
  := by
  have hy1 : y.toNat < ty0.numBits := by scalar_tac
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight, hy0, hy1, reduceIte]
  simp only
    [BitVec.ushiftRight_eq,
     ok.injEq,
     _root_.exists_eq_left',
     IScalar.toNat,
     Nat.instShiftRight,
     ]
  sorry



uscalar@[progress] theorem «%S».IScalar_ShiftRight_spec {ty1} (x : «%S») (y : IScalar ty1) (hy0 : 0 ≤ y.val) (hy : y.val < %BitWidth) :
  ∃ (z : «%S»), x >>> y = ok z ∧ z.val = x.val >>> y.toNat ∧ z.bv = x.bv >>> y.toNat
  := by apply UScalar.ShiftRight_IScalar_spec <;> simp [*]

end Aeneas.Std


namespace curve25519_dalek.montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

/-
natural language description:

• Iterates over the scalar bits from index `i` down to 0 (inclusive).

• For each iteration, extracts the current bit from `scalar_bytes`, conditionally
  swaps the accumulator points depending on the bit transition, and applies one
  `differential_add_and_double` step.

• Updates `prev_bit` to the current bit and recurses with `i - 1`.

natural language specs:

• The loop always succeeds (no panic)
• If `i < 0`, the loop returns the current accumulator points and `prev_bit`
• If `i ≥ 0`, the loop:
  - Extracts the bit at position `i`
  - Conditionally swaps `(x0, x1)` based on the bit transition
  - Applies `differential_add_and_double`
  - Continues recursively with `i - 1`
-/

/- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul_loop`**:
- No panic (always returns successfully)
- Base case (`i < 0`) returns the input accumulators unchanged
- Step case (`i ≥ 0`) performs the Montgomery ladder step and recurses with `i - 1`
- The result corresponds to iterating the loop body exactly as in the implementation
-/


set_option maxHeartbeats 1000000000 in
-- simp heavy

theorem mul_loop_spec
    (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 x1 : montgomery.ProjectivePoint)
    (scalar_bytes : Array U8 32#usize)
    (prev_bit : Bool)
    (i : Isize) :
    ∃ x,
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i = ok x ∧
    (i < 0#isize → x = (x0, x1, prev_bit)) ∧
    (0#isize ≤ i →
      ∃ i1 byte_idx i2 bit_idx scalar_byte i4 bit choice c x01 x11 x02 x12 i6,
        i >>> 3#i32 = ok i1 ∧
        (IScalar.hcast .Usize i1 : Result Usize) = ok byte_idx ∧
        (i &&& 7#isize : Result Isize) = ok i2 ∧
        (IScalar.hcast .Usize i2 : Result Usize) = ok bit_idx ∧
        Array.index_usize scalar_bytes byte_idx = ok scalar_byte ∧
        scalar_byte >>> bit_idx = ok i4 ∧
        (i4 &&& 1#u8 : Result U8) = ok bit ∧
        (UScalar.cast_fromBool .U8 (prev_bit != (bit = 1#u8)) : Result U8) = ok choice ∧
        core.convert.IntoFrom.into core.convert.FromChoiceU8 choice = ok c ∧
        montgomery.ConditionallySelectableProjectivePoint.conditional_swap x0 x1 c =
          ok (x01, x11) ∧
        montgomery.differential_add_and_double x01 x11 affine_u = ok (x02, x12) ∧
        i - 1#isize = ok i6 ∧
        mul_loop affine_u x02 x12 scalar_bytes (bit = 1#u8) i6 =
          ok x) := by

    unfold mul_loop
    progress*
    · cases System.Platform.numBits_eq <;> simp_all
    · simp_all[IScalar.hcast]
      sorry
    · simp_all [IScalar.hcast]
      sorry
    · unfold subtle.FromChoiceU8.from
      rename_i hc
      simp[hc]
      progress*
      sorry
    · unfold subtle.FromChoiceU8.from
      rename_i hc
      simp[hc]
      progress*
      sorry





















/-
natural language description:

• Computes the scalar multiplication [s]P on the Montgomery curve, where P is a
  MontgomeryPoint (u-coordinate only) and s is a scalar.

• The implementation converts the input u-coordinate to a FieldElement51, initializes
  the Montgomery ladder state, executes the ladder loop over the scalar bits, performs
  a final conditional swap based on the last processed bit, and converts the result
  back to an affine MontgomeryPoint.

natural language specs:

• The function always succeeds (no panic)
• The result equals the affine conversion of the Montgomery ladder output
  (including the final conditional swap)
-/

/-- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully)
- Converts the input u-coordinate to a field element and initializes the ladder
- Executes the Montgomery ladder loop and final conditional swap
- Returns the affine u-coordinate of the resulting projective point
-/
@[progress]
theorem mul_spec (self : MontgomeryPoint) (sc : scalar.Scalar) :
    ∃ result,
    mul self sc = ok result ∧
    ∃ affine_u x0 scalar_bytes x01 x1 prev_bit bit_choice c x02 x03,
      backend.serial.u64.field.FieldElement51.from_bytes self = ok affine_u ∧
      montgomery.IdentityProjectivePoint.identity = ok x0 ∧
      scalar.Scalar.as_bytes sc = ok scalar_bytes ∧
      montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul_loop
          affine_u x0
          { U := affine_u, W := backend.serial.u64.field.FieldElement51.ONE }
          scalar_bytes false 254#isize = ok (x01, x1, prev_bit) ∧
      (↑(UScalar.cast_fromBool .U8 prev_bit) : Result U8) = ok bit_choice ∧
      subtle.FromChoiceU8.from bit_choice = ok c ∧
      montgomery.ConditionallySelectableProjectivePoint.conditional_swap x01 x1 c =
        ok (x02, x03) ∧
      montgomery.ProjectivePoint.as_affine x02 = ok result := by

    unfold mul
    progress*
    unfold scalar.Scalar.as_bytes
    progress*
    unfold mul_loop
    simp
    progress*
    · simpa using (Aeneas.Std.three_lt_platform_numBits)
    · sorry
    · sorry
    · by_cases hx:x = 0#u8
      · simp_all
        unfold subtle.FromChoiceU8.from
        simp
        sorry
      · sorry









end curve25519_dalek.montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint

namespace curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint
open Aeneas.Std Result

/-
natural language description:

• Computes the scalar multiplication [s]P on the Montgomery curve, where s is a Scalar
  and P is a MontgomeryPoint (u-coordinate only).

• The implementation simply calls the MontgomeryPoint * Scalar routine, which uses the
  Montgomery ladder on the u-coordinate.

natural language specs:

• The function always succeeds (no panic)
• The result is exactly the output of `MontgomeryPoint * Scalar` with arguments swapped
-/

/-- **Spec and proof concerning `montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully)
- Delegates to `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`
- The returned MontgomeryPoint equals the Montgomery ladder result for the given scalar and point
-/
@[progress]
theorem mul_spec (self : scalar.Scalar) (point : MontgomeryPoint) :
    ∃ result,
    mul self point = ok result ∧
    montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul point self =
      ok result := by
    unfold mul
    progress*

end curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint
