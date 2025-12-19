/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
/-! # Spec Theorem for `Scalar52::montgomery_reduce`

Specification and proof for `Scalar52::montgomery_reduce`.

This function performs Montgomery reduction.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open curve25519_dalek.backend.serial.u64
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold  10000

/-
natural language description:

    • Takes as input a 9-limb array of u128 values (representing a product in polynomial form)
      and performs Montgomery reduction to produce an UnpackedScalar in Montgomery form.

    • Montgomery reduction is the core operation that reduces a product (m * m') back to
      Montgomery form by computing (product * R⁻¹) mod L, where R = 2^260.

    • This is used after polynomial multiplication (mul_internal or square_internal) to
      complete Montgomery multiplication or squaring operations.

natural language specs:

    • For any 9-limb array a of u128 values:
      - The function returns a Scalar52 m such that:
        Scalar52_as_Nat(m) * R ≡ U128x9_as_Nat(a) (mod L)
-/

/- **Spec and proof concerning `scalar.m`**:
- No panic (always returns successfully)
- The result is the product of x and y cast to U128
- This is a helper function used in scalar multiplication operations
-/



lemma L_spec1 : (constants.L[1]!).val = 3916664325105025 := by
  unfold constants.L constants.L_body
  decide



@[progress]
theorem montgomery_reduce_part2_spec (sum : U128) :
    ∃ cw : U128 × U64,
    montgomery_reduce.part2 sum = ok cw ∧
    cw.2.val = sum.val % (2^52) ∧
    cw.1.val = sum.val / (2^52)
    := by
  unfold  montgomery_reduce.part2
  progress*
  simp[w_post_1]
  rw[i2_post_1, i1_post_1, Nat.shiftLeft_eq, (by simp: ∀ a, 1 * a =a)]
  have : 2 ^ 52 % U64.size - 1= 2 ^ 52 - 1 := by simp[U64.size, U64.numBits]
  rw[this,land_pow_two_sub_one_eq_mod, i_post, i3_post_1, Nat.shiftRight_eq_div_pow, UScalar.cast_val_eq, UScalarTy.numBits]
  grind


set_option maxHeartbeats 10000000 in
-- progress heavy

@[progress]
theorem montgomery_reduce_part1_spec (sum : U128)
    (sum_bounds : sum.val < 7 * 2 ^ 124) :
    ∃ cp : U128 × U64,
    montgomery_reduce.part1 sum = ok cp ∧
    cp.2.val = (sum.val * constants.LFACTOR.val) % (2^52) ∧
    cp.1.val = (sum.val + cp.2.val * (constants.L[0]!).val) / (2^52)
    := by
  unfold montgomery_reduce.part1 Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  · suffices h: i5.val < 2 ^128 -  7 * 2 ^ 124 -1
    · have := Nat.add_lt_add sum_bounds h
      apply le_trans (le_of_lt this)
      scalar_tac
    · rw[i5_post, i4_post, p_post_1]
      simp[ i3_post_1]
      rw[i2_post_1, Nat.shiftLeft_eq, (by simp: ∀ a, 1 * a =a)]
      have : 2 ^ 52 % U64.size - 1= 2 ^ 52 - 1 := by simp[U64.size, U64.numBits]
      rw[this,land_pow_two_sub_one_eq_mod]
      have L0_pos:0< (constants.L[0]!).val := by
        unfold constants.L
        decide
      have := Nat.mod_lt (i1.val) (by simp : 0 < 2 ^52)
      have := (Nat.mul_lt_mul_right L0_pos).mpr this
      simp at this
      apply lt_trans this
      scalar_tac
  · constructor
    · simp[p_post_1, i3_post_1]
      rw[i2_post_1, Nat.shiftLeft_eq, (by simp: ∀ a, 1 * a =a)]
      have : 2 ^ 52 % U64.size - 1= 2 ^ 52 - 1 := by simp[U64.size, U64.numBits]
      rw[this,land_pow_two_sub_one_eq_mod]
      simp[i1_post, i_post, UScalar.cast_val_eq, UScalarTy.numBits]
      rw[(by simp : 18446744073709551616= 2 ^64 )]
      have : constants.LFACTOR.val = 1439961107955227 := by
        unfold constants.LFACTOR constants.LFACTOR_body
        decide
      simp_all [U64.size, U64.numBits]
    · simp[p_post_1, i3_post_1, i7_post_1, Nat.shiftRight_eq_div_pow,
      i6_post, i5_post, i4_post]







#check Nat.mul_lt_mul_right


























set_option maxHeartbeats 1000000000 in
-- progress heavy

/- **Spec and proof concerning `scalar.Scalar52.montgomery_reduce`**:
- No panic (always returns successfully)
- The result m satisfies the Montgomery reduction property:
  m * R ≡ a (mod L), where R = 2^260 is the Montgomery constant
-/
@[progress]
theorem montgomery_reduce_spec (a : Array U128 9#usize)
    (a_bounds : ∀ i < 9, a[i]!.val < 5 * 2 ^ 124) :
    ∃ m,
    montgomery_reduce a = ok m ∧
    (Scalar52_as_Nat m * R) % L = Scalar52_wide_as_Nat a % L ∧
    ( ∀ i < 5, m[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat m < 2 ^ 259)
    := by
  unfold montgomery_reduce backend.serial.u64.scalar.Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  · simp_all
    grind
  · have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[0]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    suffices h: __discr.1.val ≤  2 ^128-1 - 5 * 2 ^ 124
    · have :=Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp)))
      simp at this
      simp[i1_post]
      apply le_trans this
      scalar_tac
    · rw[__discr_post_2, __discr_post_1, i_post]
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      apply Nat.div_le_of_le_mul
      simp_all
      apply le_trans (le_of_lt this)
      scalar_tac
  · rw[i2_post, i4_post, i3_post]
    have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[1]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    rw[← __discr_post_1] at this
    have := Nat.add_lt_add (a_bounds 1 (by simp)) this
    suffices h:  __discr.1.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[1]!).val
    · have :=Nat.add_le_add h (le_of_lt this)
      rw[← add_assoc] at this
      simp_all
      apply le_trans this
      have : (constants.L[1]!).val = 3916664325105025 := by
        unfold constants.L constants.L_body
        decide
      simp at this
      simp[this, U128.max, U128.numBits]
    · have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
      have :0< (constants.L[0]!).val := by
       unfold constants.L
       decide
      have := (Nat.mul_lt_mul_right this).mpr ineq1
      rw[__discr_post_2, __discr_post_1, i_post]
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      apply Nat.div_le_of_le_mul
      simp_all
      apply le_trans (le_of_lt this)
      scalar_tac
  · rw[i5_post, i4_post, i3_post, __discr_post_1]
    have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[1]!).val := by
      unfold constants.L
      decide
    have ineq2:= (Nat.mul_lt_mul_right this).mpr ineq1
    have :=Nat.add_lt_add (a_bounds 1 (by simp)) ineq2
    suffices h: __discr.1.val <  7* 2 ^124-1 - (5 * 2 ^ 124 + 2 ^ 52 * ↑constants.L[1]!)
    · have :=Nat.add_lt_add h this
      simp[← add_assoc] at this
      simp[i2_post, i1_post]
      apply lt_trans this
      scalar_tac
    · rw[__discr_post_2, __discr_post_1]
      apply Nat.div_lt_of_lt_mul
      have :0< (constants.L[0]!).val := by
        unfold constants.L
        decide
      have := (Nat.mul_lt_mul_right this).mpr ineq1
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      simp[i_post]
      simp[i_post] at this
      apply lt_trans this
      scalar_tac
  · have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[0]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    suffices h: __discr.1.val ≤   2 ^128-1 - 5 * 2 ^ 124
    · have :=Nat.add_le_add h (le_of_lt (a_bounds 2 (by simp)))
      simp at this
      simp[i6_post]
      apply le_trans this
      scalar_tac
    · rw[__discr_post_2, __discr_post_1]
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      apply Nat.div_le_of_le_mul
      have ineq1:= Nat.mod_lt (i5.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
      have :0< (constants.L[0]!).val := by
       unfold constants.L
       decide
      have := (Nat.mul_lt_mul_right this).mpr ineq1
      suffices h: i5.val <  2 ^ 52 * (2 ^ 128 - 1 - 5 * 2 ^ 124) - 2 ^ 52 * (constants.L[0]!).val
      · have :=Nat.add_lt_add h this
        simp_all
        apply le_trans (le_of_lt this)
        scalar_tac
      · rw[i5_post, i2_post, i4_post, i3_post]
        have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
        have :0< (constants.L[1]!).val := by
          unfold constants.L
          decide
        have := (Nat.mul_lt_mul_right this).mpr ineq1
        clear __discr_post_1  __discr_post_2
        rw[← __discr_post_1] at this
        have := Nat.add_lt_add (a_bounds 1 (by simp)) this
        rename' __discr => ha
        suffices h:  __discr.1.val ≤  (2 ^ 52 * (2 ^ 128 - 1 - 5 * 2 ^ 124) - 2 ^ 52 * ↑constants.L[0]!)
         - (5 * 2 ^ 124 + 2 ^ 52 * (constants.L[1]!).val)-2
        · have :=Nat.add_le_add h (le_of_lt this)
          rw[← add_assoc] at this
          simp_all
          apply lt_of_le_of_lt this
          have : (constants.L[1]!).val = 3916664325105025 := by
            unfold constants.L constants.L_body
            decide
          have : (constants.L[0]!).val = 671914833335277 := by
            unfold constants.L constants.L_body
            decide
          simp_all
        · rw[__discr_post_2, __discr_post_1, i_post]
          simp_all
          clear this
          clear this
          apply Nat.div_le_of_le_mul
          apply le_trans (le_of_lt this)
          scalar_tac
  · rw[i7_post, i6_post]
    rename' __discr => discr1
    have : i9.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i9_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L constants.L_body
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rename' __discr_post_1=>  __discr1
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    have := Nat.add_lt_add (a_bounds 2 (by simp: 2<9)) this
    suffices h: discr1.1.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val
    · have := Nat.add_le_add h (le_of_lt this)
      simp[← add_assoc] at this
      simp
      apply le_trans this
      scalar_tac
    · rw[__discr_post_2]
      apply Nat.div_le_of_le_mul
      have : ↑discr1.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
        simp
        have : 0< ((constants.L)[0]!).val := by
          unfold constants.L constants.L_body
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
      2 ^ 52 *  ((constants.L)[0]!).val
      · have := Nat.add_le_add h (le_of_lt this)
        simp at this
        simp
        apply le_trans this
        scalar_tac
      · rw[i5_post]
        have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i4_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L constants.L_body
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rename' __discr_post_1=>  __discr1
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
        · have := Nat.add_le_add h (le_of_lt this)
          simp at this
          simp
          apply le_trans this
          scalar_tac
        · rw[i2_post]
          suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
          · have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
            simp at this
            simp[i1_post]
            apply le_trans this
            scalar_tac
          · rename' __discr_post_1=>  __discr1
            rename' __discr_post_2=>  __discr2
            rw[__discr_post_2]
            apply Nat.div_le_of_le_mul
            have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L constants.L_body
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i.val ≤  2 ^ 52 *
    (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
      5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
            · have := Nat.add_le_add h (le_of_lt this)
              simp at this
              simp
              apply le_trans this
              scalar_tac
            · rw[i_post]
              have:= (le_of_lt (a_bounds 0 (by simp : 0 < 9)))
              simp at this
              simp
              apply le_trans this
              scalar_tac
  · rw[i10_post]
    have eq1: i11.val < 2 ^52 * ((constants.L)[1]!).val := by
     rw[i11_post, i3_post, __discr_post_1 ]
     have ineq1:= Nat.mod_lt (i5.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
     have :0< (constants.L[1]!).val := by
      unfold constants.L
      decide
     have ineq2:= (Nat.mul_lt_mul_right this).mpr ineq1
     simp_all
    have : i9.val < 2 ^52 * ((constants.L)[2]!).val := by
     rw[i9_post, i8_post ]
     rename' __discr_post_1=>  __discr1
     rename' __discr_post_2=>  __discr2
     rw[__discr_post_1]
     have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
     have :0< (constants.L[2]!).val := by
      unfold constants.L
      decide
     have ineq2:= (Nat.mul_lt_mul_right this).mpr ineq1
     simp_all
    have :=Nat.add_lt_add this eq1
    suffices h: i7.val ≤   2 ^128 -1- (2 ^ 52 * ↑constants.L[2]! + 2 ^ 52 * ↑constants.L[1]!)
    · have := Nat.add_le_add h (le_of_lt this)
      rw[← add_assoc] at this
      apply le_trans this
      scalar_tac
    · rw[i7_post, i6_post]













  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · constructor
    · sorry
    · constructor
      · grind
      · sorry





























end curve25519_dalek.backend.serial.u64.scalar.Scalar52
