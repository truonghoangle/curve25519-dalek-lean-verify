/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Tactics
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


lemma L_spec0 : ((constants.L.val)[0]!).val = 671914833335277 := by
  unfold constants.L
  decide

lemma L_spec1 : ((constants.L.val)[1]!).val = 3916664325105025 := by
  unfold constants.L
  decide

lemma L_spec2 : ((constants.L.val)[2]!).val = 1367801 := by
  unfold constants.L
  decide

lemma L_spec3 : ((constants.L.val)[3]!).val = 0 := by
  unfold constants.L
  decide

lemma L_spec4 : ((constants.L.val)[4]!).val = 17592186044416 := by
  unfold constants.L
  decide


theorem land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  · simp
    scalar_tac
  · simp

@[progress]
theorem montgomery_reduce_part2_spec (sum : U128) :
    ∃ cw : U128 × U64,
    montgomery_reduce.part2 sum = ok cw ∧
    cw.2.val = sum.val % (2^52) ∧
    cw.1.val = sum.val / (2^52)
    := by
   sorry
/-
  unfold  montgomery_reduce.part2
  progress*
  simp[w_post_1]
  rw[i2_post_1, i1_post_1, Nat.shiftLeft_eq, (by simp: ∀ a, 1 * a =a)]
  have : 2 ^ 52 % U64.size - 1= 2 ^ 52 - 1 := by scalar_tac
  rw[this,land_pow_two_sub_one_eq_mod, i_post, i3_post_1]
  rw[Nat.shiftRight_eq_div_pow,UScalar.cast_val_eq, UScalarTy.numBits]
  grind
-/
@[progress]
theorem montgomery_reduce_part1_spec (sum : U128) (sum_bound : sum.val < 2 ^ 128 - 2 ^ 102) :
    ∃ cp : U128 × U64,
    montgomery_reduce.part1 sum = ok cp ∧
    cp.2.val = (sum.val * constants.LFACTOR.val) % (2^52) ∧
    cp.1.val = (sum.val + cp.2.val * (constants.L[0]!).val) / (2^52)
    := by
    sorry
 /-
  unfold montgomery_reduce.part1 Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
  · -- BEGIN TASK
    suffices h: i5.val <  2 ^ 102
    · -- BEGIN TASK
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[i5_post,i4_post, L_spec0]
      have : p.val < 2 ^ 52 := by
        simp[p_post_1, i3_post_1 ]
        rw[i2_post_1]
        have : 1 <<< 52 % U64.size - 1 = 2 ^ 52 -1 := by
          scalar_tac
        rw[this, land_pow_two_sub_one_eq_mod]
        apply Nat.mod_lt
        simp
      scalar_tac
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    constructor
    · -- BEGIN TASK
      simp[p_post_1, i3_post_1]
      rw[i2_post_1]
      have : 1 <<< 52 % U64.size - 1 = 2 ^ 52 -1 := by
          scalar_tac
      rw[this, land_pow_two_sub_one_eq_mod]
      simp[i1_post, i_post, UScalar.cast_val_eq, UScalarTy.numBits]
      simp[U64.size, U64.numBits]
      -- END TASK
    · -- BEGIN TASK
      simp_all[Nat.shiftRight_eq_div_pow ]
      -- END TASK
    -- END TASK
-/





-- All limbs of constants.L are bounded by 2^52
lemma L_limbs_bound : ∀ i < 5, (constants.L[i]!).val < 2 ^ 52 := by
  intro i hi
  interval_cases i
  all_goals (unfold constants.L; decide)

theorem mul_mod (a c p : ℕ) : (a * c) % p = ((a % p) * (c % p)) % p := by
  simp [Nat.mul_mod]


@[progress]
theorem L_spec : Scalar52_as_Nat constants.L = L := by
  unfold constants.L
  decide


/- **Spec and proof concerning `scalar.m`**:
- No panic (always returns successfully)
- The result is the product of x and y cast to U128
- This is a helper function used in scalar multiplication operations
-/






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
    (Scalar52_as_Nat m < L)
    := by
    sorry
/-
  unfold montgomery_reduce backend.serial.u64.scalar.Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
  progress*
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
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · intro i hi
    interval_cases i
    any_goals (simp_all [Array.make]; apply Nat.mod_lt; simp)
    simp[Array.make]
    rw[r4_post, UScalar.cast_val_eq, UScalarTy.numBits, __discr_post_2]




  · unfold constants.L
    decide
  · -- BEGIN STASK
    rw[L_spec]
    simp[Scalar52_as_Nat,Finset.sum_range_succ, Array.make]




    -- END STASK


  ·





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
  · -- BEGIN TASK
    expand a_bounds with 5; scalar_tac
    -- END TASK
  · -- BEGIN TASK
    have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
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
    -- END TASK
  · -- BEGIN TASK
    rw[i2_post, i4_post, i3_post]
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
        unfold constants.L
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
    -- END TASK
  · -- BEGIN TASK
    rw[i5_post,i2_post, i4_post, i3_post]
    have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[1]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    rw[← __discr_post_1] at this
    have := Nat.add_lt_add (a_bounds 1 (by simp)) this
    suffices h:  __discr.1.val <  2 ^128 - 2^ 102 -1- 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[1]!).val
    · -- BEGIN TASK
      have :=Nat.add_lt_add h this
      rw[← add_assoc] at this
      simp_all
      apply lt_trans this
      have : (constants.L[1]!).val = 3916664325105025 := by
        unfold constants.L
        decide
      simp at this
      simp[this]
      -- END TASK
    · -- BEGIN TASK
      have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
      have :0< (constants.L[0]!).val := by
       unfold constants.L
       decide
      have := (Nat.mul_lt_mul_right this).mpr ineq1
      rw[__discr_post_2, __discr_post_1, i_post]
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      apply Nat.div_lt_of_lt_mul
      simp_all
      apply lt_trans this
      scalar_tac
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    have ineq1:= Nat.mod_lt (i.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[0]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    suffices h: __discr.1.val ≤  2 ^128-1 - 5 * 2 ^ 124
    · -- BEGIN TASK
      have :=Nat.add_le_add h (le_of_lt (a_bounds 2 (by simp)))
      simp at this
      simp[i6_post]
      apply le_trans this
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[__discr_post_2, __discr_post_1]
      have :=Nat.add_lt_add (a_bounds 0 (by simp)) this
      apply Nat.div_le_of_le_mul
      have ineq1:= Nat.mod_lt (i5.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
      have :0< (constants.L[0]!).val := by
       unfold constants.L
       decide
      have := (Nat.mul_lt_mul_right this).mpr ineq1
      suffices h: i5.val <  2 ^ 52 * (2 ^ 128 - 1 - 5 * 2 ^ 124) - 2 ^ 52 * (constants.L[0]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[i5_post, i2_post, i4_post, i3_post]
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
        · -- BEGIN TASK
          have :=Nat.add_le_add h (le_of_lt this)
          rw[← add_assoc] at this
          simp_all
          apply lt_of_le_of_lt this
          have : (constants.L[1]!).val = 3916664325105025 := by
            unfold constants.L
            decide
          have : (constants.L[0]!).val = 671914833335277 := by
            unfold constants.L
            decide
          simp_all
          -- END TASK
        · -- BEGIN TASK
          rw[__discr_post_2, __discr_post_1, i_post]
          simp_all
          clear this
          clear this
          apply Nat.div_le_of_le_mul
          apply le_trans (le_of_lt this)
          scalar_tac
          -- END TASK
        -- END TASK
      -- END TASK
    -- END TASK

  · -- BEGIN TASK
    rw[i7_post, i6_post]
    rename' __discr => discr1
    have : i9.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i9_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rename' __discr_post_1=>  __discr1
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    have := Nat.add_lt_add (a_bounds 2 (by simp: 2<9)) this
    suffices h: discr1.1.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val
    · -- BEGIN TASK
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[__discr_post_2]
      apply Nat.div_le_of_le_mul
      have : ↑discr1.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
        simp
        have : 0< ((constants.L)[0]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
      2 ^ 52 *  ((constants.L)[0]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[i5_post]
        have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i4_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rename' __discr_post_1=>  __discr1
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[i2_post]
          suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
          · -- BEGIN TASK
            have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
            simp at this
            simp[i1_post]
            apply le_trans this
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rename' __discr_post_1=>  __discr1
            rename' __discr_post_2=>  __discr2
            rw[__discr_post_2]
            apply Nat.div_le_of_le_mul
            have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i.val ≤  2 ^ 52 *
               (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
               5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
            · -- BEGIN TASK
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[i_post]
              scalar_tac
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK
    -- END TASK

  ·  -- BEGIN TASK
    rw[i10_post, i11_post]
    have : i11.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i11_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    suffices h: i7.val + i9.val ≤  2^ 128 - 1 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · rw[i7_post, i6_post]
      rename' __discr => discr1
      have : i9.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
        simp[i9_post, i8_post]
        have : 0< ((constants.L)[2]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rename' __discr_post_1=>  __discr1
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      have := Nat.add_lt_add (a_bounds 2 (by simp: 2<9)) this
      suffices h: discr1.1.val ≤  2^ 128 - 1 - 2 ^ 52 *  ((constants.L)[1]!).val  - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_le_of_le_mul
        have : ↑discr1.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
        2 ^ 52 *  ((constants.L)[0]!).val
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[i5_post]
          have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
            simp[i4_post, i3_post]
            have : 0< ((constants.L)[1]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rename' __discr_post_1=>  __discr1
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rw[i2_post]
            suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
              simp at this
              simp[i1_post]
              apply le_trans this
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rename' __discr_post_1=>  __discr1
              rename' __discr_post_2=>  __discr2
              rw[__discr_post_2]
              apply Nat.div_le_of_le_mul
              have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i.val ≤  2 ^ 52 *
                (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i_post]
                scalar_tac
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK



    -- END TASK


  ·  -- BEGIN TASK
    rw[i12_post, i10_post, i11_post]
    have : i11.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i11_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    suffices h: i7.val + i9.val ≤  2^ 128 - 2^102-1 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · rw[i7_post, i6_post]
      rename' __discr => discr1
      have : i9.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
        simp[i9_post, i8_post]
        have : 0< ((constants.L)[2]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rename' __discr_post_1=>  __discr1
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      have := Nat.add_lt_add (a_bounds 2 (by simp: 2<9)) this
      suffices h: discr1.1.val ≤  2^ 128 - 2^102 - 1 - 2 ^ 52 *  ((constants.L)[1]!).val  - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_le_of_le_mul
        have : ↑discr1.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
        2 ^ 52 *  ((constants.L)[0]!).val
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[i5_post]
          have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
            simp[i4_post, i3_post]
            have : 0< ((constants.L)[1]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rename' __discr_post_1=>  __discr1
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rw[i2_post]
            suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
              simp at this
              simp[i1_post]
              apply le_trans this
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rename' __discr_post_1=>  __discr1
              rename' __discr_post_2=>  __discr2
              rw[__discr_post_2]
              apply Nat.div_le_of_le_mul
              have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i.val ≤  2 ^ 52 *
                (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i_post]
                have:= (le_of_lt (a_bounds 0 (by simp : 0 < 9)))
                simp at this
                simp
                apply le_trans this
                scalar_tac
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK



    -- END TASK


  · -- BEGIN TASK
    have ineq1:= Nat.mod_lt (i12.val * constants.LFACTOR.val) (by simp: 0 < 2 ^ 52)
    have :0< (constants.L[0]!).val := by
      unfold constants.L
      decide
    have := (Nat.mul_lt_mul_right this).mpr ineq1
    suffices h: __discr.1.val ≤  2 ^128-1 - 5 * 2 ^ 124
    · -- BEGIN TASK
      have :=Nat.add_le_add h (le_of_lt (a_bounds 3 (by simp)))
      simp at this
      simp[i13_post]
      apply le_trans this
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[__discr_post_2, __discr_post_1,]
      apply Nat.div_le_of_le_mul
      suffices h: i12.val ≤  2 ^ 52 * (2 ^ 128 - 1 - 5 * 2 ^ 124) - 2 ^ 52 * (constants.L.val[0]).val
      · scalar_tac
      ·  -- BEGIN TASK
        rw[i12_post, i10_post, i11_post]
        rename' __discr => discr3
        rename' __discr_post_1 => __discr_post_3
        rename' __discr_post_2 => __discr_post_4
        have : i11.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i11_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i7.val + i9.val ≤  2^ 128 - 2^102-1 - 2 ^ 52 *  ((constants.L)[1]!).val
        · scalar_tac
        · rw[i7_post, i6_post]
          rename' __discr => discr1
          have : i9.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
            simp[i9_post, i8_post]
            have : 0< ((constants.L)[2]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rename' __discr_post_1=>  __discr1
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          have := Nat.add_lt_add (a_bounds 2 (by simp: 2<9)) this
          suffices h: discr1.1.val ≤  2^ 128 - 2^102 - 1 - 2 ^ 52 *  ((constants.L)[1]!).val  - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rw[__discr_post_2]
            apply Nat.div_le_of_le_mul
            have : ↑discr1.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val
            · -- BEGIN TASK
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[i5_post]
              have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                simp[i4_post, i3_post]
                have : 0< ((constants.L)[1]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rename' __discr_post_1=>  __discr1
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i2_post]
                suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                · -- BEGIN TASK
                  have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                  simp at this
                  simp[i1_post]
                  apply le_trans this
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  rename' __discr_post_1=>  __discr1
                  rename' __discr_post_2=>  __discr2
                  rw[__discr_post_2]
                  apply Nat.div_le_of_le_mul
                  have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                    simp
                    have : 0< ((constants.L)[0]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
                  suffices h: i.val ≤  2 ^ 52 *
                    (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                    5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                  · -- BEGIN TASK
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rw[i_post]
                    scalar_tac
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK



        -- END TASK


  · -- BEGIN TASK
    rw[i14_post, i13_post, i15_post]
    have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i15_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rename' __discr_post_1 => __discr_post_3
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    have := Nat.add_lt_add (a_bounds 3 (by simp)) this
    suffices h:  __discr.1.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
    · -- BEGIN TASK
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
            rw[__discr_post_2]
            apply Nat.div_le_of_le_mul
            have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
            2 ^ 52 *  ((constants.L)[0]!).val
            · -- BEGIN TASK
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[i5_post]
              have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                simp[i4_post, i3_post]
                have : 0< ((constants.L)[1]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rename' __discr_post_1=>  __discr1
                rename' __discr_post_1=>  __discr2
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i2_post]
                rename' __discr=>  discr1
                rename' __discr=>  discr2
                suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                · -- BEGIN TASK
                  have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                  simp at this
                  simp[i1_post]
                  apply le_trans this
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  rename' __discr_post_1=>  __discr1
                  rename' __discr_post_2=>  __discr2
                  rename' __discr_post_2=>  __discr3
                  rename' __discr_post_1=>  __discr4
                  rw[__discr_post_2]
                  apply Nat.div_le_of_le_mul
                  have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                    simp
                    have : 0< ((constants.L)[0]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
                  suffices h: i.val ≤  2 ^ 52 *
                    (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                    5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                  · -- BEGIN TASK
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rw[i_post]
                    scalar_tac
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK
   -- END TASK
  · -- BEGIN TASK
    rw[i16_post]
    have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i17_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i14_post, i13_post, i15_post]
      have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
        simp[i15_post, i8_post]
        have : 0< ((constants.L)[2]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rename' __discr_post_1 => __discr_post_3
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      have := Nat.add_lt_add (a_bounds 3 (by simp)) this
      suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_le_of_le_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
              2 ^ 52 *  ((constants.L)[0]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i5_post]
                have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                  simp[i4_post, i3_post]
                  have : 0< ((constants.L)[1]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rename' __discr_post_1=>  __discr1
                  rename' __discr_post_1=>  __discr2
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                · -- BEGIN TASK
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  rw[i2_post]
                  rename' __discr=>  discr1
                  rename' __discr=>  discr2
                  suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                  · -- BEGIN TASK
                    have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                    simp at this
                    simp[i1_post]
                    apply le_trans this
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rename' __discr_post_1=>  __discr1
                    rename' __discr_post_2=>  __discr2
                    rename' __discr_post_2=>  __discr3
                    rename' __discr_post_1=>  __discr4

                    rw[__discr_post_2]
                    apply Nat.div_le_of_le_mul
                    have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                      simp
                      have : 0< ((constants.L)[0]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i.val ≤  2 ^ 52 *
                      (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                      5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      rw[i_post]
                      scalar_tac
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    rw[i18_post,i16_post]
    have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i17_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      rw[__discr_post_1]
      apply Nat.mod_lt
      simp
    suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i14_post, i13_post, i15_post]
      have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
        simp[i15_post, i8_post]
        have : 0< ((constants.L)[2]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rename' __discr_post_1 => __discr_post_3
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      have := Nat.add_lt_add (a_bounds 3 (by simp)) this
      suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_le_of_le_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
              2 ^ 52 *  ((constants.L)[0]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i5_post]
                have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                  simp[i4_post, i3_post]
                  have : 0< ((constants.L)[1]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rename' __discr_post_1=>  __discr1
                  rename' __discr_post_1=>  __discr2
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                · -- BEGIN TASK
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  rw[i2_post]
                  rename' __discr=>  discr1
                  rename' __discr=>  discr2
                  suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                  · -- BEGIN TASK
                    have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                    simp at this
                    simp[i1_post]
                    apply le_trans this
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rename' __discr_post_1=>  __discr1
                    rename' __discr_post_2=>  __discr2
                    rename' __discr_post_2=>  __discr3
                    rename' __discr_post_1=>  __discr4

                    rw[__discr_post_2]
                    apply Nat.div_le_of_le_mul
                    have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                      simp
                      have : 0< ((constants.L)[0]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i.val ≤  2 ^ 52 *
                      (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                      5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      rw[i_post]
                      scalar_tac
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    suffices h: __discr.1.val < 2 ^ 128 - 5 * 2 ^ 124
    · -- BEGIN TASK
      rw[i19_post]
      expand a_bounds with 5
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[__discr_post_2]
      apply Nat.div_lt_of_lt_mul
      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
        simp
        have : 0< ((constants.L)[0]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        rw[__discr_post_1]
        apply Nat.mod_lt
        simp
      suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
              2 ^ 52 *  ((constants.L)[0]!).val - 2
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[i18_post,i16_post]
        clear this i19_post __discr_post_2 __discr_post_1
        rename' __discr => discr0
        have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i17_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
        · scalar_tac
        · -- BEGIN TASK
          rw[i14_post, i13_post, i15_post]
          have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
            simp[i15_post, i8_post]
            have : 0< ((constants.L)[2]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rename' __discr_post_1 => __discr_post_3
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          have := Nat.add_lt_add (a_bounds 3 (by simp)) this
          suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
                  rw[__discr_post_2]
                  apply Nat.div_le_of_le_mul
                  have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                    simp
                    have : 0< ((constants.L)[0]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
                  suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                  2 ^ 52 *  ((constants.L)[0]!).val
                  · -- BEGIN TASK
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rw[i5_post]
                    have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                      simp[i4_post, i3_post]
                      have : 0< ((constants.L)[1]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rename' __discr_post_1=>  __discr1
                      rename' __discr_post_1=>  __discr2
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      rw[i2_post]
                      rename' __discr=>  discr1
                      rename' __discr=>  discr2
                      suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                      · -- BEGIN TASK
                        have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                        simp at this
                        simp[i1_post]
                        apply le_trans this
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                        rename' __discr_post_1=>  __discr1
                        rename' __discr_post_2=>  __discr2
                        rename' __discr_post_2=>  __discr3
                        rename' __discr_post_1=>  __discr4

                        rw[__discr_post_2]
                        apply Nat.div_le_of_le_mul
                        have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                          simp
                          have : 0< ((constants.L)[0]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          rw[__discr_post_1]
                          apply Nat.mod_lt
                          simp
                        suffices h: i.val ≤  2 ^ 52 *
                          (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                          5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                        · -- BEGIN TASK
                          scalar_tac
                          -- END TASK
                        · -- BEGIN TASK
                          rw[i_post]
                          scalar_tac
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK
        -- END TASK

      -- END TASK


    -- END TASK
  · -- BEGIN TASK
    rw[i20_post]
    have : i22.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
      simp[i22_post, i21_post]
      have : 0< ((constants.L)[4]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: __discr.1.val + i19.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
    · scalar_tac
    · -- BEGIN TASK
      suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
      · -- BEGIN TASK
        rw[i19_post]
        expand a_bounds with 5
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_lt_of_lt_mul
        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                2 ^ 52 *  ((constants.L)[0]!).val - 2
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[i18_post,i16_post]
          clear this i19_post __discr_post_2 __discr_post_1
          rename' __discr => discr0
          have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
            simp[i17_post, i3_post]
            have : 0< ((constants.L)[1]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
          · scalar_tac
          · -- BEGIN TASK
            rw[i14_post, i13_post, i15_post]
            have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
              simp[i15_post, i8_post]
              have : 0< ((constants.L)[2]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rename' __discr_post_1 => __discr_post_3
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            have := Nat.add_lt_add (a_bounds 3 (by simp)) this
            suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
            · -- BEGIN TASK
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
                    rw[__discr_post_2]
                    apply Nat.div_le_of_le_mul
                    have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                      simp
                      have : 0< ((constants.L)[0]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                    2 ^ 52 *  ((constants.L)[0]!).val
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      rw[i5_post]
                      have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                        simp[i4_post, i3_post]
                        have : 0< ((constants.L)[1]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rename' __discr_post_1=>  __discr1
                        rename' __discr_post_1=>  __discr2
                        rw[__discr_post_1]
                        apply Nat.mod_lt
                        simp
                      suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                        2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                        rw[i2_post]
                        rename' __discr=>  discr1
                        rename' __discr=>  discr2
                        suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                        2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                        · -- BEGIN TASK
                          have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                          simp at this
                          simp[i1_post]
                          apply le_trans this
                          scalar_tac
                          -- END TASK
                        · -- BEGIN TASK
                          rename' __discr_post_1=>  __discr1
                          rename' __discr_post_2=>  __discr2
                          rename' __discr_post_2=>  __discr3
                          rename' __discr_post_1=>  __discr4

                          rw[__discr_post_2]
                          apply Nat.div_le_of_le_mul
                          have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                            simp
                            have : 0< ((constants.L)[0]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rw[__discr_post_1]
                            apply Nat.mod_lt
                            simp
                          suffices h: i.val ≤  2 ^ 52 *
                            (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                            5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                          · -- BEGIN TASK
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                            rw[i_post]
                            scalar_tac
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK
          -- END TASK

        -- END TASK


      -- END TASK




    -- END TASK
  · -- BEGIN TASK
    rw[i23_post]
    have : i24.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i24_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp
    suffices h: i20.val + i22.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i20_post]
      have : i22.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
        simp[i22_post, i21_post]
        have : 0< ((constants.L)[4]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        simp_all
        apply Nat.mod_lt
        simp

      suffices h: __discr.1.val + i19.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
      · scalar_tac
      · -- BEGIN TASK
        suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
        · -- BEGIN TASK
          rw[i19_post]
          expand a_bounds with 5
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[__discr_post_2]
          apply Nat.div_lt_of_lt_mul
          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                    simp
                    have : 0< ((constants.L)[0]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
          suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                  2 ^ 52 *  ((constants.L)[0]!).val - 2
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rw[i18_post,i16_post]
            clear this i19_post __discr_post_2 __discr_post_1
            rename' __discr => discr0
            have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
              simp[i17_post, i3_post]
              have : 0< ((constants.L)[1]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
            · scalar_tac
            · -- BEGIN TASK
              rw[i14_post, i13_post, i15_post]
              have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                simp[i15_post, i8_post]
                have : 0< ((constants.L)[2]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rename' __discr_post_1 => __discr_post_3
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              have := Nat.add_lt_add (a_bounds 3 (by simp)) this
              suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                      rw[__discr_post_2]
                      apply Nat.div_le_of_le_mul
                      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                        simp
                        have : 0< ((constants.L)[0]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rw[__discr_post_1]
                        apply Nat.mod_lt
                        simp
                      suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                      2 ^ 52 *  ((constants.L)[0]!).val
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                        rw[i5_post]
                        have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                          simp[i4_post, i3_post]
                          have : 0< ((constants.L)[1]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          rename' __discr_post_1=>  __discr1
                          rename' __discr_post_1=>  __discr2
                          rw[__discr_post_1]
                          apply Nat.mod_lt
                          simp
                        suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                        · -- BEGIN TASK
                          scalar_tac
                          -- END TASK
                        · -- BEGIN TASK
                          rw[i2_post]
                          rename' __discr=>  discr1
                          rename' __discr=>  discr2
                          suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                          · -- BEGIN TASK
                            have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                            simp at this
                            simp[i1_post]
                            apply le_trans this
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                            rename' __discr_post_1=>  __discr1
                            rename' __discr_post_2=>  __discr2
                            rename' __discr_post_2=>  __discr3
                            rename' __discr_post_1=>  __discr4
                            rw[__discr_post_2]
                            apply Nat.div_le_of_le_mul
                            have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                              simp
                              have : 0< ((constants.L)[0]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              rw[__discr_post_1]
                              apply Nat.mod_lt
                              simp
                            suffices h: i.val ≤  2 ^ 52 *
                              (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                              5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                            · -- BEGIN TASK
                              scalar_tac
                              -- END TASK
                            · -- BEGIN TASK
                              rw[i_post]
                              scalar_tac
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK
              -- END TASK
            -- END TASK

          -- END TASK


        -- END TASK




      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    rw[i25_post]
    have : i26.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i26_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp
    suffices h: i23.val + i24.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · -- BEGIN TASK
        rw[i23_post]
        have : i24.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
          simp[i24_post, i8_post]
          have : 0< ((constants.L)[2]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp
        suffices h: i20.val + i22.val ≤ 2 ^ 128 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
        · scalar_tac
        · -- BEGIN TASK
          rw[i20_post]
          have : i22.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
            simp[i22_post, i21_post]
            have : 0< ((constants.L)[4]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp
          suffices h: __discr.1.val + i19.val ≤ 2 ^ 128 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
          · scalar_tac
          · -- BEGIN TASK
            suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              rw[i19_post]
              expand a_bounds with 5
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_lt_of_lt_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                      2 ^ 52 *  ((constants.L)[0]!).val - 2
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i18_post,i16_post]
                clear this i19_post __discr_post_2 __discr_post_1
                rename' __discr => discr0
                have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                  simp[i17_post, i3_post]
                  have : 0< ((constants.L)[1]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
                · scalar_tac
                · -- BEGIN TASK
                  rw[i14_post, i13_post, i15_post]
                  have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                    simp[i15_post, i8_post]
                    have : 0< ((constants.L)[2]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rename' __discr_post_1 => __discr_post_3
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
                  have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                  suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                  · -- BEGIN TASK
                    have :=Nat.add_le_add h (le_of_lt this)
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                          rw[__discr_post_2]
                          apply Nat.div_le_of_le_mul
                          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                            simp
                            have : 0< ((constants.L)[0]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rw[__discr_post_1]
                            apply Nat.mod_lt
                            simp
                          suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[0]!).val
                          · -- BEGIN TASK
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                            rw[i5_post]
                            have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                              simp[i4_post, i3_post]
                              have : 0< ((constants.L)[1]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              rename' __discr_post_1=>  __discr1
                              rename' __discr_post_1=>  __discr2
                              rw[__discr_post_1]
                              apply Nat.mod_lt
                              simp
                            suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                            · -- BEGIN TASK
                              scalar_tac
                              -- END TASK
                            · -- BEGIN TASK
                              rw[i2_post]
                              rename' __discr=>  discr1
                              rename' __discr=>  discr2
                              suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                              · -- BEGIN TASK
                                have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                simp at this
                                simp[i1_post]
                                apply le_trans this
                                scalar_tac
                                -- END TASK
                              · -- BEGIN TASK
                                rename' __discr_post_1=>  __discr1
                                rename' __discr_post_2=>  __discr2
                                rename' __discr_post_2=>  __discr3
                                rename' __discr_post_1=>  __discr4

                                rw[__discr_post_2]
                                apply Nat.div_le_of_le_mul
                                have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                  simp
                                  have : 0< ((constants.L)[0]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rw[__discr_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i.val ≤  2 ^ 52 *
                                  (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                  5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                · -- BEGIN TASK
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                  rw[i_post]
                                  scalar_tac
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK

              -- END TASK


            -- END TASK




          -- END TASK
        -- END TASK

    -- END TASK
  · -- BEGIN TASK
    rw[i27_post, i25_post]
    have : i26.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i26_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: i23.val + i24.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · -- BEGIN TASK
        rw[i23_post]
        have : i24.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
          simp[i24_post, i8_post]
          have : 0< ((constants.L)[2]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp
        suffices h: i20.val + i22.val ≤ 2 ^ 128 - 2 ^ 102 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
        · scalar_tac
        · -- BEGIN TASK
          rw[i20_post]
          have : i22.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
            simp[i22_post, i21_post]
            have : 0< ((constants.L)[4]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp

          suffices h: __discr.1.val + i19.val ≤ 2 ^ 128 - 2 ^ 102 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
          · scalar_tac
          · -- BEGIN TASK
            suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              rw[i19_post]
              expand a_bounds with 5
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_lt_of_lt_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                      2 ^ 52 *  ((constants.L)[0]!).val - 2
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[i18_post,i16_post]
                clear this i19_post __discr_post_2 __discr_post_1
                rename' __discr => discr0
                have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                  simp[i17_post, i3_post]
                  have : 0< ((constants.L)[1]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
                · scalar_tac
                · -- BEGIN TASK
                  rw[i14_post, i13_post, i15_post]
                  have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                    simp[i15_post, i8_post]
                    have : 0< ((constants.L)[2]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    rename' __discr_post_1 => __discr_post_3
                    rw[__discr_post_1]
                    apply Nat.mod_lt
                    simp
                  have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                  suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                  · -- BEGIN TASK
                    have :=Nat.add_le_add h (le_of_lt this)
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                          rw[__discr_post_2]
                          apply Nat.div_le_of_le_mul
                          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                            simp
                            have : 0< ((constants.L)[0]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rw[__discr_post_1]
                            apply Nat.mod_lt
                            simp
                          suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[0]!).val
                          · -- BEGIN TASK
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                            rw[i5_post]
                            have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                              simp[i4_post, i3_post]
                              have : 0< ((constants.L)[1]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              rename' __discr_post_1=>  __discr1
                              rename' __discr_post_1=>  __discr2
                              rw[__discr_post_1]
                              apply Nat.mod_lt
                              simp
                            suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                            · -- BEGIN TASK
                              scalar_tac
                              -- END TASK
                            · -- BEGIN TASK
                              rw[i2_post]
                              rename' __discr=>  discr1
                              rename' __discr=>  discr2
                              suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                              · -- BEGIN TASK
                                have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                simp at this
                                simp[i1_post]
                                apply le_trans this
                                scalar_tac
                                -- END TASK
                              · -- BEGIN TASK
                                rename' __discr_post_1=>  __discr1
                                rename' __discr_post_2=>  __discr2
                                rename' __discr_post_2=>  __discr3
                                rename' __discr_post_1=>  __discr4

                                rw[__discr_post_2]
                                apply Nat.div_le_of_le_mul
                                have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                  simp
                                  have : 0< ((constants.L)[0]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rw[__discr_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i.val ≤  2 ^ 52 *
                                  (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                  5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                · -- BEGIN TASK
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                  rw[i_post]
                                  scalar_tac
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK
                  -- END TASK
                -- END TASK

              -- END TASK


            -- END TASK




          -- END TASK
        -- END TASK

    -- END TASK

  · -- BEGIN TASK
    suffices h: __discr.1.val < 2 ^ 128 - 5 * 2 ^ 124
    · -- BEGIN TASK
      rw[i28_post]
      expand a_bounds with 9
      scalar_tac
      -- END TASK
    · -- BEGIN TASK
      rw[__discr_post_2]
      apply Nat.div_lt_of_lt_mul
      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
      suffices h: i27.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
              2 ^ 52 *  ((constants.L)[0]!).val - 2
      · -- BEGIN TASK
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[i27_post, i25_post]
        have : i26.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i26_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp

        suffices h: i23.val + i24.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
        · scalar_tac
        · -- BEGIN TASK
            rw[i23_post]
            have : i24.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
              simp[i24_post, i8_post]
              have : 0< ((constants.L)[2]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              simp_all
              apply Nat.mod_lt
              simp
            suffices h: i20.val + i22.val ≤ 2 ^ 128 - 2 ^ 102 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
            · scalar_tac
            · -- BEGIN TASK
              rw[i20_post]
              have : i22.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                simp[i22_post, i21_post]
                have : 0< ((constants.L)[4]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                simp_all
                apply Nat.mod_lt
                simp
              rename' __discr => discr00
              rename' __discr_post_1 => discr00_post_1
              rename' __discr_post_2 => discr00_post_2
              suffices h: __discr.1.val + i19.val ≤ 2 ^ 128 - 2 ^ 102 - 2 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
              · scalar_tac
              · -- BEGIN TASK
                suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                · -- BEGIN TASK
                  rw[i19_post]
                  expand a_bounds with 5
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  rw[__discr_post_2]
                  apply Nat.div_lt_of_lt_mul
                  have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                            simp
                            have : 0< ((constants.L)[0]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rw[__discr_post_1]
                            apply Nat.mod_lt
                            simp
                  suffices h: i18.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                          2 ^ 52 *  ((constants.L)[0]!).val - 2
                  · -- BEGIN TASK
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rw[i18_post,i16_post]
                    clear this i19_post __discr_post_2 __discr_post_1
                    rename' __discr => discr0
                    have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                      simp[i17_post, i3_post]
                      have : 0< ((constants.L)[1]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i14.val + i15.val ≤ 2 ^ 128 - 2 ^ 102 - 2 ^ 52 *  ((constants.L)[1]!).val
                    · scalar_tac
                    · -- BEGIN TASK
                      rw[i14_post, i13_post, i15_post]
                      have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                        simp[i15_post, i8_post]
                        have : 0< ((constants.L)[2]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rename' __discr_post_1 => __discr_post_3
                        rw[__discr_post_1]
                        apply Nat.mod_lt
                        simp
                      have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                      suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                              rw[__discr_post_2]
                              apply Nat.div_le_of_le_mul
                              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                simp
                                have : 0< ((constants.L)[0]!).val := by
                                  unfold constants.L
                                  decide
                                simp at this
                                apply (Nat.mul_lt_mul_right this).mpr
                                rw[__discr_post_1]
                                apply Nat.mod_lt
                                simp
                              suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val
                              · -- BEGIN TASK
                                scalar_tac
                                -- END TASK
                              · -- BEGIN TASK
                                rw[i5_post]
                                have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                  simp[i4_post, i3_post]
                                  have : 0< ((constants.L)[1]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rename' __discr_post_1=>  __discr1
                                  rename' __discr_post_1=>  __discr2
                                  rw[__discr_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                · -- BEGIN TASK
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                  rw[i2_post]
                                  rename' __discr=>  discr1
                                  rename' __discr=>  discr2
                                  suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                  · -- BEGIN TASK
                                    have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                    simp at this
                                    simp[i1_post]
                                    apply le_trans this
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                    rename' __discr_post_1=>  __discr1
                                    rename' __discr_post_2=>  __discr2
                                    rename' __discr_post_2=>  __discr3
                                    rename' __discr_post_1=>  __discr4

                                    rw[__discr_post_2]
                                    apply Nat.div_le_of_le_mul
                                    have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                      simp
                                      have : 0< ((constants.L)[0]!).val := by
                                        unfold constants.L
                                        decide
                                      simp at this
                                      apply (Nat.mul_lt_mul_right this).mpr
                                      rw[__discr_post_1]
                                      apply Nat.mod_lt
                                      simp
                                    suffices h: i.val ≤  2 ^ 52 *
                                      (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                      5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                    · -- BEGIN TASK
                                      scalar_tac
                                      -- END TASK
                                    · -- BEGIN TASK
                                      rw[i_post]
                                      scalar_tac
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK

                  -- END TASK


                -- END TASK




              -- END TASK
            -- END TASK

        -- END TASK



    -- END TASK
  · -- BEGIN TASK
    rw[i29_post]
    have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
      simp[i30_post, i21_post]
      have : 0< ((constants.L)[4]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: ↑__discr.1 + i28.val ≤ 2 ^ 128 - 1 - 2 ^ 52 *  ((constants.L)[4]!).val
    · scalar_tac
    · -- BEGIN TASK
      suffices h: ↑__discr.1  ≤ 2 ^ 128 - 1 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
      · expand a_bounds with 9
        scalar_tac
      · -- BEGIN TASK
        rw[__discr_post_2, __discr_post_1]
        apply Nat.div_le_of_le_mul
        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i18.val ≤  2 ^ 128 - 1 -
            2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
                    rw[i18_post,i16_post]
                    clear this i19_post __discr_post_2 __discr_post_1
                    rename' __discr => discr0
                    rename' __discr => discr1
                    rename' __discr => discr2
                    rename' __discr_post_2 => __discr1_post_2
                    rename' __discr_post_2 => __discr2_post_2
                    rename' __discr_post_1 => __discr1_post_1
                    rename' __discr_post_1 => __discr2_post_1
                    have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                      simp[i17_post, i3_post]
                      have : 0< ((constants.L)[1]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr2_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i14.val + i15.val ≤ 2 ^ 128 - 1 -
                      2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                      2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                    · scalar_tac
                    · -- BEGIN TASK
                      rw[i14_post, i13_post, i15_post]
                      have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                        simp[i15_post, i8_post]
                        have : 0< ((constants.L)[2]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rename' __discr_post_1 => __discr_post_3
                        rw[__discr_post_3]
                        apply Nat.mod_lt
                        simp
                      have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                      suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                              rename' __discr_post_2 => h_discr_post_2
                              rename' __discr_post_2 => h_discr_post_3
                              rw[h_discr_post_2]
                              apply Nat.div_le_of_le_mul
                              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                simp
                                have : 0< ((constants.L)[0]!).val := by
                                  unfold constants.L
                                  decide
                                simp at this
                                apply (Nat.mul_lt_mul_right this).mpr
                                rw[__discr_post_1]
                                apply Nat.mod_lt
                                simp
                              suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[0]!).val
                              · -- BEGIN TASK
                                have := Nat.add_le_add h (le_of_lt this)
                                simp at this
                                scalar_tac
                                -- END TASK
                              · -- BEGIN TASK
                                rw[i5_post]
                                have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                  simp[i4_post, i3_post]
                                  have : 0< ((constants.L)[1]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rename' __discr_post_1=>  __discr1
                                  rename' __discr_post_1=>  __discr2
                                  rw[__discr2]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                · -- BEGIN TASK
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                  rw[i2_post]
                                  rename' __discr=>  discr1
                                  suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                  · -- BEGIN TASK
                                    have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                    simp at this
                                    simp[i1_post]
                                    apply le_trans this
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                    rename' __discr_post_1=>  __discr1
                                    rename' __discr_post_1=>  __discr4

                                    rw[h_discr_post_3]
                                    apply Nat.div_le_of_le_mul
                                    have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                      simp
                                      have : 0< ((constants.L)[0]!).val := by
                                        unfold constants.L
                                        decide
                                      simp at this
                                      apply (Nat.mul_lt_mul_right this).mpr
                                      rw[__discr4]
                                      apply Nat.mod_lt
                                      simp
                                    suffices h: i.val ≤  2 ^ 52 *
                                      (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                      5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                    · -- BEGIN TASK
                                      scalar_tac
                                      -- END TASK
                                    · -- BEGIN TASK
                                      rw[i_post]
                                      scalar_tac
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK
                    -- END TASK

                  -- END TASK


        -- END TASK
      -- END TASK
    -- END TASK
    -- END TASK
  · -- BEGIN TASK
    rw[i31_post]
    have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i32_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp
    suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i29_post]
      have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
        simp[i30_post, i21_post]
        have : 0< ((constants.L)[4]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        simp_all
        apply Nat.mod_lt
        simp

      suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
      · scalar_tac
      · -- BEGIN TASK
        suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
        · expand a_bounds with 9
          scalar_tac
        · -- BEGIN TASK
          rw[__discr_post_2, __discr_post_1]
          apply Nat.div_le_of_le_mul
          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
            simp
            have : 0< ((constants.L)[0]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val -
              2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
                      rw[i18_post,i16_post]
                      clear this i19_post __discr_post_2 __discr_post_1
                      rename' __discr => discr0
                      rename' __discr => discr1
                      rename' __discr => discr2
                      rename' __discr_post_2 => __discr1_post_2
                      rename' __discr_post_2 => __discr2_post_2
                      rename' __discr_post_1 => __discr1_post_1
                      rename' __discr_post_1 => __discr2_post_1
                      have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                        simp[i17_post, i3_post]
                        have : 0< ((constants.L)[1]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rw[__discr2_post_1]
                        apply Nat.mod_lt
                        simp
                      suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val -
                        2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                        2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                      · scalar_tac
                      · -- BEGIN TASK
                        rw[i14_post, i13_post, i15_post]
                        have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                          simp[i15_post, i8_post]
                          have : 0< ((constants.L)[2]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          rename' __discr_post_1 => __discr_post_3
                          rw[__discr_post_3]
                          apply Nat.mod_lt
                          simp
                        have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                        suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                        · -- BEGIN TASK
                          scalar_tac
                          -- END TASK
                        · -- BEGIN TASK
                                rename' __discr_post_2 => h_discr_post_2
                                rename' __discr_post_2 => h_discr_post_3
                                rw[h_discr_post_2]
                                apply Nat.div_le_of_le_mul
                                have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                  simp
                                  have : 0< ((constants.L)[0]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rw[__discr_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                2 ^ 52 *  ((constants.L)[0]!).val
                                · -- BEGIN TASK
                                  have := Nat.add_le_add h (le_of_lt this)
                                  simp at this
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                  rw[i5_post]
                                  have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                    simp[i4_post, i3_post]
                                    have : 0< ((constants.L)[1]!).val := by
                                      unfold constants.L
                                      decide
                                    simp at this
                                    apply (Nat.mul_lt_mul_right this).mpr
                                    rename' __discr_post_1=>  __discr1
                                    rename' __discr_post_1=>  __discr2
                                    rw[__discr2]
                                    apply Nat.mod_lt
                                    simp
                                  suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                    2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                  · -- BEGIN TASK
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                    rw[i2_post]
                                    rename' __discr=>  discr1
                                    suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                    2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                    · -- BEGIN TASK
                                      have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                      simp at this
                                      simp[i1_post]
                                      apply le_trans this
                                      scalar_tac
                                      -- END TASK
                                    · -- BEGIN TASK
                                      rename' __discr_post_1=>  __discr1
                                      rename' __discr_post_1=>  __discr4

                                      rw[h_discr_post_3]
                                      apply Nat.div_le_of_le_mul
                                      have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                        simp
                                        have : 0< ((constants.L)[0]!).val := by
                                          unfold constants.L
                                          decide
                                        simp at this
                                        apply (Nat.mul_lt_mul_right this).mpr
                                        rw[__discr4]
                                        apply Nat.mod_lt
                                        simp
                                      suffices h: i.val ≤  2 ^ 52 *
                                        (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                        5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                      · -- BEGIN TASK
                                        scalar_tac
                                        -- END TASK
                                      · -- BEGIN TASK
                                        rw[i_post]
                                        scalar_tac
                                        -- END TASK
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK
                      -- END TASK

                    -- END TASK


          -- END TASK
        -- END TASK
      -- END TASK
      -- END TASK



    -- END TASK
  · -- BEGIN TASK
    rw[i33_post]
    have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
      simp[i34_post, i3_post]
      have : 0< ((constants.L)[1]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp
    suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i31_post]
      have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
        simp[i32_post, i8_post]
        have : 0< ((constants.L)[2]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        simp_all
        apply Nat.mod_lt
        simp
      suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
      · scalar_tac
      · -- BEGIN TASK
        rw[i29_post]
        have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
          simp[i30_post, i21_post]
          have : 0< ((constants.L)[4]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp

        suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
        · scalar_tac
        · -- BEGIN TASK
          suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
          · expand a_bounds with 9
            scalar_tac
          · -- BEGIN TASK
            rw[__discr_post_2, __discr_post_1]
            apply Nat.div_le_of_le_mul
            have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
            · -- BEGIN TASK
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
                        rw[i18_post,i16_post]
                        clear this i19_post __discr_post_2 __discr_post_1
                        rename' __discr => discr0
                        rename' __discr => discr1
                        rename' __discr => discr2
                        rename' __discr_post_2 => __discr1_post_2
                        rename' __discr_post_2 => __discr2_post_2
                        rename' __discr_post_1 => __discr1_post_1
                        rename' __discr_post_1 => __discr2_post_1
                        have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                          simp[i17_post, i3_post]
                          have : 0< ((constants.L)[1]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          rw[__discr2_post_1]
                          apply Nat.mod_lt
                          simp
                        suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                          2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                        · scalar_tac
                        · -- BEGIN TASK
                          rw[i14_post, i13_post, i15_post]
                          have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                            simp[i15_post, i8_post]
                            have : 0< ((constants.L)[2]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rename' __discr_post_1 => __discr_post_3
                            rw[__discr_post_3]
                            apply Nat.mod_lt
                            simp
                          have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                          suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                          · -- BEGIN TASK
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                                  rename' __discr_post_2 => h_discr_post_2
                                  rename' __discr_post_2 => h_discr_post_3
                                  rw[h_discr_post_2]
                                  apply Nat.div_le_of_le_mul
                                  have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                    simp
                                    have : 0< ((constants.L)[0]!).val := by
                                      unfold constants.L
                                      decide
                                    simp at this
                                    apply (Nat.mul_lt_mul_right this).mpr
                                    rw[__discr_post_1]
                                    apply Nat.mod_lt
                                    simp
                                  suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[0]!).val
                                  · -- BEGIN TASK
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                    rw[i5_post]
                                    have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                      simp[i4_post, i3_post]
                                      have : 0< ((constants.L)[1]!).val := by
                                        unfold constants.L
                                        decide
                                      simp at this
                                      apply (Nat.mul_lt_mul_right this).mpr
                                      rename' __discr_post_1=>  __discr1
                                      rename' __discr_post_1=>  __discr2
                                      rw[__discr2]
                                      apply Nat.mod_lt
                                      simp
                                    suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                    · -- BEGIN TASK
                                      scalar_tac
                                      -- END TASK
                                    · -- BEGIN TASK
                                      rw[i2_post]
                                      rename' __discr=>  discr1
                                      suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                      · -- BEGIN TASK
                                        have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                        simp at this
                                        simp[i1_post]
                                        apply le_trans this
                                        scalar_tac
                                        -- END TASK
                                      · -- BEGIN TASK
                                        rename' __discr_post_1=>  __discr1
                                        rename' __discr_post_1=>  __discr4

                                        rw[h_discr_post_3]
                                        apply Nat.div_le_of_le_mul
                                        have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                          simp
                                          have : 0< ((constants.L)[0]!).val := by
                                            unfold constants.L
                                            decide
                                          simp at this
                                          apply (Nat.mul_lt_mul_right this).mpr
                                          rw[__discr4]
                                          apply Nat.mod_lt
                                          simp
                                        suffices h: i.val ≤  2 ^ 52 *
                                          (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                          5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                        · -- BEGIN TASK
                                          scalar_tac
                                          -- END TASK
                                        · -- BEGIN TASK
                                          rw[i_post]
                                          scalar_tac
                                          -- END TASK
                                        -- END TASK
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK
                          -- END TASK
                        -- END TASK

                      -- END TASK


            -- END TASK
          -- END TASK
        -- END TASK
        -- END TASK



      -- END TASK

    -- END TASK
  · -- BEGIN TASK
    suffices h: __discr.1.val < 2 ^128 - 5 * 2 ^ 124
    · expand a_bounds with 9; scalar_tac
    · rw[__discr_post_2]
      apply Nat.div_lt_of_lt_mul
      suffices h: i33.val + i34.val < 2 ^ 128
      · rw[i35_post];scalar_tac
      · -- BEGIN TASK
        rw[i33_post]
        have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
          simp[i34_post, i3_post]
          have : 0< ((constants.L)[1]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp
        suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
        · scalar_tac
        · -- BEGIN TASK
          clear this __discr_post_1 __discr_post_2
          rename' __discr => x
          rw[i31_post]
          have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
            simp[i32_post, i8_post]
            have : 0< ((constants.L)[2]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp
          suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
          · scalar_tac
          · -- BEGIN TASK
            rw[i29_post]
            have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
              simp[i30_post, i21_post]
              have : 0< ((constants.L)[4]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              simp_all
              apply Nat.mod_lt
              simp

            suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
            · scalar_tac
            · -- BEGIN TASK
              suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
              · expand a_bounds with 9
                scalar_tac
              · -- BEGIN TASK
                rw[__discr_post_2, __discr_post_1]
                apply Nat.div_le_of_le_mul
                have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                  simp
                  have : 0< ((constants.L)[0]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                    2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                · -- BEGIN TASK
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                            rw[i18_post,i16_post]
                            clear this i19_post __discr_post_2 __discr_post_1
                            rename' __discr => discr0
                            rename' __discr => discr1
                            rename' __discr => discr2
                            rename' __discr_post_2 => __discr1_post_2
                            rename' __discr_post_2 => __discr2_post_2
                            rename' __discr_post_1 => __discr1_post_1
                            rename' __discr_post_1 => __discr2_post_1
                            have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                              simp[i17_post, i3_post]
                              have : 0< ((constants.L)[1]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              rw[__discr2_post_1]
                              apply Nat.mod_lt
                              simp
                            suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                              2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                            · scalar_tac
                            · -- BEGIN TASK
                              rw[i14_post, i13_post, i15_post]
                              have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                simp[i15_post, i8_post]
                                have : 0< ((constants.L)[2]!).val := by
                                  unfold constants.L
                                  decide
                                simp at this
                                apply (Nat.mul_lt_mul_right this).mpr
                                rename' __discr_post_1 => __discr_post_3
                                rw[__discr_post_3]
                                apply Nat.mod_lt
                                simp
                              have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                              suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                              · -- BEGIN TASK
                                scalar_tac
                                -- END TASK
                              · -- BEGIN TASK
                                      rename' __discr_post_2 => h_discr_post_2
                                      rename' __discr_post_2 => h_discr_post_3
                                      rw[h_discr_post_2]
                                      apply Nat.div_le_of_le_mul
                                      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                        simp
                                        have : 0< ((constants.L)[0]!).val := by
                                          unfold constants.L
                                          decide
                                        simp at this
                                        apply (Nat.mul_lt_mul_right this).mpr
                                        rw[__discr_post_1]
                                        apply Nat.mod_lt
                                        simp
                                      suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                      2 ^ 52 *  ((constants.L)[0]!).val
                                      · -- BEGIN TASK
                                        scalar_tac
                                        -- END TASK
                                      · -- BEGIN TASK
                                        rw[i5_post]
                                        have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                          simp[i4_post, i3_post]
                                          have : 0< ((constants.L)[1]!).val := by
                                            unfold constants.L
                                            decide
                                          simp at this
                                          apply (Nat.mul_lt_mul_right this).mpr
                                          rename' __discr_post_1=>  __discr1
                                          rename' __discr_post_1=>  __discr2
                                          rw[__discr2]
                                          apply Nat.mod_lt
                                          simp
                                        suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                        · -- BEGIN TASK
                                          scalar_tac
                                          -- END TASK
                                        · -- BEGIN TASK
                                          rw[i2_post]
                                          rename' __discr=>  discr1
                                          suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                          · -- BEGIN TASK
                                            have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                            simp at this
                                            simp[i1_post]
                                            apply le_trans this
                                            scalar_tac
                                            -- END TASK
                                          · -- BEGIN TASK
                                            rename' __discr_post_1=>  __discr1
                                            rename' __discr_post_1=>  __discr4

                                            rw[h_discr_post_3]
                                            apply Nat.div_le_of_le_mul
                                            have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                              simp
                                              have : 0< ((constants.L)[0]!).val := by
                                                unfold constants.L
                                                decide
                                              simp at this
                                              apply (Nat.mul_lt_mul_right this).mpr
                                              rw[__discr4]
                                              apply Nat.mod_lt
                                              simp
                                            suffices h: i.val ≤  2 ^ 52 *
                                              (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                              5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                            · -- BEGIN TASK
                                              scalar_tac
                                              -- END TASK
                                            · -- BEGIN TASK
                                              rw[i_post]
                                              scalar_tac
                                              -- END TASK
                                            -- END TASK
                                          -- END TASK
                                        -- END TASK
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK
                              -- END TASK
                            -- END TASK

                          -- END TASK


                -- END TASK
              -- END TASK
            -- END TASK
            -- END TASK



          -- END TASK

        -- END TASK



    -- END TASK
  · -- BEGIN TASK
    rw[i37_post]
    have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
      simp[i38_post, i21_post]
      have : 0< ((constants.L)[4]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: __discr.1.val + i36.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
    · scalar_tac
    · -- BEGIN TASK
      suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
      · -- BEGIN TASK
        rw[i36_post]
        expand a_bounds with 9
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_lt_of_lt_mul
        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                2 ^ 52 *  ((constants.L)[0]!).val - 2
        · -- BEGIN TASK
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          suffices h: i33.val + i34.val < 2 ^ 128
          · rw[i35_post];scalar_tac
          · -- BEGIN TASK
            rw[i33_post]
            have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
              simp[i34_post, i3_post]
              have : 0< ((constants.L)[1]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              simp_all
              apply Nat.mod_lt
              simp
            suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
            · scalar_tac
            · -- BEGIN TASK
              clear this __discr_post_1 __discr_post_2
              rename' __discr => x
              rw[i31_post]
              have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                simp[i32_post, i8_post]
                have : 0< ((constants.L)[2]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                simp_all
                apply Nat.mod_lt
                simp
              suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
              · scalar_tac
              · -- BEGIN TASK
                rw[i29_post]
                have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                  simp[i30_post, i21_post]
                  have : 0< ((constants.L)[4]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  simp_all
                  apply Nat.mod_lt
                  simp

                suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                · scalar_tac
                · -- BEGIN TASK
                  suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                  · expand a_bounds with 9
                    scalar_tac
                  · -- BEGIN TASK
                    rw[__discr_post_2, __discr_post_1]
                    apply Nat.div_le_of_le_mul
                    have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                      simp
                      have : 0< ((constants.L)[0]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                        2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                                rw[i18_post,i16_post]
                                clear this i19_post __discr_post_2 __discr_post_1
                                rename' __discr => discr0
                                rename' __discr => discr1
                                rename' __discr => discr2
                                rename' __discr_post_2 => __discr1_post_2
                                rename' __discr_post_2 => __discr2_post_2
                                rename' __discr_post_1 => __discr1_post_1
                                rename' __discr_post_1 => __discr2_post_1
                                have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                  simp[i17_post, i3_post]
                                  have : 0< ((constants.L)[1]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rw[__discr2_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                  2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                  2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                · scalar_tac
                                · -- BEGIN TASK
                                  rw[i14_post, i13_post, i15_post]
                                  have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                    simp[i15_post, i8_post]
                                    have : 0< ((constants.L)[2]!).val := by
                                      unfold constants.L
                                      decide
                                    simp at this
                                    apply (Nat.mul_lt_mul_right this).mpr
                                    rename' __discr_post_1 => __discr_post_3
                                    rw[__discr_post_3]
                                    apply Nat.mod_lt
                                    simp
                                  have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                  suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                  · -- BEGIN TASK
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                          rename' __discr_post_2 => h_discr_post_2
                                          rename' __discr_post_2 => h_discr_post_3
                                          rw[h_discr_post_2]
                                          apply Nat.div_le_of_le_mul
                                          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                            simp
                                            have : 0< ((constants.L)[0]!).val := by
                                              unfold constants.L
                                              decide
                                            simp at this
                                            apply (Nat.mul_lt_mul_right this).mpr
                                            rw[__discr_post_1]
                                            apply Nat.mod_lt
                                            simp
                                          suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                          2 ^ 52 *  ((constants.L)[0]!).val
                                          · -- BEGIN TASK
                                            scalar_tac
                                            -- END TASK
                                          · -- BEGIN TASK
                                            rw[i5_post]
                                            have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                              simp[i4_post, i3_post]
                                              have : 0< ((constants.L)[1]!).val := by
                                                unfold constants.L
                                                decide
                                              simp at this
                                              apply (Nat.mul_lt_mul_right this).mpr
                                              rename' __discr_post_1=>  __discr1
                                              rename' __discr_post_1=>  __discr2
                                              rw[__discr2]
                                              apply Nat.mod_lt
                                              simp
                                            suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                            · -- BEGIN TASK
                                              scalar_tac
                                              -- END TASK
                                            · -- BEGIN TASK
                                              rw[i2_post]
                                              rename' __discr=>  discr1
                                              suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                              2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                              · -- BEGIN TASK
                                                have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                simp at this
                                                simp[i1_post]
                                                apply le_trans this
                                                scalar_tac
                                                -- END TASK
                                              · -- BEGIN TASK
                                                rename' __discr_post_1=>  __discr1
                                                rename' __discr_post_1=>  __discr4

                                                rw[h_discr_post_3]
                                                apply Nat.div_le_of_le_mul
                                                have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                  simp
                                                  have : 0< ((constants.L)[0]!).val := by
                                                    unfold constants.L
                                                    decide
                                                  simp at this
                                                  apply (Nat.mul_lt_mul_right this).mpr
                                                  rw[__discr4]
                                                  apply Nat.mod_lt
                                                  simp
                                                suffices h: i.val ≤  2 ^ 52 *
                                                  (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                  5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                · -- BEGIN TASK
                                                  scalar_tac
                                                  -- END TASK
                                                · -- BEGIN TASK
                                                  rw[i_post]
                                                  scalar_tac
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK
                                            -- END TASK
                                          -- END TASK
                                        -- END TASK
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK
                                -- END TASK

                              -- END TASK


                    -- END TASK
                  -- END TASK
                -- END TASK
                -- END TASK



              -- END TASK

            -- END TASK



        -- END TASK

        -- END TASK


      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    rw[i39_post]
    have : i40.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
      simp[i40_post, i8_post]
      have : 0< ((constants.L)[2]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp
    suffices h: i37.val + i38.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
    · scalar_tac
    · -- BEGIN TASK
      rw[i37_post]
      have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
        simp[i38_post, i21_post]
        have : 0< ((constants.L)[4]!).val := by
          unfold constants.L
          decide
        simp at this
        apply (Nat.mul_lt_mul_right this).mpr
        simp_all
        apply Nat.mod_lt
        simp

      suffices h: __discr.1.val + i36.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
      · scalar_tac
      · -- BEGIN TASK
        suffices h: __discr.1.val < 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
        · -- BEGIN TASK
          rw[i36_post]
          expand a_bounds with 9
          scalar_tac
          -- END TASK
        · -- BEGIN TASK
          rw[__discr_post_2]
          apply Nat.div_lt_of_lt_mul
          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
            simp
            have : 0< ((constants.L)[0]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            rw[__discr_post_1]
            apply Nat.mod_lt
            simp
          suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                  2 ^ 52 *  ((constants.L)[0]!).val - 2
          · -- BEGIN TASK
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            suffices h: i33.val + i34.val < 2 ^ 128
            · rw[i35_post];scalar_tac
            · -- BEGIN TASK
              rw[i33_post]
              have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                simp[i34_post, i3_post]
                have : 0< ((constants.L)[1]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                simp_all
                apply Nat.mod_lt
                simp
              suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
              · scalar_tac
              · -- BEGIN TASK
                clear this __discr_post_1 __discr_post_2
                rename' __discr => x
                rw[i31_post]
                have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                  simp[i32_post, i8_post]
                  have : 0< ((constants.L)[2]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  simp_all
                  apply Nat.mod_lt
                  simp
                suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
                · scalar_tac
                · -- BEGIN TASK
                  rw[i29_post]
                  have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                    simp[i30_post, i21_post]
                    have : 0< ((constants.L)[4]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    simp_all
                    apply Nat.mod_lt
                    simp

                  suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                  · scalar_tac
                  · -- BEGIN TASK
                    suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                    · expand a_bounds with 9
                      scalar_tac
                    · -- BEGIN TASK
                      rw[__discr_post_2, __discr_post_1]
                      apply Nat.div_le_of_le_mul
                      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                        simp
                        have : 0< ((constants.L)[0]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rw[__discr_post_1]
                        apply Nat.mod_lt
                        simp
                      suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                          2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                                  rw[i18_post,i16_post]
                                  clear this i19_post __discr_post_2 __discr_post_1
                                  rename' __discr => discr0
                                  rename' __discr => discr1
                                  rename' __discr => discr2
                                  rename' __discr_post_2 => __discr1_post_2
                                  rename' __discr_post_2 => __discr2_post_2
                                  rename' __discr_post_1 => __discr1_post_1
                                  rename' __discr_post_1 => __discr2_post_1
                                  have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                    simp[i17_post, i3_post]
                                    have : 0< ((constants.L)[1]!).val := by
                                      unfold constants.L
                                      decide
                                    simp at this
                                    apply (Nat.mul_lt_mul_right this).mpr
                                    rw[__discr2_post_1]
                                    apply Nat.mod_lt
                                    simp
                                  suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                    2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                    2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                  · scalar_tac
                                  · -- BEGIN TASK
                                    rw[i14_post, i13_post, i15_post]
                                    have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                      simp[i15_post, i8_post]
                                      have : 0< ((constants.L)[2]!).val := by
                                        unfold constants.L
                                        decide
                                      simp at this
                                      apply (Nat.mul_lt_mul_right this).mpr
                                      rename' __discr_post_1 => __discr_post_3
                                      rw[__discr_post_3]
                                      apply Nat.mod_lt
                                      simp
                                    have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                    suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                    · -- BEGIN TASK
                                      scalar_tac
                                      -- END TASK
                                    · -- BEGIN TASK
                                            rename' __discr_post_2 => h_discr_post_2
                                            rename' __discr_post_2 => h_discr_post_3
                                            rw[h_discr_post_2]
                                            apply Nat.div_le_of_le_mul
                                            have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                              simp
                                              have : 0< ((constants.L)[0]!).val := by
                                                unfold constants.L
                                                decide
                                              simp at this
                                              apply (Nat.mul_lt_mul_right this).mpr
                                              rw[__discr_post_1]
                                              apply Nat.mod_lt
                                              simp
                                            suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                            2 ^ 52 *  ((constants.L)[0]!).val
                                            · -- BEGIN TASK
                                              scalar_tac
                                              -- END TASK
                                            · -- BEGIN TASK
                                              rw[i5_post]
                                              have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                simp[i4_post, i3_post]
                                                have : 0< ((constants.L)[1]!).val := by
                                                  unfold constants.L
                                                  decide
                                                simp at this
                                                apply (Nat.mul_lt_mul_right this).mpr
                                                rename' __discr_post_1=>  __discr1
                                                rename' __discr_post_1=>  __discr2
                                                rw[__discr2]
                                                apply Nat.mod_lt
                                                simp
                                              suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                              · -- BEGIN TASK
                                                scalar_tac
                                                -- END TASK
                                              · -- BEGIN TASK
                                                rw[i2_post]
                                                rename' __discr=>  discr1
                                                suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                                · -- BEGIN TASK
                                                  have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                  simp at this
                                                  simp[i1_post]
                                                  apply le_trans this
                                                  scalar_tac
                                                  -- END TASK
                                                · -- BEGIN TASK
                                                  rename' __discr_post_1=>  __discr1
                                                  rename' __discr_post_1=>  __discr4

                                                  rw[h_discr_post_3]
                                                  apply Nat.div_le_of_le_mul
                                                  have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                    simp
                                                    have : 0< ((constants.L)[0]!).val := by
                                                      unfold constants.L
                                                      decide
                                                    simp at this
                                                    apply (Nat.mul_lt_mul_right this).mpr
                                                    rw[__discr4]
                                                    apply Nat.mod_lt
                                                    simp
                                                  suffices h: i.val ≤  2 ^ 52 *
                                                    (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                    5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                  · -- BEGIN TASK
                                                    scalar_tac
                                                    -- END TASK
                                                  · -- BEGIN TASK
                                                    rw[i_post]
                                                    scalar_tac
                                                    -- END TASK
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK
                                            -- END TASK
                                          -- END TASK
                                        -- END TASK
                                      -- END TASK
                                    -- END TASK
                                  -- END TASK

                                -- END TASK


                      -- END TASK
                    -- END TASK
                  -- END TASK
                  -- END TASK



                -- END TASK

              -- END TASK



          -- END TASK

          -- END TASK


        -- END TASK
      -- END TASK
    -- END TASK
  · -- BEGIN TASK
    suffices h: __discr.1.val < 2 ^128 - 5 * 2 ^ 124
    · expand a_bounds with 9; scalar_tac
    · rw[__discr_post_2]
      apply Nat.div_lt_of_lt_mul
      suffices h: i39.val + i40.val < 2 ^ 128
      · scalar_tac
      · -- BEGIN TASK

        rw[i39_post]
        have : i40.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
          simp[i40_post, i8_post]
          have : 0< ((constants.L)[2]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp
        suffices h: i37.val + i38.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
        · scalar_tac
        · -- BEGIN TASK
          clear this __discr_post_1 __discr_post_2
          rename' __discr => __discr40
          rw[i37_post]
          have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
            simp[i38_post, i21_post]
            have : 0< ((constants.L)[4]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp

          suffices h: __discr.1.val + i36.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
          · scalar_tac
          · -- BEGIN TASK
            suffices h: __discr.1.val < 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              rw[i36_post]
              expand a_bounds with 9
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_lt_of_lt_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                      2 ^ 52 *  ((constants.L)[0]!).val - 2
              · -- BEGIN TASK
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                suffices h: i33.val + i34.val < 2 ^ 128
                · rw[i35_post];scalar_tac
                · -- BEGIN TASK
                  rw[i33_post]
                  have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                    simp[i34_post, i3_post]
                    have : 0< ((constants.L)[1]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    simp_all
                    apply Nat.mod_lt
                    simp
                  suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
                  · scalar_tac
                  · -- BEGIN TASK
                    clear this __discr_post_1 __discr_post_2
                    rename' __discr => x
                    rw[i31_post]
                    have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                      simp[i32_post, i8_post]
                      have : 0< ((constants.L)[2]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      simp_all
                      apply Nat.mod_lt
                      simp
                    suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
                    · scalar_tac
                    · -- BEGIN TASK
                      rw[i29_post]
                      have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                        simp[i30_post, i21_post]
                        have : 0< ((constants.L)[4]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        simp_all
                        apply Nat.mod_lt
                        simp

                      suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                      · scalar_tac
                      · -- BEGIN TASK
                        suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                        · expand a_bounds with 9
                          scalar_tac
                        · -- BEGIN TASK
                          rw[__discr_post_2, __discr_post_1]
                          apply Nat.div_le_of_le_mul
                          have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                            simp
                            have : 0< ((constants.L)[0]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            rw[__discr_post_1]
                            apply Nat.mod_lt
                            simp
                          suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                              2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                          · -- BEGIN TASK
                            scalar_tac
                            -- END TASK
                          · -- BEGIN TASK
                                      rw[i18_post,i16_post]
                                      clear this i19_post __discr_post_2 __discr_post_1
                                      rename' __discr => discr0
                                      rename' __discr => discr1
                                      rename' __discr => discr2
                                      rename' __discr_post_2 => __discr1_post_2
                                      rename' __discr_post_2 => __discr2_post_2
                                      rename' __discr_post_1 => __discr1_post_1
                                      rename' __discr_post_1 => __discr2_post_1
                                      have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                        simp[i17_post, i3_post]
                                        have : 0< ((constants.L)[1]!).val := by
                                          unfold constants.L
                                          decide
                                        simp at this
                                        apply (Nat.mul_lt_mul_right this).mpr
                                        rw[__discr2_post_1]
                                        apply Nat.mod_lt
                                        simp
                                      suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                        2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                        2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                      · scalar_tac
                                      · -- BEGIN TASK
                                        rw[i14_post, i13_post, i15_post]
                                        have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                          simp[i15_post, i8_post]
                                          have : 0< ((constants.L)[2]!).val := by
                                            unfold constants.L
                                            decide
                                          simp at this
                                          apply (Nat.mul_lt_mul_right this).mpr
                                          rename' __discr_post_1 => __discr_post_3
                                          rw[__discr_post_3]
                                          apply Nat.mod_lt
                                          simp
                                        have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                        suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                        · -- BEGIN TASK
                                          scalar_tac
                                          -- END TASK
                                        · -- BEGIN TASK
                                                rename' __discr_post_2 => h_discr_post_2
                                                rename' __discr_post_2 => h_discr_post_3
                                                rw[h_discr_post_2]
                                                apply Nat.div_le_of_le_mul
                                                have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                  simp
                                                  have : 0< ((constants.L)[0]!).val := by
                                                    unfold constants.L
                                                    decide
                                                  simp at this
                                                  apply (Nat.mul_lt_mul_right this).mpr
                                                  rw[__discr_post_1]
                                                  apply Nat.mod_lt
                                                  simp
                                                suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                2 ^ 52 *  ((constants.L)[0]!).val
                                                · -- BEGIN TASK
                                                  scalar_tac
                                                  -- END TASK
                                                · -- BEGIN TASK
                                                  rw[i5_post]
                                                  have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                    simp[i4_post, i3_post]
                                                    have : 0< ((constants.L)[1]!).val := by
                                                      unfold constants.L
                                                      decide
                                                    simp at this
                                                    apply (Nat.mul_lt_mul_right this).mpr
                                                    rename' __discr_post_1=>  __discr1
                                                    rename' __discr_post_1=>  __discr2
                                                    rw[__discr2]
                                                    apply Nat.mod_lt
                                                    simp
                                                  suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                    2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                                  · -- BEGIN TASK
                                                    scalar_tac
                                                    -- END TASK
                                                  · -- BEGIN TASK
                                                    rw[i2_post]
                                                    rename' __discr=>  discr1
                                                    suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                    2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                                    · -- BEGIN TASK
                                                      have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                      simp at this
                                                      simp[i1_post]
                                                      apply le_trans this
                                                      scalar_tac
                                                      -- END TASK
                                                    · -- BEGIN TASK
                                                      rename' __discr_post_1=>  __discr1
                                                      rename' __discr_post_1=>  __discr4

                                                      rw[h_discr_post_3]
                                                      apply Nat.div_le_of_le_mul
                                                      have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                        simp
                                                        have : 0< ((constants.L)[0]!).val := by
                                                          unfold constants.L
                                                          decide
                                                        simp at this
                                                        apply (Nat.mul_lt_mul_right this).mpr
                                                        rw[__discr4]
                                                        apply Nat.mod_lt
                                                        simp
                                                      suffices h: i.val ≤  2 ^ 52 *
                                                        (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                        5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                      · -- BEGIN TASK
                                                        scalar_tac
                                                        -- END TASK
                                                      · -- BEGIN TASK
                                                        rw[i_post]
                                                        scalar_tac
                                                        -- END TASK
                                                      -- END TASK
                                                    -- END TASK
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK
                                            -- END TASK
                                          -- END TASK
                                        -- END TASK
                                      -- END TASK

                                    -- END TASK


                          -- END TASK
                        -- END TASK
                      -- END TASK
                      -- END TASK



                    -- END TASK

                  -- END TASK



              -- END TASK

              -- END TASK


            -- END TASK
          -- END TASK
        -- END TASK

    -- END TASK
  · -- BEGIN TASK
    rw[i43_post]
    have : i44.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
      simp[i44_post, i21_post]
      have : 0< ((constants.L)[4]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: __discr.1.val + i42.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
    · scalar_tac
    · -- BEGIN TASK
      suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
      · -- BEGIN TASK
        rw[i42_post]
        expand a_bounds with 9
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_lt_of_lt_mul
        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i41.val ≤  2^128-1
        · scalar_tac
        · -- BEGIN TASK
          clear this __discr_post_1 __discr_post_2
          rename' __discr => q40
          rw[i41_post, i39_post]
          have : i40.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
            simp[i40_post, i8_post]
            have : 0< ((constants.L)[2]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp
          suffices h: i37.val + i38.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
          · scalar_tac
          · -- BEGIN TASK
            rw[i37_post]
            have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
              simp[i38_post, i21_post]
              have : 0< ((constants.L)[4]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              simp_all
              apply Nat.mod_lt
              simp

            suffices h: __discr.1.val + i36.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
            · scalar_tac
            · -- BEGIN TASK
              suffices h: __discr.1.val < 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
              · -- BEGIN TASK
                rw[i36_post]
                expand a_bounds with 9
                scalar_tac
                -- END TASK
              · -- BEGIN TASK
                rw[__discr_post_2]
                apply Nat.div_lt_of_lt_mul
                have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                  simp
                  have : 0< ((constants.L)[0]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  rw[__discr_post_1]
                  apply Nat.mod_lt
                  simp
                suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                        2 ^ 52 *  ((constants.L)[0]!).val - 2
                · -- BEGIN TASK
                  scalar_tac
                  -- END TASK
                · -- BEGIN TASK
                  suffices h: i33.val + i34.val < 2 ^ 128
                  · rw[i35_post];scalar_tac
                  · -- BEGIN TASK
                    rw[i33_post]
                    have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                      simp[i34_post, i3_post]
                      have : 0< ((constants.L)[1]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      simp_all
                      apply Nat.mod_lt
                      simp
                    suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
                    · scalar_tac
                    · -- BEGIN TASK
                      clear this __discr_post_1 __discr_post_2
                      rename' __discr => x
                      rw[i31_post]
                      have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                        simp[i32_post, i8_post]
                        have : 0< ((constants.L)[2]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        simp_all
                        apply Nat.mod_lt
                        simp
                      suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
                      · scalar_tac
                      · -- BEGIN TASK
                        rw[i29_post]
                        have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                          simp[i30_post, i21_post]
                          have : 0< ((constants.L)[4]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          simp_all
                          apply Nat.mod_lt
                          simp

                        suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                        · scalar_tac
                        · -- BEGIN TASK
                          suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                          · expand a_bounds with 9
                            scalar_tac
                          · -- BEGIN TASK
                            rw[__discr_post_2, __discr_post_1]
                            apply Nat.div_le_of_le_mul
                            have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                              simp
                              have : 0< ((constants.L)[0]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              rw[__discr_post_1]
                              apply Nat.mod_lt
                              simp
                            suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                            · -- BEGIN TASK
                              scalar_tac
                              -- END TASK
                            · -- BEGIN TASK
                                        rw[i18_post,i16_post]
                                        clear this i19_post __discr_post_2 __discr_post_1
                                        rename' __discr => discr0
                                        rename' __discr => discr1
                                        rename' __discr => discr2
                                        rename' __discr_post_2 => __discr1_post_2
                                        rename' __discr_post_2 => __discr2_post_2
                                        rename' __discr_post_1 => __discr1_post_1
                                        rename' __discr_post_1 => __discr2_post_1
                                        have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                          simp[i17_post, i3_post]
                                          have : 0< ((constants.L)[1]!).val := by
                                            unfold constants.L
                                            decide
                                          simp at this
                                          apply (Nat.mul_lt_mul_right this).mpr
                                          rw[__discr2_post_1]
                                          apply Nat.mod_lt
                                          simp
                                        suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                          2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                          2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                        · scalar_tac
                                        · -- BEGIN TASK
                                          rw[i14_post, i13_post, i15_post]
                                          have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                            simp[i15_post, i8_post]
                                            have : 0< ((constants.L)[2]!).val := by
                                              unfold constants.L
                                              decide
                                            simp at this
                                            apply (Nat.mul_lt_mul_right this).mpr
                                            rename' __discr_post_1 => __discr_post_3
                                            rw[__discr_post_3]
                                            apply Nat.mod_lt
                                            simp
                                          have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                          suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                          · -- BEGIN TASK
                                            scalar_tac
                                            -- END TASK
                                          · -- BEGIN TASK
                                                  rename' __discr_post_2 => h_discr_post_2
                                                  rename' __discr_post_2 => h_discr_post_3
                                                  rw[h_discr_post_2]
                                                  apply Nat.div_le_of_le_mul
                                                  have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                    simp
                                                    have : 0< ((constants.L)[0]!).val := by
                                                      unfold constants.L
                                                      decide
                                                    simp at this
                                                    apply (Nat.mul_lt_mul_right this).mpr
                                                    rw[__discr_post_1]
                                                    apply Nat.mod_lt
                                                    simp
                                                  suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                  2 ^ 52 *  ((constants.L)[0]!).val
                                                  · -- BEGIN TASK
                                                    scalar_tac
                                                    -- END TASK
                                                  · -- BEGIN TASK
                                                    rw[i5_post]
                                                    have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                      simp[i4_post, i3_post]
                                                      have : 0< ((constants.L)[1]!).val := by
                                                        unfold constants.L
                                                        decide
                                                      simp at this
                                                      apply (Nat.mul_lt_mul_right this).mpr
                                                      rename' __discr_post_1=>  __discr1
                                                      rename' __discr_post_1=>  __discr2
                                                      rw[__discr2]
                                                      apply Nat.mod_lt
                                                      simp
                                                    suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                                    · -- BEGIN TASK
                                                      scalar_tac
                                                      -- END TASK
                                                    · -- BEGIN TASK
                                                      rw[i2_post]
                                                      rename' __discr=>  discr1
                                                      suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                      2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                                      · -- BEGIN TASK
                                                        have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                        simp at this
                                                        simp[i1_post]
                                                        apply le_trans this
                                                        scalar_tac
                                                        -- END TASK
                                                      · -- BEGIN TASK
                                                        rename' __discr_post_1=>  __discr1
                                                        rename' __discr_post_1=>  __discr4

                                                        rw[h_discr_post_3]
                                                        apply Nat.div_le_of_le_mul
                                                        have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                          simp
                                                          have : 0< ((constants.L)[0]!).val := by
                                                            unfold constants.L
                                                            decide
                                                          simp at this
                                                          apply (Nat.mul_lt_mul_right this).mpr
                                                          rw[__discr4]
                                                          apply Nat.mod_lt
                                                          simp
                                                        suffices h: i.val ≤  2 ^ 52 *
                                                          (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                          5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                        · -- BEGIN TASK
                                                          scalar_tac
                                                          -- END TASK
                                                        · -- BEGIN TASK
                                                          rw[i_post]
                                                          scalar_tac
                                                          -- END TASK
                                                        -- END TASK
                                                      -- END TASK
                                                    -- END TASK
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK
                                            -- END TASK
                                          -- END TASK
                                        -- END TASK

                                      -- END TASK


                            -- END TASK
                          -- END TASK
                        -- END TASK
                        -- END TASK



                      -- END TASK

                    -- END TASK



                -- END TASK

                -- END TASK


              -- END TASK
            -- END TASK
          -- END TASK



    -- END TASK
  · -- BEGIN TASK
    suffices h: __discr.1.val < 2 ^128 - 5 * 2 ^ 124
    · expand a_bounds with 9; scalar_tac
    · rw[__discr_post_2]
      apply Nat.div_lt_of_lt_mul
      suffices h: i43.val + i44.val < 2 ^ 128
      · scalar_tac
      · -- BEGIN TASK
        clear  __discr_post_1 __discr_post_2
        rename' __discr => q44

        rw[i43_post]
        have : i44.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
          simp[i44_post, i21_post]
          have : 0< ((constants.L)[4]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          simp_all
          apply Nat.mod_lt
          simp

        suffices h: __discr.1.val + i42.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
        · scalar_tac
        · -- BEGIN TASK
          suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
          · -- BEGIN TASK
            rw[i42_post]
            expand a_bounds with 9
            scalar_tac
            -- END TASK
          · -- BEGIN TASK
            rw[__discr_post_2]
            apply Nat.div_lt_of_lt_mul
            have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
              simp
              have : 0< ((constants.L)[0]!).val := by
                unfold constants.L
                decide
              simp at this
              apply (Nat.mul_lt_mul_right this).mpr
              rw[__discr_post_1]
              apply Nat.mod_lt
              simp
            suffices h: i41.val ≤  2^128-1
            · scalar_tac
            · -- BEGIN TASK
              clear this __discr_post_1 __discr_post_2
              rename' __discr => q40
              rw[i41_post, i39_post]
              have : i40.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                simp[i40_post, i8_post]
                have : 0< ((constants.L)[2]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                simp_all
                apply Nat.mod_lt
                simp
              suffices h: i37.val + i38.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
              · scalar_tac
              · -- BEGIN TASK
                rw[i37_post]
                have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                  simp[i38_post, i21_post]
                  have : 0< ((constants.L)[4]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  simp_all
                  apply Nat.mod_lt
                  simp

                suffices h: __discr.1.val + i36.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                · scalar_tac
                · -- BEGIN TASK
                  suffices h: __discr.1.val < 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                  · -- BEGIN TASK
                    rw[i36_post]
                    expand a_bounds with 9
                    scalar_tac
                    -- END TASK
                  · -- BEGIN TASK
                    rw[__discr_post_2]
                    apply Nat.div_lt_of_lt_mul
                    have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                      simp
                      have : 0< ((constants.L)[0]!).val := by
                        unfold constants.L
                        decide
                      simp at this
                      apply (Nat.mul_lt_mul_right this).mpr
                      rw[__discr_post_1]
                      apply Nat.mod_lt
                      simp
                    suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                            2 ^ 52 *  ((constants.L)[0]!).val - 2
                    · -- BEGIN TASK
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      suffices h: i33.val + i34.val < 2 ^ 128
                      · rw[i35_post];scalar_tac
                      · -- BEGIN TASK
                        rw[i33_post]
                        have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                          simp[i34_post, i3_post]
                          have : 0< ((constants.L)[1]!).val := by
                            unfold constants.L
                            decide
                          simp at this
                          apply (Nat.mul_lt_mul_right this).mpr
                          simp_all
                          apply Nat.mod_lt
                          simp
                        suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
                        · scalar_tac
                        · -- BEGIN TASK
                          clear this __discr_post_1 __discr_post_2
                          rename' __discr => x
                          rw[i31_post]
                          have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                            simp[i32_post, i8_post]
                            have : 0< ((constants.L)[2]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            simp_all
                            apply Nat.mod_lt
                            simp
                          suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
                          · scalar_tac
                          · -- BEGIN TASK
                            rw[i29_post]
                            have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                              simp[i30_post, i21_post]
                              have : 0< ((constants.L)[4]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              simp_all
                              apply Nat.mod_lt
                              simp

                            suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                            · scalar_tac
                            · -- BEGIN TASK
                              suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                              · expand a_bounds with 9
                                scalar_tac
                              · -- BEGIN TASK
                                rw[__discr_post_2, __discr_post_1]
                                apply Nat.div_le_of_le_mul
                                have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                  simp
                                  have : 0< ((constants.L)[0]!).val := by
                                    unfold constants.L
                                    decide
                                  simp at this
                                  apply (Nat.mul_lt_mul_right this).mpr
                                  rw[__discr_post_1]
                                  apply Nat.mod_lt
                                  simp
                                suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                    2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                                · -- BEGIN TASK
                                  scalar_tac
                                  -- END TASK
                                · -- BEGIN TASK
                                            rw[i18_post,i16_post]
                                            clear this i19_post __discr_post_2 __discr_post_1
                                            rename' __discr => discr0
                                            rename' __discr => discr1
                                            rename' __discr => discr2
                                            rename' __discr_post_2 => __discr1_post_2
                                            rename' __discr_post_2 => __discr2_post_2
                                            rename' __discr_post_1 => __discr1_post_1
                                            rename' __discr_post_1 => __discr2_post_1
                                            have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                              simp[i17_post, i3_post]
                                              have : 0< ((constants.L)[1]!).val := by
                                                unfold constants.L
                                                decide
                                              simp at this
                                              apply (Nat.mul_lt_mul_right this).mpr
                                              rw[__discr2_post_1]
                                              apply Nat.mod_lt
                                              simp
                                            suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                              2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                              2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                            · scalar_tac
                                            · -- BEGIN TASK
                                              rw[i14_post, i13_post, i15_post]
                                              have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                                simp[i15_post, i8_post]
                                                have : 0< ((constants.L)[2]!).val := by
                                                  unfold constants.L
                                                  decide
                                                simp at this
                                                apply (Nat.mul_lt_mul_right this).mpr
                                                rename' __discr_post_1 => __discr_post_3
                                                rw[__discr_post_3]
                                                apply Nat.mod_lt
                                                simp
                                              have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                              suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                              · -- BEGIN TASK
                                                scalar_tac
                                                -- END TASK
                                              · -- BEGIN TASK
                                                      rename' __discr_post_2 => h_discr_post_2
                                                      rename' __discr_post_2 => h_discr_post_3
                                                      rw[h_discr_post_2]
                                                      apply Nat.div_le_of_le_mul
                                                      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                        simp
                                                        have : 0< ((constants.L)[0]!).val := by
                                                          unfold constants.L
                                                          decide
                                                        simp at this
                                                        apply (Nat.mul_lt_mul_right this).mpr
                                                        rw[__discr_post_1]
                                                        apply Nat.mod_lt
                                                        simp
                                                      suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                      2 ^ 52 *  ((constants.L)[0]!).val
                                                      · -- BEGIN TASK
                                                        scalar_tac
                                                        -- END TASK
                                                      · -- BEGIN TASK
                                                        rw[i5_post]
                                                        have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                          simp[i4_post, i3_post]
                                                          have : 0< ((constants.L)[1]!).val := by
                                                            unfold constants.L
                                                            decide
                                                          simp at this
                                                          apply (Nat.mul_lt_mul_right this).mpr
                                                          rename' __discr_post_1=>  __discr1
                                                          rename' __discr_post_1=>  __discr2
                                                          rw[__discr2]
                                                          apply Nat.mod_lt
                                                          simp
                                                        suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                                        · -- BEGIN TASK
                                                          scalar_tac
                                                          -- END TASK
                                                        · -- BEGIN TASK
                                                          rw[i2_post]
                                                          rename' __discr=>  discr1
                                                          suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                          2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                                          · -- BEGIN TASK
                                                            have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                            simp at this
                                                            simp[i1_post]
                                                            apply le_trans this
                                                            scalar_tac
                                                            -- END TASK
                                                          · -- BEGIN TASK
                                                            rename' __discr_post_1=>  __discr1
                                                            rename' __discr_post_1=>  __discr4

                                                            rw[h_discr_post_3]
                                                            apply Nat.div_le_of_le_mul
                                                            have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                              simp
                                                              have : 0< ((constants.L)[0]!).val := by
                                                                unfold constants.L
                                                                decide
                                                              simp at this
                                                              apply (Nat.mul_lt_mul_right this).mpr
                                                              rw[__discr4]
                                                              apply Nat.mod_lt
                                                              simp
                                                            suffices h: i.val ≤  2 ^ 52 *
                                                              (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                              5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                            · -- BEGIN TASK
                                                              scalar_tac
                                                              -- END TASK
                                                            · -- BEGIN TASK
                                                              rw[i_post]
                                                              scalar_tac
                                                              -- END TASK
                                                            -- END TASK
                                                          -- END TASK
                                                        -- END TASK
                                                      -- END TASK
                                                    -- END TASK
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK
                                            -- END TASK

                                          -- END TASK


                                -- END TASK
                              -- END TASK
                            -- END TASK
                            -- END TASK



                          -- END TASK

                        -- END TASK



                    -- END TASK

                    -- END TASK


                  -- END TASK
                -- END TASK
              -- END TASK



        -- END TASK



    -- END TASK
  · -- BEGIN TASK
    rw[i47_post]
    have : i48.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
      simp[i48_post, i21_post]
      have : 0< ((constants.L)[4]!).val := by
        unfold constants.L
        decide
      simp at this
      apply (Nat.mul_lt_mul_right this).mpr
      simp_all
      apply Nat.mod_lt
      simp

    suffices h: __discr.1.val + i46.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
    · scalar_tac
    · -- BEGIN TASK
      suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
      · -- BEGIN TASK
        rw[i46_post]
        expand a_bounds with 9
        scalar_tac
        -- END TASK
      · -- BEGIN TASK
        rw[__discr_post_2]
        apply Nat.div_lt_of_lt_mul
        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
          simp
          have : 0< ((constants.L)[0]!).val := by
            unfold constants.L
            decide
          simp at this
          apply (Nat.mul_lt_mul_right this).mpr
          rw[__discr_post_1]
          apply Nat.mod_lt
          simp
        suffices h: i45.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                2 ^ 52 *  ((constants.L)[0]!).val - 2
        · scalar_tac

        · -- BEGIN TASK
          clear  __discr_post_1 __discr_post_2
          rename' __discr => q44

          rw[i45_post, i43_post]
          have : i44.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
            simp[i44_post, i21_post]
            have : 0< ((constants.L)[4]!).val := by
              unfold constants.L
              decide
            simp at this
            apply (Nat.mul_lt_mul_right this).mpr
            simp_all
            apply Nat.mod_lt
            simp

          suffices h: __discr.1.val + i42.val ≤ 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val
          · scalar_tac
          · -- BEGIN TASK
            suffices h: __discr.1.val < 2 ^ 128 - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
            · -- BEGIN TASK
              rw[i42_post]
              expand a_bounds with 9
              scalar_tac
              -- END TASK
            · -- BEGIN TASK
              rw[__discr_post_2]
              apply Nat.div_lt_of_lt_mul
              have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                simp
                have : 0< ((constants.L)[0]!).val := by
                  unfold constants.L
                  decide
                simp at this
                apply (Nat.mul_lt_mul_right this).mpr
                rw[__discr_post_1]
                apply Nat.mod_lt
                simp
              suffices h: i41.val ≤  2^128-1
              · scalar_tac
              · -- BEGIN TASK
                clear this __discr_post_1 __discr_post_2
                rename' __discr => q40
                rw[i41_post, i39_post]
                have : i40.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                  simp[i40_post, i8_post]
                  have : 0< ((constants.L)[2]!).val := by
                    unfold constants.L
                    decide
                  simp at this
                  apply (Nat.mul_lt_mul_right this).mpr
                  simp_all
                  apply Nat.mod_lt
                  simp
                suffices h: i37.val + i38.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val
                · scalar_tac
                · -- BEGIN TASK
                  rw[i37_post]
                  have : i38.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                    simp[i38_post, i21_post]
                    have : 0< ((constants.L)[4]!).val := by
                      unfold constants.L
                      decide
                    simp at this
                    apply (Nat.mul_lt_mul_right this).mpr
                    simp_all
                    apply Nat.mod_lt
                    simp

                  suffices h: __discr.1.val + i36.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                  · scalar_tac
                  · -- BEGIN TASK
                    suffices h: __discr.1.val < 2^ 128 - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                    · -- BEGIN TASK
                      rw[i36_post]
                      expand a_bounds with 9
                      scalar_tac
                      -- END TASK
                    · -- BEGIN TASK
                      rw[__discr_post_2]
                      apply Nat.div_lt_of_lt_mul
                      have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                        simp
                        have : 0< ((constants.L)[0]!).val := by
                          unfold constants.L
                          decide
                        simp at this
                        apply (Nat.mul_lt_mul_right this).mpr
                        rw[__discr_post_1]
                        apply Nat.mod_lt
                        simp
                      suffices h: i35.val ≤  2 ^ 52 * (2 ^ 128 - 5 * 2 ^ 124) -
                              2 ^ 52 *  ((constants.L)[0]!).val - 2
                      · -- BEGIN TASK
                        scalar_tac
                        -- END TASK
                      · -- BEGIN TASK
                        suffices h: i33.val + i34.val < 2 ^ 128
                        · rw[i35_post];scalar_tac
                        · -- BEGIN TASK
                          rw[i33_post]
                          have : i34.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                            simp[i34_post, i3_post]
                            have : 0< ((constants.L)[1]!).val := by
                              unfold constants.L
                              decide
                            simp at this
                            apply (Nat.mul_lt_mul_right this).mpr
                            simp_all
                            apply Nat.mod_lt
                            simp
                          suffices h: i31.val + i32.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val
                          · scalar_tac
                          · -- BEGIN TASK
                            clear this __discr_post_1 __discr_post_2
                            rename' __discr => x
                            rw[i31_post]
                            have : i32.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                              simp[i32_post, i8_post]
                              have : 0< ((constants.L)[2]!).val := by
                                unfold constants.L
                                decide
                              simp at this
                              apply (Nat.mul_lt_mul_right this).mpr
                              simp_all
                              apply Nat.mod_lt
                              simp
                            suffices h: i29.val + i30.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val
                            · scalar_tac
                            · -- BEGIN TASK
                              rw[i29_post]
                              have : i30.val < 2 ^ 52 *  ((constants.L)[4]!).val := by
                                simp[i30_post, i21_post]
                                have : 0< ((constants.L)[4]!).val := by
                                  unfold constants.L
                                  decide
                                simp at this
                                apply (Nat.mul_lt_mul_right this).mpr
                                simp_all
                                apply Nat.mod_lt
                                simp

                              suffices h: ↑__discr.1 + i28.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val
                              · scalar_tac
                              · -- BEGIN TASK
                                suffices h: ↑__discr.1  ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val - 2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124
                                · expand a_bounds with 9
                                  scalar_tac
                                · -- BEGIN TASK
                                  rw[__discr_post_2, __discr_post_1]
                                  apply Nat.div_le_of_le_mul
                                  have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                    simp
                                    have : 0< ((constants.L)[0]!).val := by
                                      unfold constants.L
                                      decide
                                    simp at this
                                    apply (Nat.mul_lt_mul_right this).mpr
                                    rw[__discr_post_1]
                                    apply Nat.mod_lt
                                    simp
                                  suffices h: i18.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                      2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 - 2 ^ 52 *  ((constants.L)[0]!).val
                                  · -- BEGIN TASK
                                    scalar_tac
                                    -- END TASK
                                  · -- BEGIN TASK
                                              rw[i18_post,i16_post]
                                              clear this i19_post __discr_post_2 __discr_post_1
                                              rename' __discr => discr0
                                              rename' __discr => discr1
                                              rename' __discr => discr2
                                              rename' __discr_post_2 => __discr1_post_2
                                              rename' __discr_post_2 => __discr2_post_2
                                              rename' __discr_post_1 => __discr1_post_1
                                              rename' __discr_post_1 => __discr2_post_1
                                              have : i17.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                simp[i17_post, i3_post]
                                                have : 0< ((constants.L)[1]!).val := by
                                                  unfold constants.L
                                                  decide
                                                simp at this
                                                apply (Nat.mul_lt_mul_right this).mpr
                                                rw[__discr2_post_1]
                                                apply Nat.mod_lt
                                                simp
                                              suffices h: i14.val + i15.val ≤ 2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[2]!).val -
                                                2 ^ 52 *  ((constants.L)[4]!).val - 5 * 2 ^ 124 -
                                                2 ^ 52 *  ((constants.L)[0]!).val - 2 ^ 52 *  ((constants.L)[1]!).val
                                              · scalar_tac
                                              · -- BEGIN TASK
                                                rw[i14_post, i13_post, i15_post]
                                                have : i15.val < 2 ^ 52 *  ((constants.L)[2]!).val := by
                                                  simp[i15_post, i8_post]
                                                  have : 0< ((constants.L)[2]!).val := by
                                                    unfold constants.L
                                                    decide
                                                  simp at this
                                                  apply (Nat.mul_lt_mul_right this).mpr
                                                  rename' __discr_post_1 => __discr_post_3
                                                  rw[__discr_post_3]
                                                  apply Nat.mod_lt
                                                  simp
                                                have := Nat.add_lt_add (a_bounds 3 (by simp)) this
                                                suffices h:  __discr.1.val ≤  2^ 128 - 2 ^ 52 *  ((constants.L)[1]!).val - 2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124 - 2 ^ 52 * (constants.L[2]!).val
                                                · -- BEGIN TASK
                                                  scalar_tac
                                                  -- END TASK
                                                · -- BEGIN TASK
                                                        rename' __discr_post_2 => h_discr_post_2
                                                        rename' __discr_post_2 => h_discr_post_3
                                                        rw[h_discr_post_2]
                                                        apply Nat.div_le_of_le_mul
                                                        have : __discr.2.val * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                          simp
                                                          have : 0< ((constants.L)[0]!).val := by
                                                            unfold constants.L
                                                            decide
                                                          simp at this
                                                          apply (Nat.mul_lt_mul_right this).mpr
                                                          rw[__discr_post_1]
                                                          apply Nat.mod_lt
                                                          simp
                                                        suffices h: i5.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                        2 ^ 52 *  ((constants.L)[0]!).val
                                                        · -- BEGIN TASK
                                                          scalar_tac
                                                          -- END TASK
                                                        · -- BEGIN TASK
                                                          rw[i5_post]
                                                          have : i4.val < 2 ^ 52 *  ((constants.L)[1]!).val := by
                                                            simp[i4_post, i3_post]
                                                            have : 0< ((constants.L)[1]!).val := by
                                                              unfold constants.L
                                                              decide
                                                            simp at this
                                                            apply (Nat.mul_lt_mul_right this).mpr
                                                            rename' __discr_post_1=>  __discr1
                                                            rename' __discr_post_1=>  __discr2
                                                            rw[__discr2]
                                                            apply Nat.mod_lt
                                                            simp
                                                          suffices h: i2.val ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val
                                                          · -- BEGIN TASK
                                                            scalar_tac
                                                            -- END TASK
                                                          · -- BEGIN TASK
                                                            rw[i2_post]
                                                            rename' __discr=>  discr1
                                                            suffices h: ↑__discr.1 ≤  2 ^128-1 - 5 * 2 ^ 124 - 2^ 52 * ((constants.L)[2]!).val -
                                                            2 ^ 52 *  ((constants.L)[0]!).val  -2 ^ 52 *  ((constants.L)[1]!).val - 5 * 2 ^ 124
                                                            · -- BEGIN TASK
                                                              have := Nat.add_le_add h (le_of_lt (a_bounds 1 (by simp: 1<9)))
                                                              simp at this
                                                              simp[i1_post]
                                                              apply le_trans this
                                                              scalar_tac
                                                              -- END TASK
                                                            · -- BEGIN TASK
                                                              rename' __discr_post_1=>  __discr1
                                                              rename' __discr_post_1=>  __discr4

                                                              rw[h_discr_post_3]
                                                              apply Nat.div_le_of_le_mul
                                                              have : ↑__discr.2 * ↑constants.L[0]! < 2 ^ 52 *  ((constants.L)[0]!).val := by
                                                                simp
                                                                have : 0< ((constants.L)[0]!).val := by
                                                                  unfold constants.L
                                                                  decide
                                                                simp at this
                                                                apply (Nat.mul_lt_mul_right this).mpr
                                                                rw[__discr4]
                                                                apply Nat.mod_lt
                                                                simp
                                                              suffices h: i.val ≤  2 ^ 52 *
                                                                (2 ^ 128 - 1 - 5 * 2 ^ 124 - 2 ^ 52 * ↑constants.L[2]! - 2 ^ 52 * ↑constants.L[0]! - 2 ^ 52 * ↑constants.L[1]! -
                                                                5 * 2 ^ 124) - 2 ^ 52 *  ((constants.L)[0]!).val
                                                              · -- BEGIN TASK
                                                                scalar_tac
                                                                -- END TASK
                                                              · -- BEGIN TASK
                                                                rw[i_post]
                                                                scalar_tac
                                                                -- END TASK
                                                              -- END TASK
                                                            -- END TASK
                                                          -- END TASK
                                                        -- END TASK
                                                      -- END TASK
                                                    -- END TASK
                                                  -- END TASK
                                                -- END TASK
                                              -- END TASK

                                            -- END TASK


                                  -- END TASK
                                -- END TASK
                              -- END TASK
                              -- END TASK



                            -- END TASK

                          -- END TASK



                      -- END TASK

                      -- END TASK


                    -- END TASK
                  -- END TASK
                -- END TASK



          -- END TASK



    -- END TASK
  · intro i hi
    interval_cases i
    any_goals (simp_all [Array.make]; apply Nat.mod_lt; simp)
    simp[Array.make]
    rw[r4_post, UScalar.cast_val_eq, UScalarTy.numBits, __discr_post_2]
    suffices h: i49.val < 2 ^ 52 * 2 ^ 52
    · scalar_tac
    ·

  · interval_cases i
  · constructor
    · interval_cases i
      ·

    · constructor
      · grind
      · sorry






-/






















end curve25519_dalek.backend.serial.u64.scalar.Scalar52
