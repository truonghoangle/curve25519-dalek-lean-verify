/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.AsExtended
/-! # Spec Theorem for `RistrettoPoint::elligator_ristretto_flavor`

Specification and proof for `RistrettoPoint::elligator_ristretto_flavor`.

This function implements the Ristretto Elligator map, which is the MAP function
defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4).

It maps an arbitrary field element to a valid Ristretto point (which represents an equivalence
class of 8 Edwards points).

**Source**: curve25519-dalek/src/ristretto.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.curve_models (ProjectivePoint)
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.ristretto.RistrettoPoint

/-
natural language description:

• Takes a field element r₀ and maps it to a valid RistrettoPoint (which represents an equivalence class
  of 8 Edwards points) using the Elligator map:
  https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-04#section-4.3.4
  Arithmetics are performed in the field 𝔽ₚ where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic) for all field element inputs
• Given an input field element r₀, the output RistrettoPoint indeed lies on the Curve25519 Edwards curve, i.e.,
  it indeed fulfils the curve equation.
-/

/- **Spec and proof concerning `ristretto.RistrettoPoint.elligator_ristretto_flavor`**:
• The function always succeeds (no panic) for all field element inputs
• Given an input field element r₀, the output RistrettoPoint indeed lies on the Curve25519 Edwards curve, i.e.,
  it indeed fulfils the curve equation.
-/


set_option maxHeartbeats 1000000000 in
-- simp_all heavy

@[progress]
theorem elligator_ristretto_flavor_spec
  (r_0 : backend.serial.u64.field.FieldElement51)
  (h_r_0_bounds : ∀ i, i < 5 → (r_0[i]!).val < 2 ^ 54) :
  ∃ rist,
    elligator_ristretto_flavor r_0 = ok rist ∧
    rist.IsValid := by
  unfold elligator_ristretto_flavor
  progress*
  · unfold  constants.SQRT_M1
    decide
  · expand fe_post_2 with 5; grind
  · expand r_post_2 with 5; grind
  · unfold  ONE
    decide
  · unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
    decide
  · unfold constants.EDWARDS_D
    decide
  · expand r_post_2 with 5; grind
  · unfold constants.MINUS_ONE
    decide
  · expand fe2_post_2 with 5; grind
  · expand r_post_2 with 5; grind
  · unfold constants.EDWARDS_D
    decide
  · expand fe3_post_1 with 5; grind
  · expand D_post_2 with 5; grind
  · expand D_post_2 with 5; grind
  · -- BEGIN TASK
    by_cases h: Field51_as_Nat N_s % p = 0
    · rw[← modEq_zero_iff] at h
      have :=(h.symm.trans N_s_post_1).symm
      have := mul_zero_eq_or prime_25519 this
      rcases this with h | h
      ·
        have : Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE := by
          simp[Field51_as_Nat, Finset.sum_range_succ]
          simp_all
          grind
        rw[this] at h
        have : Field51_as_Nat ONE =1 := by
          unfold ONE
          decide
        rw[this] at h
        have h:=h.add_right (p-1)
        rw[add_assoc] at h
        have : 1+(p-1)=p := by unfold p; scalar_tac
        rw[this] at h
        simp at h
        have :=r_post_1.symm.trans h
        have := (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans this
        have eq1:= this.mul_left  ((Field51_as_Nat constants.SQRT_M1) ^3)
        rw[← mul_assoc] at eq1
        have :Field51_as_Nat constants.SQRT_M1 ^ 3 * Field51_as_Nat constants.SQRT_M1 ≡ 1 [MOD p] := by
          unfold constants.SQRT_M1
          decide
        have eq1 := (this.mul_right (Field51_as_Nat r_0 ^ 2)).symm.trans eq1
        have :Field51_as_Nat constants.SQRT_M1 ^ 3 * (p-1) ≡  Field51_as_Nat constants.SQRT_M1 [MOD p] := by
          unfold constants.SQRT_M1
          decide
        have eq1:= (eq1.trans this).pow 2
        simp[← pow_mul] at eq1
        have :Field51_as_Nat constants.SQRT_M1 ^ 2  ≡   (p-1) [MOD p] := by
          unfold constants.SQRT_M1
          decide
        have := eq1.trans this
        have := (SQRT_M1_not_square (Field51_as_Nat r_0)) this
        apply False.elim this
      · have : ¬ Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ 0 [MOD p] := by
          unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
          decide
        have := this h
        apply False.elim this
    · by_cases h1: Field51_as_Nat D % p = 0
      · simp_all
        grind
      · by_cases h2 : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p = Field51_as_Nat N_s % p
        · simp_all
          grind
        ·
          simp[h, h1] at __discr_post
          simp at h2
          simp[h2] at __discr_post
          have:=__discr_post.right.right

          intro i hi
          interval_cases i
          all_goals (expand this with 5; simp [*];grind)
    -- END TASK
  · -- BEGIN TASK
    by_cases first_choice: c.val = 1#u8
    · -- BEGIN TASK
      simp[first_choice]
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · -- BEGIN TASK
        expand s_prime_post_2 with 5
        grind
        -- END TASK
      · -- BEGIN TASK
        rename_i y hx5 hx4 hx3 hx2  hx1 x1
        simp[Choice.zero]
        by_cases second_choice :y.1.val = 1#u8
        · -- BEGIN TASK
          simp_all[second_choice]
          progress*
          · grind
          · unfold ONE
            decide
          · simp at c2_post
            unfold constants.MINUS_ONE at c2_post
            expand c2_post with 5
            intro i hi
            interval_cases i
            all_goals(simp_all; decide)
          · grind
          · grind
          · unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
            decide
          · grind
          · grind
          · -- BEGIN TASK
            simp at s1_post
            expand s1_post with 5
            simp_all
            by_cases h: Field51_as_Nat N_s % p = 0
            · rw[← modEq_zero_iff] at h
              have :=(h.symm.trans N_s_post_1).symm
              have := mul_zero_eq_or prime_25519 this
              rcases this with h | h
              ·
                have : Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE := by
                  simp[Field51_as_Nat, Finset.sum_range_succ]
                  simp_all
                  grind
                rw[this] at h
                have : Field51_as_Nat ONE =1 := by
                  unfold ONE
                  decide
                rw[this] at h
                have h:=h.add_right (p-1)
                rw[add_assoc] at h
                have : 1+(p-1)=p := by unfold p; scalar_tac
                rw[this] at h
                simp at h
                have :=r_post_1.symm.trans h
                have := (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans this
                have eq1:= this.mul_left  ((Field51_as_Nat constants.SQRT_M1) ^3)
                rw[← mul_assoc] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * Field51_as_Nat constants.SQRT_M1 ≡ 1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1 := (this.mul_right (Field51_as_Nat r_0 ^ 2)).symm.trans eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * (p-1) ≡  Field51_as_Nat constants.SQRT_M1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1:= (eq1.trans this).pow 2
                simp[← pow_mul] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 2  ≡   (p-1) [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have := eq1.trans this
                have := (SQRT_M1_not_square (Field51_as_Nat r_0)) this
                apply False.elim this
              · have : ¬ Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ 0 [MOD p] := by
                  unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                  decide
                have := this h
                apply False.elim this
            · by_cases h1: Field51_as_Nat D % p = 0
              · simp_all
              · by_cases h2 : ∃ x, x ^ 2 * (Field51_as_Nat D % p) % p = Field51_as_Nat N_s % p
                · simp_all
                  grind
                ·
                  simp[h, h1] at __discr_post
                  simp at h2
                  simp[h2] at __discr_post
            -- END TASK
          · simp at s1_post
            expand s1_post with 5
            simp_all
            by_cases h: Field51_as_Nat N_s % p = 0
            · rw[← modEq_zero_iff] at h
              have :=(h.symm.trans N_s_post_1).symm
              have := mul_zero_eq_or prime_25519 this
              rcases this with h | h
              ·
                have : Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE := by
                  simp[Field51_as_Nat, Finset.sum_range_succ]
                  simp_all
                  grind
                rw[this] at h
                have : Field51_as_Nat ONE =1 := by
                  unfold ONE
                  decide
                rw[this] at h
                have h:=h.add_right (p-1)
                rw[add_assoc] at h
                have : 1+(p-1)=p := by unfold p; scalar_tac
                rw[this] at h
                simp at h
                have :=r_post_1.symm.trans h
                have := (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans this
                have eq1:= this.mul_left  ((Field51_as_Nat constants.SQRT_M1) ^3)
                rw[← mul_assoc] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * Field51_as_Nat constants.SQRT_M1 ≡ 1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1 := (this.mul_right (Field51_as_Nat r_0 ^ 2)).symm.trans eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * (p-1) ≡  Field51_as_Nat constants.SQRT_M1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1:= (eq1.trans this).pow 2
                simp[← pow_mul] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 2  ≡   (p-1) [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have := eq1.trans this
                have := (SQRT_M1_not_square (Field51_as_Nat r_0)) this
                apply False.elim this
              · have : ¬ Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ 0 [MOD p] := by
                  unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                  decide
                have := this h
                apply False.elim this
            · obtain ⟨ a, ha⟩  := __discr_post h
              have := (__discr h a ha).right
              grind
          ·
            -- BEGIN TASK
            simp at s1_post
            simp_all
            by_cases h: Field51_as_Nat N_s % p = 0
            · rw[← modEq_zero_iff] at h
              have :=(h.symm.trans N_s_post_1).symm
              have := mul_zero_eq_or prime_25519 this
              rcases this with h | h
              ·
                have : Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE := by
                  simp[Field51_as_Nat, Finset.sum_range_succ]
                  simp_all
                  grind
                rw[this] at h
                have : Field51_as_Nat ONE =1 := by
                  unfold ONE
                  decide
                rw[this] at h
                have h:=h.add_right (p-1)
                rw[add_assoc] at h
                have : 1+(p-1)=p := by unfold p; scalar_tac
                rw[this] at h
                simp at h
                have :=r_post_1.symm.trans h
                have := (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans this
                have eq1:= this.mul_left  ((Field51_as_Nat constants.SQRT_M1) ^3)
                rw[← mul_assoc] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * Field51_as_Nat constants.SQRT_M1 ≡ 1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1 := (this.mul_right (Field51_as_Nat r_0 ^ 2)).symm.trans eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 3 * (p-1) ≡  Field51_as_Nat constants.SQRT_M1 [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have eq1:= (eq1.trans this).pow 2
                simp[← pow_mul] at eq1
                have :Field51_as_Nat constants.SQRT_M1 ^ 2  ≡   (p-1) [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have := eq1.trans this
                have := (SQRT_M1_not_square (Field51_as_Nat r_0)) this
                apply False.elim this
              · have : ¬ Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ 0 [MOD p] := by
                  unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                  decide
                have := this h
                apply False.elim this
            · obtain ⟨ a, ha⟩  := __discr_post h
              have := (__discr h a ha).right
              grind
            -- END TASK
          · grind
          · grind
          · unfold constants.SQRT_AD_MINUS_ONE
            decide
          · unfold ONE
            decide
          · grind
          · unfold ONE
            decide
          · grind
          · simp
            intro i hi
            interval_cases i
            all_goals(simp; expand fe9_post_2 with 5; grind)
          · simp
            intro i hi
            interval_cases i
            all_goals(simp; expand fe11_post_1 with 5; grind)
          · simp
            intro i hi
            interval_cases i
            all_goals(simp; expand fe10_post_2 with 5; grind)
          · -- BEGIN TASK
            unfold RistrettoPoint.IsValid curve25519_dalek.edwards.EdwardsPoint.IsValid
            simp_all
            rename_i X  heq_x heq_y
            constructor
            · -- BEGIN TASK
              intro hz
              rw[← Nat.ModEq] at ep
              have := mul_zero_eq_or prime_25519 (ep.symm.trans hz)
              rcases this with hl | hr
              · -- BEGIN TASK
                have hN_t:= mul_zero_eq_or prime_25519 (fe10_post_1.symm.trans hl)
                have : ¬ Field51_as_Nat constants.SQRT_AD_MINUS_ONE ≡ 0 [MOD p] := by
                  unfold constants.SQRT_AD_MINUS_ONE
                  decide
                simp[this] at hN_t
                rw[← Nat.ModEq] at N_t_post_2
                have := N_t_post_2.symm.trans (hN_t.add_right (Field51_as_Nat D))
                have := fe7_post_1.symm.trans this
                have eq1:= (fe6_post_1.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED)).symm.trans this
                have :Field51_as_Nat c2 = p-1 := by
                   simp_all [Field51_as_Nat , Finset.sum_range_succ]
                   unfold constants.MINUS_ONE
                   decide
                simp[this] at eq1
                have eq1:= eq1.trans D_post_1
                have :Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  grind
                rw[this] at eq1
                have :Field51_as_Nat ONE =1 := by
                  unfold ONE
                  decide
                rw[← Nat.ModEq, this] at fe5_post_2
                have hfe5:= fe5_post_2.add_right (p-1)
                have : 1+ (p-1) =p := by unfold p; scalar_tac
                simp[add_assoc, this] at hfe5
                have hfe5:= hfe5.mul_left (p-1)
                simp[mul_add] at hfe5
                have : (p-1) *(p-1) ≡ 1 [MOD p] := by unfold p; decide
                have := this.add_left ((p - 1) * Field51_as_Nat r)
                have eq1:= eq1.symm.trans ((hfe5.trans this).mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED))
                have :Field51_as_Nat constants.MINUS_ONE = p-1 := by
                   unfold constants.MINUS_ONE
                   decide
                rw[← Nat.ModEq, this] at fe3_post_2
                have eq2:= fe3_post_2.add (fe2_post_1.mul_left (p-1))
                have :Field51_as_Nat fe2 + (p - 1) * Field51_as_Nat fe2= p * Field51_as_Nat fe2 := by
                  unfold p
                  grind
                simp[add_assoc, this] at eq2
                have eq2:= eq2.mul_right ((Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D))
                have eq2:= eq2.symm.trans eq1
                have : Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED ≡ (d - 1)^2 [MOD p] := by
                  unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
                  decide
                have := this.mul_left ((p - 1) * Field51_as_Nat r + 1)
                have eq2:= eq2.trans this
                have :Field51_as_Nat constants.EDWARDS_D = d := by
                  unfold constants.EDWARDS_D
                  decide
                rw[this] at eq2
                have eq2:= eq2.add_left ((1 +  (d * Field51_as_Nat r)) * (Field51_as_Nat r + d))
                have : (1 + d * Field51_as_Nat r) * (Field51_as_Nat r + d) +
                  (p - 1 + (p - 1) * (d * Field51_as_Nat r)) * (Field51_as_Nat r + d)
                  = p * ((1 +  (d * Field51_as_Nat r)) * (Field51_as_Nat r + d)) := by grind
                simp[this] at eq2
                have : p * ((1 +  (d * Field51_as_Nat r)) * (Field51_as_Nat r + d)) ≡ 0 [MOD p] := by
                  simp[Nat.modEq_zero_iff_dvd ]
                have :=eq2.symm.trans this








                -- END TASK
              · -- BEGIN TASK
                have : Field51_as_Nat fe12 = Field51_as_Nat s_sq +Field51_as_Nat ONE := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  grind
                rw[this] at hr
                have : Field51_as_Nat ONE = 1 := by
                  unfold ONE
                  decide
                rw[this] at hr
                have hr:= hr.add_right (p-1)
                have : 1+ (p-1) =p := by unfold p; scalar_tac
                simp[add_assoc, this] at hr
                have hr:= s_sq_post_1.symm.trans hr
                have : Field51_as_Nat s1 =  Field51_as_Nat y.2 := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at hr








                -- END TASK


              -- END TASK







            -- END TASK
          -- END TASK
        · -- BEGIN TASK
          -- END TASK
        -- END TASK



      -- END TASK
    · -- BEGIN TASK

      -- END TASK


















    -- END TASK















end curve25519_dalek.ristretto.RistrettoPoint
