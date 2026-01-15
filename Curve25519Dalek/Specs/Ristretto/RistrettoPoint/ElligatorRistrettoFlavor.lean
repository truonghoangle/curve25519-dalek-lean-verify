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
import Curve25519Dalek.Defs.Edwards.Curve
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
theorem curveField_mod_eq (a b : ℕ) : ((a : Edwards.CurveField ) = (b : Edwards.CurveField )) ↔  (a % p = b % p)  := by
  exact (ZMod.natCast_eq_natCast_iff a b p)


theorem curveField_add (a b c d : ℕ)
  (h : (b : Edwards.CurveField ) = (c : Edwards.CurveField )+ (d : Edwards.CurveField ) +  (a : Edwards.CurveField )) :
  Edwards.Ed25519.a * (a : Edwards.CurveField) + (b : Edwards.CurveField) = (c : Edwards.CurveField) + (d : Edwards.CurveField)
  := by
  simp only [Edwards.Ed25519]
  grind


theorem EDWARDS_D_not_square (x : ℕ) :
  ¬ (x ^ 2 ≡ d [MOD p]) := by
  have :legendreSym p ↑d = -1 := by norm_num [d, p]
  have:= (@legendreSym.eq_neg_one_iff'  p _ d).mp this
  rw[IsSquare] at this
  intro hd
  apply this
  use x
  rw[← Nat.cast_mul, (by grind : x * x =x^2), ZMod.natCast_eq_natCast_iff]
  apply hd.symm


theorem EDWARDS_D_one_square :
  ∃ (x : ℕ), x ^ 2 ≡ d +1 [MOD p] := by
  have:=(@legendreSym.eq_one_iff  p _ (d+1) (by unfold d p; decide)).mp (by norm_num [d, p])
  rw[IsSquare] at this
  obtain ⟨r, hr⟩ := this
  use r.val
  simp only [← ZMod.natCast_eq_natCast_iff, sq] at hr ⊢
  exact hr.symm





theorem ONE_MINUS_EDWARDS_D_SQUARED_not_zero : ¬ 1 + p - d ^ 2 % p ≡ 0 [MOD p] := by
 norm_num [d, p]


theorem complex_modular_congruence (r : ℕ) :
  ((r + (p - 1)) * (d - 1) ^ 2 + (p - 1 + (p - 1) * (d * r)) * (r + d)) ^ 2 *
    (d + 1) ≡
  d *
      ((p - 1) * ((1 + d * r) * (r + d) + (r + 1) * (1 + p - d ^ 2 % p))) ^
        2 +
    ((r + 1) * (1 + p - d ^ 2 % p) + (p - 1) * (1 + d * r) * (r+ d)) ^
      2 [MOD p] := by
      sorry

theorem complex_modular_congruenceI (r : ℕ) :
(r * (( r + (p - 1)) * (d - 1) ^ 2) +
        (p - 1) * ((p - 1) * (1 + d * r) * (r + d))) ^
      2 *
    (d + 1) ≡
  d *
      ((p - 1 + (p - 1) * (d *  r)) * (r + d) +
          (p - 1) * ( r * ((r + 1) * (1 + p - d ^ 2 % p)))) ^
        2 +
    ( r * ( r + 1) * (1 + p - d ^ 2 % p) +
        (p - 1 + (p - 1) * (d * r)) * ( r + d)) ^
      2 [MOD p] := by sorry




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
    unfold subtle.NotChoiceChoice.not
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
          sorry
/-
          simp_all
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
            unfold RistrettoPoint.IsValid
            simp_all
            rename_i X heq_x heq_y heq_z heq_t hlt_x hlt_y
            constructor
            · grind
            · grind
            · grind
            · grind

            · -- BEGIN TASK
              intro hz
              unfold field.FieldElement51.toField  at hz
              have hz:=(curveField_mod_eq (Field51_as_Nat X.Z) 0).mp hz
              rw[ ← Nat.ModEq] at hz
              rw[ ← Nat.ModEq] at heq_z
              have := mul_zero_eq_or prime_25519 (heq_z.symm.trans hz)
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
                have eq2:=eq2.symm.trans this
                simp[mul_add, add_mul] at eq2
                have : Field51_as_Nat r + d * Field51_as_Nat r * Field51_as_Nat r + (d + d * Field51_as_Nat r * d) +
                  ((p - 1) * Field51_as_Nat r * (d - 1) ^ 2 + (d - 1) ^ 2)
                = d * (Field51_as_Nat r +1) ^2 + ((d - 1) ^ 2) +  p *((d-1)^2 * Field51_as_Nat r) := by
                  calc
                    Field51_as_Nat r + d * Field51_as_Nat r * Field51_as_Nat r + (d + d * Field51_as_Nat r * d) +
                    ((p - 1) * Field51_as_Nat r * (d - 1) ^ 2 + (d - 1) ^ 2)
                     = d * Field51_as_Nat r * Field51_as_Nat r + (d^2 +1 +(p-1) *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d) :=by grind
                  _  = d * Field51_as_Nat r ^2 + (d^2 +1 +(p-1) *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d) := by grind
                  _  = d * Field51_as_Nat r ^2 + (2 *d    + p *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d)  := by
                    have :d^2 +1 +(p-1) *(d-1)^2 =2 *d    + p *(d-1)^2 := by
                      calc  d^2 +1 +(p-1) *(d-1)^2
                          = d^2 +1 - (d-1)^2 + p *(d-1)^2 := by unfold p; decide
                       _  = d^2 +1 - (d^2 - 2 *d +1)   + p *(d-1)^2 := by unfold d; decide
                       _  =  2 *d    + p *(d-1)^2 := by unfold d; decide
                    rw[this]
                  _  = d * Field51_as_Nat r ^2 + (2 *d    ) * Field51_as_Nat r + ((d - 1) ^ 2+d) +  p *((d-1)^2 * Field51_as_Nat r) := by  grind
                  _  = d * (Field51_as_Nat r +1) ^2 + ((d - 1) ^ 2) +  p *((d-1)^2 * Field51_as_Nat r) := by  grind
                simp[this] at eq2
                by_cases h: Field51_as_Nat r +1   ≡ 0 [MOD p]
                · have := (((h.pow 2).mul_left d).add_right ((d - 1) ^ 2)).symm.trans eq2
                  simp[(by grind : ∀ a: ℕ , a^2 =a* a)] at this
                  have := mul_zero_eq_or prime_25519 this
                  rcases this with h | h
                  all_goals (unfold d p at h; rw[Nat.ModEq] at h; grind)
                ·
                  have r_lt:∀ i < 5, r[i]!.val < 2 ^ 53 := by grind
                  have one_lt:(∀ i < 5, ONE[i]!.val < 2 ^ 53) := by unfold ONE; decide
                  obtain ⟨ add_r_1, hr1_ok, hr1, hr1_lt⟩  := field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add_spec  r  ONE  r_lt one_lt
                  have eq_add_r: Field51_as_Nat r + Field51_as_Nat ONE = Field51_as_Nat add_r_1 := by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  have :   Field51_as_Nat ONE =1 := by unfold ONE; decide
                  rw[this] at eq_add_r
                  rw[eq_add_r] at h
                  obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec add_r_1 hr1_lt
                  have : Field51_as_Nat add_r_1 % p ≠ 0 := by
                    intro hu1
                    apply h
                    rw[modEq_zero_iff]
                    apply hu1
                  have inv_1:= inv_1 this
                  rw[← modEq_one_iff] at inv_1
                  have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat add_r_1)).symm.trans inv_1).pow 2
                  simp[mul_comm, mul_pow] at inv_1
                  have eq20:= (inv_1.mul_left d).add_right ((d-1)^2 * (Field51_as_Nat inv)^2)
                  rw[← mul_assoc, ← add_mul] at eq20
                  rw[eq_add_r] at eq2
                  have eq3:= (eq2.mul_right ((Field51_as_Nat inv)^2)).symm.trans eq20
                  simp[] at eq3
                  have eq3:= eq3.add_right ((p-1)* (d - 1) ^ 2 *(Field51_as_Nat inv)^2)
                  rw[add_assoc] at eq3
                  have : (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 + (p - 1) * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 =
                    p  * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 := by unfold p; grind
                  simp[this] at eq3
                  have : d + p * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 ≡ d [MOD p] := by
                    rw[mul_assoc]
                    simp[Nat.modEq_iff_dvd]
                  have eq3:= eq3.trans this
                  have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                  have := this.mul_right  ((d - 1) ^ 2 * Field51_as_Nat inv ^ 2)
                  rw[← mul_assoc, ← mul_assoc] at this
                  have eq3:= this.trans eq3
                  rw[← mul_pow, ← mul_pow] at eq3
                  apply EDWARDS_D_not_square (Field51_as_Nat constants.SQRT_M1 * (d - 1) * Field51_as_Nat inv) eq3
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
                by_cases h: Field51_as_Nat N_s % p = 0
                · -- BEGIN TASK
                  rw[← modEq_zero_iff] at h
                  have := N_s_post_1.symm.trans h
                  have := mul_zero_eq_or prime_25519 this
                  rcases this with h | h
                  · -- BEGIN TASK
                    have r_lt:∀ i < 5, r[i]!.val < 2 ^ 53 := by grind
                    have one_lt:(∀ i < 5, ONE[i]!.val < 2 ^ 53) := by unfold ONE; decide
                    obtain ⟨ add_r_1, hr1_ok, hr1, hr1_lt⟩  := field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add_spec  r  ONE  r_lt one_lt
                    have eq_add_r: Field51_as_Nat r + Field51_as_Nat ONE = Field51_as_Nat fe1 := by
                      simp_all [Field51_as_Nat , Finset.sum_range_succ]
                      grind
                    have :   Field51_as_Nat ONE =1 := by unfold ONE; decide
                    rw[this] at eq_add_r
                    rw[← eq_add_r] at h
                    have h:= h.add_right (p-1)
                    rw[add_assoc] at h
                    have :1+ (p-1) =p := by unfold p; grind
                    rw[this] at h
                    simp at h
                    have h:= r_post_1.symm.trans h
                    have := (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1)).symm.trans h
                    have eq1:= this.mul_left (Field51_as_Nat constants.SQRT_M1 ^3)
                    rw[← mul_assoc] at eq1
                    have :Field51_as_Nat constants.SQRT_M1 ^3 * Field51_as_Nat constants.SQRT_M1  ≡ 1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                    have eq1:= (this.mul_right (Field51_as_Nat r_0 ^ 2)).symm.trans eq1
                    have : Field51_as_Nat constants.SQRT_M1 ^3 * (p-1)  ≡ Field51_as_Nat constants.SQRT_M1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                    have eq1:= (eq1.trans this).pow 2
                    simp[← pow_mul] at eq1
                    have : Field51_as_Nat constants.SQRT_M1 ^2  ≡ p-1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                    have := eq1.trans this
                    apply SQRT_M1_not_square (Field51_as_Nat r_0) this
                    -- END TASK
                  · -- BEGIN TASK
                    have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                      unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                      decide
                    have := this.symm.trans h
                    apply ONE_MINUS_EDWARDS_D_SQUARED_not_zero  this
                    -- END TASK

                  -- END TASK
                · -- BEGIN TASK
                  obtain ⟨check, hcheck ⟩  := __discr_post h
                  have := (__discr h check hcheck).left
                  rw[←  Nat.ModEq] at this
                  have := (mod_sq_mod_mul (Field51_as_Nat y.2) (Field51_as_Nat D) p).symm.trans this
                  have hr:= ((hr.mul_right (Field51_as_Nat D)).symm.trans this).trans N_s_post_1
                  have hr:= (D_post_1.mul_left (p-1)).symm.trans hr
                  have hfe4:Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  rw[hfe4] at hr
                  have :Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE:= by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  rw[this] at hr
                  have :Field51_as_Nat ONE =1 := by
                    unfold ONE
                    decide
                  rw[this, ← mul_assoc] at hr
                  rw[← Nat.ModEq] at fe3_post_2
                  have :Field51_as_Nat constants.MINUS_ONE =p-1 := by
                    unfold constants.MINUS_ONE
                    decide
                  rw[this] at fe3_post_2
                  have hl:= fe3_post_2.add_right 1
                  have p_eq:(p-1) +1=p :=by unfold p; simp
                  simp[p_eq] at hl
                  have hl:=hl.add_left ((p-1)* (Field51_as_Nat fe3))
                  rw[← add_assoc, ← add_assoc] at hl
                  simp[(by grind : (p - 1) * Field51_as_Nat fe3 + Field51_as_Nat fe3= ((p-1)+1)* Field51_as_Nat fe3), p_eq] at hl
                  simp[add_assoc] at hl
                  have hl:= (fe2_post_1.add_right 1).symm.trans hl
                  have hl:= (hl.mul_right ((Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D))).trans hr
                  have hd10: Field51_as_Nat constants.EDWARDS_D = d:= by
                    unfold constants.EDWARDS_D
                    decide
                  rw[hd10] at hl
                  have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                      unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                      decide
                  have := this.mul_left (Field51_as_Nat r + 1)
                  have hl:= hl.trans this
                  have :d ^ 2  ≡ d^2 % p [MOD p] :=by simp[Nat.ModEq]
                  have := this.mul_left (Field51_as_Nat r + 1)
                  have hl:= hl.add this
                  simp[← mul_add] at hl
                  have : 1 + p - d ^ 2 % p + d ^ 2 % p = 1+p := by
                    unfold p d
                    simp
                  rw[this] at hl
                  have : (Field51_as_Nat r + 1) * (1 + p) ≡ (Field51_as_Nat r + 1) [MOD p] := by
                    simp[mul_add, Nat.modEq_iff_dvd ]
                  have hl:=hl.trans this

                  simp[add_mul, mul_add] at hl
                  have : d * Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r + (d * Field51_as_Nat r * d + d) +
                    (Field51_as_Nat r * d ^ 2 + d ^ 2) =
                    Field51_as_Nat r + (d * Field51_as_Nat r^2  + 2* d^2 * Field51_as_Nat r  + d + d ^ 2) := by grind
                  rw[this] at hl
                  have hl:= Nat.ModEq.add_left_cancel' _ hl
                  have hl:= hl.add_right (d^3)
                  have :d * Field51_as_Nat r ^ 2 + 2 * d ^ 2 * Field51_as_Nat r + d + d ^ 2 + d ^ 3 =
                  d * (Field51_as_Nat r +d) ^ 2 + (d + d ^ 2) := by grind
                  rw[this] at hl
                  have : 1 + d ^ 3=(1 + d ^ 3 - d - d^2 ) +(d+d^2) := by
                    unfold d
                    simp
                  rw[this] at hl
                  have hl:= Nat.ModEq.add_right_cancel' _ hl
                  have :1 + d ^ 3 - d - d ^ 2 = (d+1)*(d-1)^2 := by
                    unfold d
                    simp
                  rw[this] at hl
                  by_cases  h: Field51_as_Nat r + d  ≡ 0 [MOD p]
                  · have := (((h.pow 2).mul_left d).symm.trans hl).symm
                    simp at this
                    have := mul_zero_eq_or prime_25519 this
                    rcases this with h | h
                    · rw[Nat.ModEq] at h
                      unfold d p at h
                      grind
                    · rw[Nat.ModEq] at h
                      unfold d p at h
                      grind

                  · rw[← hd10, ← hfe4] at h
                    have fe4_lt: (∀ i < 5, fe4[i]!.val < 2 ^ 54) := by
                      grind
                    obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec fe4  fe4_lt
                    have inv_1:= inv_1 h
                    rw[← modEq_one_iff] at inv_1
                    have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat fe4)).symm.trans inv_1).pow 2
                    simp[mul_pow, mul_comm] at inv_1
                    rw[← hd10, ← hfe4] at hl
                    rw[hd10] at hl
                    have := inv_1.mul_left d
                    rw[← mul_assoc] at this
                    have eq1:= (hl.mul_right (Field51_as_Nat inv ^2)).symm.trans this
                    obtain ⟨ dx, hdx⟩  :=EDWARDS_D_one_square
                    have := hdx.mul_right ((d - 1) ^ 2 * Field51_as_Nat inv ^ 2)
                    simp [← mul_assoc] at this
                    have := this.trans eq1
                    simp[← mul_pow] at this
                    apply EDWARDS_D_not_square _ this
                  -- END TASK
                -- END TASK
              -- END TASK

            · -- BEGIN TASK
              unfold field.FieldElement51.toField
              simp[← Nat.cast_mul , ZMod.natCast_eq_natCast_iff]
              rw[← Nat.ModEq] at heq_x
              rw[← Nat.ModEq] at heq_y
              rw[← Nat.ModEq] at heq_z
              rw[← Nat.ModEq] at heq_t
              apply (heq_x.mul heq_y).trans
              apply Nat.ModEq.trans _ (heq_t.mul heq_z).symm
              have :Field51_as_Nat fe9 * Field51_as_Nat fe12 * (Field51_as_Nat fe11 * Field51_as_Nat fe10) =
                Field51_as_Nat fe9 * Field51_as_Nat fe11 * (Field51_as_Nat fe10 * Field51_as_Nat fe12) := by grind
              rw[this]
              -- END TASK
            · -- EBEGIN TASK

              simp
              unfold field.FieldElement51.toField
              have :Edwards.Ed25519.d = d := by decide
              rw[this]
              rw[← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow]
              rw[mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul,  ← Nat.cast_mul]
              apply curveField_add
              rw[← Nat.cast_add,← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
              rw[← Nat.ModEq] at heq_x
              rw[← Nat.ModEq] at heq_y
              rw[← Nat.ModEq] at heq_z
              rw[← Nat.ModEq] at heq_t
              apply ((heq_y.pow 2).mul (heq_z.pow 2)).trans
              have := (heq_z.pow 4).add ((((heq_x.pow 2).mul (heq_y.pow 2))).mul_left d)
              have := (this.add ((heq_x.pow 2).mul (heq_z.pow 2)))
              rw[← mul_assoc] at this
              apply Nat.ModEq.trans _ this.symm
              simp[mul_pow]
              have :Field51_as_Nat fe10 ^ 4 * Field51_as_Nat fe12 ^ 4 +
              d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe11 ^ 2 * Field51_as_Nat fe10 ^ 2)) +
              Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2)
              = (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2 +
              d * (Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat fe11 ^ 2 )) +
              Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2) * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2) := by grind
              rw[this]
              apply Nat.ModEq.mul_right
              clear this
              clear this
              clear this
              clear this
              have : Field51_as_Nat fe12 = Field51_as_Nat s_sq +Field51_as_Nat ONE := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  scalar_tac
              rw[this]
              have :Field51_as_Nat ONE=1:= by unfold ONE; decide
              rw[this]
              rw[← Nat.ModEq, this] at fe11_post_2
              have p_add_1:1+ (p-1)= p:= by unfold p; decide
              have := fe11_post_2.add_right ((p-1)* (Field51_as_Nat s_sq))
              rw[add_assoc, (by grind: ∀ a:ℕ , a+ (p-1)*a =(1+(p-1))*a),p_add_1] at this
              simp at this
              have hfe11:=(this.pow 2)
              have hfe10:= fe10_post_1.pow 2
              rw[mul_pow] at hfe10
              have  : (Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2  ≡ (p-1) * (d +1) [MOD p] := by
                unfold constants.SQRT_AD_MINUS_ONE
                decide
              have hfe10:= hfe10.trans (this.mul_left (Field51_as_Nat N_t ^ 2))
              have hfe9:= fe9_post_1.pow 2
              rw[mul_pow] at hfe9
              apply  (hfe11.mul hfe10).trans
              have hfe10_1:=hfe10.mul_right ((Field51_as_Nat s_sq + 1) ^ 2)
              have :=(hfe11.mul_left d).add_right  ((Field51_as_Nat s_sq + 1) ^ 2)
              have re:= hfe10_1.add (hfe9.mul this)
              have : Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 +
                Field51_as_Nat fe9 ^ 2 * (d * Field51_as_Nat fe11 ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)
                = Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 + d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe11 ^ 2) +
                Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2:=by grind
              rw[← this]
              apply Nat.ModEq.trans _ re.symm
              apply Nat.ModEq.add_left_cancel' ((p-1)*(Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2))
              have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2 +
              Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
              (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)) =
              (1+(p - 1) ) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
              (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2) := by ring
              rw[this]; clear this
              simp[p_add_1]; clear this
              have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
              ((1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p-1)* (Field51_as_Nat s_sq + 1) ^ 2)* (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) := by ring
              rw[this]; clear this
              have : (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p - 1) * (Field51_as_Nat s_sq + 1) ^ 2
                = (1+(p-1))+ 4 * (p-1)* Field51_as_Nat s_sq + ((p-1)^2+ (p-1))* Field51_as_Nat s_sq ^ 2 := by ring
              rw[this,p_add_1] ; clear this
              have : (p - 1) ^ 2 + (p - 1) = p*(p -1) := by unfold p; decide
              rw[this]; clear this
              have : p + 4 * (p - 1) * Field51_as_Nat s_sq + p*(p  - 1) * Field51_as_Nat s_sq ^ 2 =
              4 * (p - 1) * Field51_as_Nat s_sq + p*(1+(p  - 1) * Field51_as_Nat s_sq ^ 2) := by ring
              rw[this, add_mul]; clear this
              have : p * (1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
               p *((1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)))) := by ring
              simp[this] ; clear this
              have : 4 * (p - 1) * Field51_as_Nat s_sq * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
              4 * (p - 1)^2 * Field51_as_Nat s_sq * Field51_as_Nat N_t ^ 2  * (d + 1) := by ring
              rw[this]; clear this
              have  : Field51_as_Nat fe8 ^ 2 = 4 * Field51_as_Nat y.2 ^ 2 := by
                simp_all [Field51_as_Nat , Finset.sum_range_succ]
                ring
              rw[this]; clear this
              by_cases h: Field51_as_Nat N_s % p = 0
              · have h1:=hx4 h
                rw[← modEq_zero_iff] at h1
                have  : Field51_as_Nat s1 =  Field51_as_Nat y.2  := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at s_sq_post_1
                have h2:= s_sq_post_1.trans (h1.pow 2)
                have:= ((h2.mul_left (4*(p-1)^2)).mul_right (Field51_as_Nat N_t ^ 2 * (d + 1)))
                simp[← mul_assoc] at this
                apply this.trans
                have :=((h1.pow 2).mul_left 4).mul_right (Field51_as_Nat D ^ 2 *
                (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2))
                simp[← mul_assoc] at this
                apply Nat.ModEq.symm
                exact this
              · obtain ⟨ xx, hxx⟩ := __discr_post h
                have := (__discr h xx hxx).left
                rw[← Nat.ModEq] at this
                have hy:= (mod_sq_mod_mul (Field51_as_Nat y.2) (Field51_as_Nat D) p).symm.trans this
                simp[mul_assoc]
                apply Nat.ModEq.mul_left 4
                simp[← mul_assoc]
                have  : Field51_as_Nat s1 =  Field51_as_Nat y.2  := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at s_sq_post_1
                have : (p-1)^2 ≡ 1 [MOD p]:= by unfold p; decide
                have := (this.mul s_sq_post_1).mul_right (Field51_as_Nat N_t ^ 2 * (d + 1))
                simp[← mul_assoc] at this
                apply Nat.ModEq.trans this
                simp[mul_assoc]
                apply Nat.ModEq.mul_left
                rw[← Nat.ModEq] at N_t_post_2
                have hNt:= N_t_post_2.add_right ((p-1)*Field51_as_Nat D)
                have : Field51_as_Nat N_t + Field51_as_Nat D + (p - 1) * Field51_as_Nat D =
                Field51_as_Nat N_t + (1+(p-1))*Field51_as_Nat D := by ring
                simp[this,p_add_1] at hNt; clear this
                have := hNt.pow 2
                have := fe6_post_1.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED)
                have eq1:= fe7_post_1.trans this
                have :Field51_as_Nat c2 = Field51_as_Nat constants.MINUS_ONE := by
                   simp_all [Field51_as_Nat , Finset.sum_range_succ]
                simp[this] at eq1
                have :Field51_as_Nat constants.MINUS_ONE  = p-1 := by
                  unfold constants.MINUS_ONE
                  decide
                rw[this] at eq1
                have :Field51_as_Nat ONE  = 1 := by
                  unfold ONE
                  decide
                rw[← Nat.ModEq, this] at fe5_post_2
                have hfe5:= fe5_post_2.add_right (p-1)
                have : 1+ (p-1) =p := by unfold p; scalar_tac
                simp[add_assoc, this] at hfe5
                have hfe5:= hfe5.mul_left (p-1)
                simp[mul_add] at hfe5
                have := (hfe5.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED))
                have eq1:= eq1.trans this
                have eq1:= hNt.trans (eq1.add_right ((p - 1) * Field51_as_Nat D ))
                rw[← mul_add, mul_assoc, ← mul_add] at eq1
                have :Field51_as_Nat constants.MINUS_ONE = p-1 := by
                   unfold constants.MINUS_ONE
                   decide
                rw[← Nat.ModEq, this] at fe3_post_2
                have eq2:= fe3_post_2.add (fe2_post_1.mul_left (p-1))
                have :Field51_as_Nat fe2 + (p - 1) * Field51_as_Nat fe2= p * Field51_as_Nat fe2 := by
                  unfold p
                  grind
                simp[add_assoc, this] at eq2
                have eq2:=D_post_1.trans (eq2.mul_right (Field51_as_Nat fe4))
                have :Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  ring
                rw[this] at eq2; clear this
                have : Field51_as_Nat constants.EDWARDS_D =d := by unfold constants.EDWARDS_D; decide
                rw[this] at eq2; clear this
                have := (eq2.add_left ((Field51_as_Nat r + (p - 1)) * Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED)).mul_left (p-1)
                have eq1:= eq1.trans this
                have : Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED ≡ (d - 1)^2 [MOD p] := by
                  unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
                  decide
                have := ((this.mul_left ((Field51_as_Nat r + (p - 1)))).add_right  ((p - 1 + (p - 1) * (d * Field51_as_Nat r)) * (Field51_as_Nat r + d))).mul_left (p-1)
                have eq1:= ((eq1.trans this).pow 2).mul_right (d+1)
                rw[mul_pow] at eq1
                have : (p-1)^2 ≡ 1 [MOD p]:= by unfold p; decide
                have := this.mul_right (((Field51_as_Nat r + (p - 1)) * (d - 1) ^ 2 +
                (p - 1 + (p - 1) * (d * Field51_as_Nat r)) * (Field51_as_Nat r + d)) ^ 2 * (d + 1))
                rw[← mul_assoc] at this
                have := eq1.trans this
                apply this.trans
                conv =>
                  rhs
                  rw[mul_add, (by ring : Field51_as_Nat D ^ 2 * (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2) =
                  d * (Field51_as_Nat D   + (p - 1) * (Field51_as_Nat s_sq * Field51_as_Nat D)  ) ^ 2), ← mul_pow, mul_add, (by ring :Field51_as_Nat D * Field51_as_Nat s_sq =Field51_as_Nat s_sq * Field51_as_Nat D )]
                  simp
                have :Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE:= by
                    clear *- fe1_post_1
                    simp_all[Field51_as_Nat , Finset.sum_range_succ]
                    grind
                rw[this] at N_s_post_1
                have :Field51_as_Nat ONE =1 := by
                    unfold ONE
                    decide
                rw[this] at N_s_post_1
                have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                      unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                      decide
                have eq1:=(((s_sq_post_1.mul_right (Field51_as_Nat D)).trans hy).trans (N_s_post_1)).trans (this.mul_left (Field51_as_Nat r + 1))
                have :(p - 1 + (p - 1) * (d * Field51_as_Nat r)) =
                (p - 1)*( 1+ d * Field51_as_Nat r) := by unfold p; ring
                rw[this] at eq2
                have eq3:= eq1.add eq2
                have := eq2.add (eq1.mul_left (p-1))
                simp[mul_assoc] at this
                rw[← mul_add] at this
                have := ((this.pow 2).mul_left d).add (eq3.pow 2)
                apply Nat.ModEq.trans _ this.symm
                simp
                apply complex_modular_congruence


              -- END TASK
            -- END TASK
          -- END TASK
-/
        · -- BEGIN TASK
          sorry
/-
          simp[second_choice,Choice.one ]
          progress*
          · grind
          · unfold ONE; decide
          · grind
          · grind
          · grind
          · unfold constants.EDWARDS_D_MINUS_ONE_SQUARED; decide
          · grind
          · grind
          · grind
          · grind
          · grind
          · grind
          · grind
          · unfold constants.SQRT_AD_MINUS_ONE; decide
          · grind
          · grind
          · unfold ONE; decide
          · grind
          · grind
          · grind
          · grind
          · unfold RistrettoPoint.IsValid
            simp_all
            rename_i X heq_x heq_y heq_z heq_t hlt_x hlt_y
            constructor
            · grind
            · grind
            · grind
            · grind
            · -- BEGIN TASK

              intro hz
              unfold field.FieldElement51.toField  at hz
              have hz:=(curveField_mod_eq (Field51_as_Nat X.Z) 0).mp hz
              rw[ ← Nat.ModEq] at hz
              rw[ ← Nat.ModEq] at heq_z
              have := mul_zero_eq_or prime_25519 (heq_z.symm.trans hz)
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
                have :Field51_as_Nat c2 = Field51_as_Nat r := by
                   simp_all [Field51_as_Nat , Finset.sum_range_succ]
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
                have hfe5:= hfe5.mul_left (Field51_as_Nat r)
                simp[mul_add] at hfe5
                have := (hfe5.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED))
                have eq1:= eq1.symm.trans this
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
                have := this.mul_left (Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r * (p - 1))
                have eq2:= eq2.trans this
                have :Field51_as_Nat constants.EDWARDS_D = d := by
                  unfold constants.EDWARDS_D
                  decide
                rw[this] at eq2
                have eq2:= eq2.add_right (Field51_as_Nat r * (d-1)^2)
                have : (Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r * (p - 1)) * (d - 1) ^ 2 + Field51_as_Nat r * (d - 1) ^ 2
                  = Field51_as_Nat r^2  * (d - 1) ^ 2 + (p - 1 +1) * (Field51_as_Nat r  * (d - 1) ^ 2) := by grind
                simp[this] at eq2
                have :  Field51_as_Nat r ^ 2 * (d - 1) ^ 2 + (p - 1 + 1) * (Field51_as_Nat r * (d - 1) ^ 2) ≡  Field51_as_Nat r ^ 2 * (d - 1) ^ 2  [MOD p] := by
                  have : p-1 +1 =p := by unfold p; decide
                  simp[this]
                have eq2:=eq2.trans this
                simp[mul_add, add_mul] at eq2
                have : (p - 1) * Field51_as_Nat r + (p - 1) * (d * Field51_as_Nat r) * Field51_as_Nat r +
                ((p - 1) * d + (p - 1) * (d * Field51_as_Nat r) * d) + Field51_as_Nat r * (d - 1) ^ 2 =
                (p - 1) * (d * Field51_as_Nat r^2)+ ((p - 1) * d + ((p - 1) * (d^2 +1) +(d - 1) ^ 2) * Field51_as_Nat r)  := by  grind
                rw[this] at eq2
                have :  (p - 1) * (d * Field51_as_Nat r ^ 2) + ((p - 1) * d + ((p - 1) * (d ^ 2 + 1) + (d - 1) ^ 2) * Field51_as_Nat r)
                ≡ d * (p-1) * (Field51_as_Nat r +1)^2 [MOD p] := by
                  have :d * (p - 1) * (Field51_as_Nat r + 1) ^ 2 =
                    (p - 1) * (d * Field51_as_Nat r ^ 2) + ((p - 1) * d + ((p - 1) * (2 * d ) * Field51_as_Nat r)):= by grind
                  rw[this]
                  apply Nat.ModEq.add_left
                  apply Nat.ModEq.add_left
                  apply Nat.ModEq.mul_right
                  apply Nat.ModEq.add_right_cancel' (2*d)
                  unfold d p; decide
                have eq2:=(this.symm.trans eq2).mul_left (p-1)
                have : (p - 1) * (d * (p - 1) * (Field51_as_Nat r + 1) ^ 2) =
                 (p - 1)^2 * (d *  (Field51_as_Nat r + 1) ^ 2) := by grind
                rw[this] at eq2
                have :(p - 1)^2 ≡ 1 [MOD p] := by unfold p; decide
                have eq2:= (this.mul_right (d *  (Field51_as_Nat r + 1) ^ 2)).symm.trans eq2
                simp at eq2
                have  :  p - 1 ≡(Field51_as_Nat constants.SQRT_M1)^2  [MOD p] := by
                  unfold constants.SQRT_M1
                  decide
                have := this.mul_right ((Field51_as_Nat r ^ 2 * (d - 1) ^ 2))
                have eq2:= eq2.trans this
                rw[←  mul_pow] at eq2
                by_cases h:  (Field51_as_Nat r +1)   ≡ 0 [MOD p]
                · have := ((((h.pow 2).mul_left d)).symm.trans eq2).symm
                  rw[←  mul_pow] at this
                  simp[(by grind : ∀ a: ℕ , a^2 =a* a)] at this
                  have := mul_zero_eq_or prime_25519 this
                  simp at this
                  have := mul_zero_eq_or prime_25519 this
                  rcases this with h1  | h1
                  · have eq2:= h1.pow 2
                    have : (Field51_as_Nat constants.SQRT_M1)^2 ≡ p-1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                    have := this.symm.trans  eq2
                    congr
                    unfold p at this
                    revert this
                    decide
                  · have := mul_zero_eq_or prime_25519 h1
                    rcases this with h1  | h1
                    · have eq2:= (h1.add_right 1).symm.trans h
                      unfold p at eq2
                      revert eq2
                      decide
                    · revert h1
                      unfold d p; decide
                · have r_lt:∀ i < 5, r[i]!.val < 2 ^ 53 := by grind
                  have one_lt:(∀ i < 5, ONE[i]!.val < 2 ^ 53) := by unfold ONE; decide
                  obtain ⟨ add_r_1, hr1_ok, hr1, hr1_lt⟩  := field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add_spec  r  ONE  r_lt one_lt
                  have eq_add_r: Field51_as_Nat r + Field51_as_Nat ONE = Field51_as_Nat add_r_1 := by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  have :   Field51_as_Nat ONE =1 := by unfold ONE; decide
                  rw[this] at eq_add_r
                  rw[eq_add_r] at h
                  obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec add_r_1 hr1_lt
                  have : Field51_as_Nat add_r_1 % p ≠ 0 := by
                    intro hu1
                    apply h
                    rw[modEq_zero_iff]
                    apply hu1
                  have inv_1:= inv_1 this
                  rw[← modEq_one_iff] at inv_1
                  have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat add_r_1)).symm.trans inv_1).pow 2
                  simp[mul_comm, mul_pow] at inv_1
                  have eq20:= (inv_1.mul_left d)
                  rw[← mul_assoc] at eq20
                  rw[eq_add_r] at eq2
                  have eq3:= (eq2.mul_right ((Field51_as_Nat inv)^2)).symm.trans eq20
                  simp[← mul_pow] at eq3
                  apply EDWARDS_D_not_square (Field51_as_Nat constants.SQRT_M1 * (Field51_as_Nat r * (d - 1)) * Field51_as_Nat inv) eq3
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
                simp_all[Choice.zero]
                have : Field51_as_Nat s1 =  Field51_as_Nat s_prime := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at hr
                have hr:= (s_prime_post_1.pow 2).symm.trans hr
                by_cases h: Field51_as_Nat D % p = 0
                · -- BEGIN TASK
                  have := (hx3 h).right.left
                  rw[← modEq_zero_iff] at this
                  have := ((this.mul_right (Field51_as_Nat r_0)).pow 2).symm.trans hr
                  simp at this
                  revert this
                  unfold p; decide
                  -- END TASK
                · -- BEGIN TASK
                  rw[mul_comm, mul_pow] at hr
                  have := (__discr_post h).right.left
                  rw[←  Nat.ModEq] at this
                  have := (mod_sq_mod_mul (Field51_as_Nat y.2) (Field51_as_Nat D) p).symm.trans this
                  have := this.mul_left (Field51_as_Nat r_0 ^ 2)
                  rw[← mul_assoc] at this
                  have hr:= ((hr.mul_right (Field51_as_Nat D)).symm.trans this)
                  rw[← mul_assoc] at hr
                  have hr:=hr.trans (N_s_post_1.mul_left (Field51_as_Nat r_0 ^ 2 * Field51_as_Nat constants.SQRT_M1))
                  have hr:= (D_post_1.mul_left (p-1)).symm.trans hr
                  have hfe4:Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  rw[hfe4] at hr
                  have :Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE:= by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  rw[this] at hr
                  have :Field51_as_Nat ONE =1 := by
                    unfold ONE
                    decide
                  rw[this, ← mul_assoc] at hr
                  rw[← Nat.ModEq] at fe3_post_2
                  have :Field51_as_Nat constants.MINUS_ONE =p-1 := by
                    unfold constants.MINUS_ONE
                    decide
                  rw[this] at fe3_post_2
                  have hl:= fe3_post_2.add_right 1
                  have p_eq:(p-1) +1=p :=by unfold p; simp
                  simp[p_eq] at hl
                  have hl:=hl.add_left ((p-1)* (Field51_as_Nat fe3))
                  rw[← add_assoc, ← add_assoc] at hl
                  simp[(by grind : (p - 1) * Field51_as_Nat fe3 + Field51_as_Nat fe3= ((p-1)+1)* Field51_as_Nat fe3), p_eq] at hl
                  simp[add_assoc] at hl
                  have hl_1:= (fe2_post_1.add_right 1).symm.trans hl
                  have hl:= (hl_1.mul_right ((Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D))).trans hr
                  have hd10: Field51_as_Nat constants.EDWARDS_D = d:= by
                    unfold constants.EDWARDS_D
                    decide
                  rw[hd10, ← mul_assoc] at hl
                  have :=r_post_1.trans (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1))
                  rw[mul_comm] at this
                  have hl:=hl.trans ((this.mul_right  (Field51_as_Nat r + 1)).mul_right ( Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED)).symm
                  have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                      unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                      decide
                  have := this.mul_left (Field51_as_Nat r *(Field51_as_Nat r + 1))
                  have hl:= hl.trans this
                  have :d ^ 2  ≡ d^2 % p [MOD p] :=by simp[Nat.ModEq]
                  have := this.mul_left (Field51_as_Nat r *(Field51_as_Nat r + 1))
                  have hl:= hl.add this
                  have :  Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p - d ^ 2 % p) +
                  Field51_as_Nat r * (Field51_as_Nat r + 1) * (d ^ 2 % p) =
                  Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p - d ^ 2 % p + d ^ 2 % p) := by ring
                  rw[this] at hl
                  have : 1 + p - d ^ 2 % p + d ^ 2 % p = 1+p := by
                    unfold p d
                    simp
                  rw[this] at hl
                  have : Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p) ≡Field51_as_Nat r * (Field51_as_Nat r + 1) [MOD p] := by
                    simp[mul_add, Nat.modEq_iff_dvd ]
                  have hl:=hl.trans this
                  simp[add_mul, mul_add] at hl
                  have : d * Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r + (d * Field51_as_Nat r * d + d) +
                    (Field51_as_Nat r * Field51_as_Nat r * d ^ 2 + Field51_as_Nat r * d ^ 2) =
                     Field51_as_Nat r +(        d *((d+1) * Field51_as_Nat r^2 + 2* d * Field51_as_Nat r  + 1))  := by ring
                  rw[this, (by ring : Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r
                  =Field51_as_Nat r + Field51_as_Nat r^2)] at hl
                  have hl:= Nat.ModEq.add_left_cancel' _ hl
                  have hl:= hl.add_right ((d^3 -d^2 -d) * Field51_as_Nat r^2)
                  have eq1:  d * ((d + 1) * Field51_as_Nat r ^ 2 + 2 * d * Field51_as_Nat r + 1) + (d ^ 3 - d ^ 2 - d) * Field51_as_Nat r ^ 2
                  =  ((d^3 -d^2 -d) + d^2 +d) * Field51_as_Nat r ^ 2 + d*(2 * d * Field51_as_Nat r + 1) := by ring
                  have : (d^3 -d^2 -d) + d^2 +d =d^3 := by unfold d; decide
                  rw[this] at eq1
                  have :d ^ 3 * Field51_as_Nat r ^ 2 + d * (2 * d * Field51_as_Nat r + 1) =
                  d*(d* Field51_as_Nat r +1)^2:= by ring
                  rw[this] at eq1
                  rw[eq1] at hl
                  have : Field51_as_Nat r ^ 2 + (d ^ 3 - d ^ 2 - d) * Field51_as_Nat r ^ 2
                  = (d ^ 3 - d ^ 2 - d+1) * Field51_as_Nat r ^ 2 := by ring
                  rw[this] at hl
                  have :d ^ 3 - d^2 - d +1 = (d+1)*(d-1)^2 := by
                    unfold d
                    simp
                  rw[this] at hl
                  by_cases  h: d*Field51_as_Nat r + 1  ≡ 0 [MOD p]
                  · have := (((h.pow 2).mul_left d).symm.trans hl).symm
                    simp at this
                    have := mul_zero_eq_or prime_25519 this
                    rcases this with h | h1
                    · rw[Nat.ModEq] at h
                      unfold d p at h
                      grind
                    · rw[(by grind : ∀ a, a^2 =a*a)] at h1
                      have := mul_zero_eq_or prime_25519 h1
                      simp at this
                      have := ((this.mul_left d).add_right 1).symm.trans h
                      simp at this
                      revert this
                      unfold p
                      decide
                  · rw[hd10] at hl_1
                    have : (d * Field51_as_Nat r + 1) ^ 2 ≡ (Field51_as_Nat fe3)^2 [MOD p]:= by
                      apply Nat.ModEq.trans (hl_1.pow 2)
                      rw[mul_pow]
                      conv =>
                        rhs
                        rw [(by simp : Field51_as_Nat fe3 ^ 2  = 1* Field51_as_Nat fe3 ^ 2)]
                      apply Nat.ModEq.mul_right
                      unfold p
                      decide
                    have hl:= (this.mul_left d).symm.trans hl

                    have h: ¬ Field51_as_Nat fe3 ≡ 0 [MOD p] := by
                      intro h1
                      have := h1.mul_left (p-1)
                      simp at this
                      apply h
                      apply Nat.ModEq.trans hl_1 this
                    have : (∀ i < 5, fe3[i]!.val < 2 ^ 54) := by grind
                    obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec fe3 this
                    have : Field51_as_Nat fe3 % p ≠ 0 := by
                      intro hu1
                      apply h
                      rw[modEq_zero_iff]
                      apply hu1
                    have inv_1:= inv_1 this
                    rw[← modEq_one_iff] at inv_1
                    have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat fe3)).symm.trans inv_1).pow 2
                    simp[mul_comm, mul_pow] at inv_1
                    have inv_1:= inv_1.mul_left d
                    rw[← mul_assoc] at inv_1
                    have hl:=inv_1.symm.trans (hl.mul_right (Field51_as_Nat inv ^ 2))
                    simp at hl
                    obtain ⟨ dx, hdx⟩  :=EDWARDS_D_one_square
                    have := hdx.mul_right ((d - 1) ^ 2 *  Field51_as_Nat r ^ 2 * Field51_as_Nat inv ^ 2)
                    simp [← mul_assoc] at this
                    have := this.trans hl.symm
                    simp[← mul_pow] at this
                    apply EDWARDS_D_not_square _ this
                  -- END TASK

                -- END TASK
            · -- BEGIN TASK
              unfold field.FieldElement51.toField
              simp[← Nat.cast_mul , ZMod.natCast_eq_natCast_iff]
              rw[← Nat.ModEq] at heq_x
              rw[← Nat.ModEq] at heq_y
              rw[← Nat.ModEq] at heq_z
              rw[← Nat.ModEq] at heq_t
              apply (heq_x.mul heq_y).trans
              apply Nat.ModEq.trans _ (heq_t.mul heq_z).symm
              have :Field51_as_Nat fe9 * Field51_as_Nat fe12 * (Field51_as_Nat fe11 * Field51_as_Nat fe10) =
                Field51_as_Nat fe9 * Field51_as_Nat fe11 * (Field51_as_Nat fe10 * Field51_as_Nat fe12) := by grind
              rw[this]
              -- END TASK
            · -- EBEGIN TASK

              simp
              unfold field.FieldElement51.toField
              have :Edwards.Ed25519.d = d := by decide
              rw[this]
              rw[← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow]
              rw[mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul,  ← Nat.cast_mul]
              apply curveField_add
              rw[← Nat.cast_add,← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
              rw[← Nat.ModEq] at heq_x
              rw[← Nat.ModEq] at heq_y
              rw[← Nat.ModEq] at heq_z
              rw[← Nat.ModEq] at heq_t
              apply ((heq_y.pow 2).mul (heq_z.pow 2)).trans
              have := (heq_z.pow 4).add ((((heq_x.pow 2).mul (heq_y.pow 2))).mul_left d)
              have := (this.add ((heq_x.pow 2).mul (heq_z.pow 2)))
              rw[← mul_assoc] at this
              apply Nat.ModEq.trans _ this.symm
              simp[mul_pow]
              have :Field51_as_Nat fe10 ^ 4 * Field51_as_Nat fe12 ^ 4 +
              d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe11 ^ 2 * Field51_as_Nat fe10 ^ 2)) +
              Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2)
              = (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2 +
              d * (Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat fe11 ^ 2 )) +
              Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2) * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2) := by grind
              rw[this]
              apply Nat.ModEq.mul_right
              clear this
              clear this
              clear this
              clear this
              have : Field51_as_Nat fe12 = Field51_as_Nat s_sq +Field51_as_Nat ONE := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  scalar_tac
              rw[this]
              have :Field51_as_Nat ONE=1:= by unfold ONE; decide
              rw[this]
              rw[← Nat.ModEq, this] at fe11_post_2
              have p_add_1:1+ (p-1)= p:= by unfold p; decide
              have := fe11_post_2.add_right ((p-1)* (Field51_as_Nat s_sq))
              rw[add_assoc, (by grind: ∀ a:ℕ , a+ (p-1)*a =(1+(p-1))*a),p_add_1] at this
              simp at this
              have hfe11:=(this.pow 2)
              have hfe10:= fe10_post_1.pow 2
              rw[mul_pow] at hfe10
              have  : (Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2  ≡ (p-1) * (d +1) [MOD p] := by
                unfold constants.SQRT_AD_MINUS_ONE
                decide
              have hfe10:= hfe10.trans (this.mul_left (Field51_as_Nat N_t ^ 2))
              have hfe9:= fe9_post_1.pow 2
              rw[mul_pow] at hfe9
              apply  (hfe11.mul hfe10).trans
              have hfe10_1:=hfe10.mul_right ((Field51_as_Nat s_sq + 1) ^ 2)
              have :=(hfe11.mul_left d).add_right  ((Field51_as_Nat s_sq + 1) ^ 2)
              have re:= hfe10_1.add (hfe9.mul this)
              have : Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 +
                Field51_as_Nat fe9 ^ 2 * (d * Field51_as_Nat fe11 ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)
                = Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 + d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe11 ^ 2) +
                Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2:=by grind
              rw[← this]
              apply Nat.ModEq.trans _ re.symm
              apply Nat.ModEq.add_left_cancel' ((p-1)*(Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2))
              have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2 +
              Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
              (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)) =
              (1+(p - 1) ) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
              (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2) := by ring
              rw[this]; clear this
              simp[p_add_1]; clear this
              have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
              (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
              ((1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p-1)* (Field51_as_Nat s_sq + 1) ^ 2)* (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) := by ring
              rw[this]; clear this
              have : (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p - 1) * (Field51_as_Nat s_sq + 1) ^ 2
                = (1+(p-1))+ 4 * (p-1)* Field51_as_Nat s_sq + ((p-1)^2+ (p-1))* Field51_as_Nat s_sq ^ 2 := by ring
              rw[this,p_add_1] ; clear this
              have : (p - 1) ^ 2 + (p - 1) = p*(p -1) := by unfold p; decide
              rw[this]; clear this
              have : p + 4 * (p - 1) * Field51_as_Nat s_sq + p*(p  - 1) * Field51_as_Nat s_sq ^ 2 =
              4 * (p - 1) * Field51_as_Nat s_sq + p*(1+(p  - 1) * Field51_as_Nat s_sq ^ 2) := by ring
              rw[this, add_mul]; clear this
              have : p * (1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
               p *((1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)))) := by ring
              simp[this] ; clear this
              have : 4 * (p - 1) * Field51_as_Nat s_sq * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
              4 * (p - 1)^2 * Field51_as_Nat s_sq * Field51_as_Nat N_t ^ 2  * (d + 1) := by ring
              rw[this]; clear this
              simp[Choice.zero] at fe8_post_1
              simp[Choice.zero] at s1_post
              have  : Field51_as_Nat s1 = Field51_as_Nat s_prime := by
                simp_all [Field51_as_Nat , Finset.sum_range_succ]
              rw[this] at s_sq_post_1
              have hs_sq:=s_sq_post_1.trans (s_prime_post_1.pow 2)
              simp[Choice.zero] at s_prime1_post
              have  : Field51_as_Nat fe8 ^ 2 = 4 * Field51_as_Nat s_prime ^ 2 := by
                simp_all [Field51_as_Nat , Finset.sum_range_succ]
                ring
              rw[this]; clear this
              simp[mul_assoc]
              apply Nat.ModEq.mul_left 4
              simp[← mul_assoc]
              have : (p-1)^2 ≡ 1 [MOD p]:= by unfold p; decide
              have := (this.mul s_sq_post_1).mul_right (Field51_as_Nat N_t ^ 2 * (d + 1))
              simp[← mul_assoc] at this
              apply Nat.ModEq.trans this
              simp[mul_assoc]
              by_cases h: Field51_as_Nat D % p = 0
              · have h1:=(hx3 h).right.left
                rw[← modEq_zero_iff] at h1
                have :=s_prime_post_1.trans (h1.mul_right (Field51_as_Nat r_0))
                have eq1:= this.pow 2
                simp at eq1
                apply (eq1.mul_right (Field51_as_Nat N_t ^ 2 * (d + 1))).trans
                apply Nat.ModEq.trans _ (eq1.mul_right ((Field51_as_Nat D ^ 2 * (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)))).symm
                simp
                decide
              · apply Nat.ModEq.mul_left
                rw[← Nat.ModEq] at N_t_post_2
                have hNt:= N_t_post_2.add_right ((p-1)*Field51_as_Nat D)
                have : Field51_as_Nat N_t + Field51_as_Nat D + (p - 1) * Field51_as_Nat D =
                Field51_as_Nat N_t + (1+(p-1))*Field51_as_Nat D := by ring
                simp[this,p_add_1] at hNt; clear this
                have := hNt.pow 2
                have := fe6_post_1.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED)
                have eq1:= fe7_post_1.trans this
                have :Field51_as_Nat c2 = Field51_as_Nat r := by
                   simp_all [Field51_as_Nat , Finset.sum_range_succ]
                simp[this] at eq1
                have :Field51_as_Nat ONE  = 1 := by
                  unfold ONE
                  decide
                rw[← Nat.ModEq, this] at fe5_post_2
                have hfe5:= fe5_post_2.add_right (p-1)
                have : 1+ (p-1) =p := by unfold p; scalar_tac
                simp[add_assoc, this] at hfe5
                have hfe5:= hfe5.mul_left (Field51_as_Nat r)
                simp[mul_add] at hfe5
                have := (hfe5.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED))
                have eq1:= eq1.trans this
                have eq1:= hNt.trans (eq1.add_right ((p - 1) * Field51_as_Nat D ))
                rw[← mul_add, mul_assoc] at eq1
                have :Field51_as_Nat constants.MINUS_ONE = p-1 := by
                   unfold constants.MINUS_ONE
                   decide
                rw[← Nat.ModEq, this] at fe3_post_2
                have eq2:= fe3_post_2.add (fe2_post_1.mul_left (p-1))
                have :Field51_as_Nat fe2 + (p - 1) * Field51_as_Nat fe2= p * Field51_as_Nat fe2 := by
                  unfold p
                  grind
                simp[add_assoc, this] at eq2
                have eq2:=D_post_1.trans (eq2.mul_right (Field51_as_Nat fe4))
                have :Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  ring
                rw[this] at eq2; clear this
                have : Field51_as_Nat constants.EDWARDS_D =d := by unfold constants.EDWARDS_D; decide
                rw[this] at eq2; clear this
                have : Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED ≡ (d - 1)^2 [MOD p] := by
                  unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
                  decide
                have := this.mul_left ( Field51_as_Nat r * ((Field51_as_Nat r + (p - 1))))
                rw[mul_assoc] at this
                have := this.add (eq2.mul_left (p-1))
                have eq1:= eq1.trans this
                apply ((eq1.pow 2).mul_right (d+1)).trans
                have :=(__discr_post h).right.left
                rw[← Nat.ModEq] at this
                have hy:= (mod_sq_mod_mul (Field51_as_Nat y.2) (Field51_as_Nat D) p).symm.trans this
                simp[mul_assoc]
                conv =>
                  rhs
                  rw[mul_add, (by ring : Field51_as_Nat D ^ 2 * (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2) =
                  d * (Field51_as_Nat D   + (p - 1) * (Field51_as_Nat s_sq * Field51_as_Nat D)  ) ^ 2), ← mul_pow, mul_add, (by ring :Field51_as_Nat D * Field51_as_Nat s_sq =Field51_as_Nat s_sq * Field51_as_Nat D )]
                  simp
                have :Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE:= by
                    clear *- fe1_post_1
                    simp_all[Field51_as_Nat , Finset.sum_range_succ]
                    grind
                rw[this] at N_s_post_1
                have :Field51_as_Nat ONE =1 := by
                    unfold ONE
                    decide
                rw[this] at N_s_post_1
                have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                      unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                      decide
                have hone:= this.mul_left (Field51_as_Nat r * (Field51_as_Nat r + 1))
                rw[mul_assoc] at hone
                have eq1:=(hs_sq.mul_right (Field51_as_Nat D))
                rw[mul_pow, (by grind :∀ a b c :ℕ, a * b * c =b *(a*c))] at eq1
                have hy:=hy.mul_left (Field51_as_Nat r_0 ^2)
                have : Field51_as_Nat r_0 ^ 2 * (Field51_as_Nat constants.SQRT_M1 * Field51_as_Nat N_s) =
                 (Field51_as_Nat constants.SQRT_M1 *Field51_as_Nat r_0 ^ 2 ) * Field51_as_Nat N_s := by ring
                rw[this] at hy
                have := (r_post_1.trans (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1))).mul_right (Field51_as_Nat N_s)
                have hy:= hy.trans this.symm
                have eq1:= (eq1.trans hy).trans (N_s_post_1.mul_left (Field51_as_Nat r))
                have eq1:=eq1.trans hone
                have :(p - 1 + (p - 1) * (d * Field51_as_Nat r)) =
                (p - 1)*( 1+ d * Field51_as_Nat r) := by unfold p; ring
                rw[this]
                have eq3:= eq1.add eq2
                have := eq2.add (eq1.mul_left (p-1))
                simp[mul_assoc] at this
                have := ((this.pow 2).mul_left d).add (eq3.pow 2)
                apply Nat.ModEq.trans _ this.symm
                apply complex_modular_congruenceI
              -- END TASK

-/


          -- END TASK
        -- END TASK



      -- END TASK
    · -- BEGIN TASK
      rename_i con h1 h2 h3 h4
      simp_all
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · grind
      · by_cases h:  Field51_as_Nat N_s % p = 0
        · -- BEGIN TASK
          sorry
/-
          have := (h2 h).left
          simp[this]
          progress*
          · grind
          · unfold ONE; decide
          · simp_all[Choice.zero]
            unfold constants.MINUS_ONE
            decide
          · grind
          · grind
          · unfold constants.EDWARDS_D_MINUS_ONE_SQUARED
            decide
          · grind
          · grind
          · simp_all[Choice.zero]
            grind
          · grind
          · grind
          · grind
          · grind
          · unfold constants.SQRT_AD_MINUS_ONE; decide
          · unfold ONE; decide
          · grind
          · unfold ONE; decide
          · grind
          · simp_all; grind
          · simp_all; grind
          · simp_all; grind
          · unfold RistrettoPoint.IsValid
            simp_all[Choice.zero]
            rename_i X heq_x heq_y heq_z heq_t hlt_x hlt_y
            constructor
            · grind
            · grind
            · grind
            · grind
            · -- BEGIN TASK
              intro hz
              unfold field.FieldElement51.toField  at hz
              have hz:=(curveField_mod_eq (Field51_as_Nat X.Z) 0).mp hz
              rw[ ← Nat.ModEq] at hz
              rw[ ← Nat.ModEq] at heq_z
              have := mul_zero_eq_or prime_25519 (heq_z.symm.trans hz)
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
                have eq2:=eq2.symm.trans this
                simp[mul_add, add_mul] at eq2
                have : Field51_as_Nat r + d * Field51_as_Nat r * Field51_as_Nat r + (d + d * Field51_as_Nat r * d) +
                  ((p - 1) * Field51_as_Nat r * (d - 1) ^ 2 + (d - 1) ^ 2)
                = d * (Field51_as_Nat r +1) ^2 + ((d - 1) ^ 2) +  p *((d-1)^2 * Field51_as_Nat r) := by
                  calc
                    Field51_as_Nat r + d * Field51_as_Nat r * Field51_as_Nat r + (d + d * Field51_as_Nat r * d) +
                    ((p - 1) * Field51_as_Nat r * (d - 1) ^ 2 + (d - 1) ^ 2)
                     = d * Field51_as_Nat r * Field51_as_Nat r + (d^2 +1 +(p-1) *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d) :=by grind
                  _  = d * Field51_as_Nat r ^2 + (d^2 +1 +(p-1) *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d) := by grind
                  _  = d * Field51_as_Nat r ^2 + (2 *d    + p *(d-1)^2) * Field51_as_Nat r + ((d - 1) ^ 2+d)  := by
                    have :d^2 +1 +(p-1) *(d-1)^2 =2 *d    + p *(d-1)^2 := by
                      calc  d^2 +1 +(p-1) *(d-1)^2
                          = d^2 +1 - (d-1)^2 + p *(d-1)^2 := by unfold p; decide
                       _  = d^2 +1 - (d^2 - 2 *d +1)   + p *(d-1)^2 := by unfold d; decide
                       _  =  2 *d    + p *(d-1)^2 := by unfold d; decide
                    rw[this]
                  _  = d * Field51_as_Nat r ^2 + (2 *d    ) * Field51_as_Nat r + ((d - 1) ^ 2+d) +  p *((d-1)^2 * Field51_as_Nat r) := by  grind
                  _  = d * (Field51_as_Nat r +1) ^2 + ((d - 1) ^ 2) +  p *((d-1)^2 * Field51_as_Nat r) := by  grind
                simp[this] at eq2
                by_cases h: Field51_as_Nat r +1   ≡ 0 [MOD p]
                · have := (((h.pow 2).mul_left d).add_right ((d - 1) ^ 2)).symm.trans eq2
                  simp[(by grind : ∀ a: ℕ , a^2 =a* a)] at this
                  have := mul_zero_eq_or prime_25519 this
                  rcases this with h | h
                  all_goals (unfold d p at h; rw[Nat.ModEq] at h; grind)
                ·
                  have r_lt:∀ i < 5, r[i]!.val < 2 ^ 53 := by grind
                  have one_lt:(∀ i < 5, ONE[i]!.val < 2 ^ 53) := by unfold ONE; decide
                  obtain ⟨ add_r_1, hr1_ok, hr1, hr1_lt⟩  := field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add_spec  r  ONE  r_lt one_lt
                  have eq_add_r: Field51_as_Nat r + Field51_as_Nat ONE = Field51_as_Nat add_r_1 := by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                    grind
                  have :   Field51_as_Nat ONE =1 := by unfold ONE; decide
                  rw[this] at eq_add_r
                  rw[eq_add_r] at h
                  obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec add_r_1 hr1_lt
                  have : Field51_as_Nat add_r_1 % p ≠ 0 := by
                    intro hu1
                    apply h
                    rw[modEq_zero_iff]
                    apply hu1
                  have inv_1:= inv_1 this
                  rw[← modEq_one_iff] at inv_1
                  have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat add_r_1)).symm.trans inv_1).pow 2
                  simp[mul_comm, mul_pow] at inv_1
                  have eq20:= (inv_1.mul_left d).add_right ((d-1)^2 * (Field51_as_Nat inv)^2)
                  rw[← mul_assoc, ← add_mul] at eq20
                  rw[eq_add_r] at eq2
                  have eq3:= (eq2.mul_right ((Field51_as_Nat inv)^2)).symm.trans eq20
                  simp[] at eq3
                  have eq3:= eq3.add_right ((p-1)* (d - 1) ^ 2 *(Field51_as_Nat inv)^2)
                  rw[add_assoc] at eq3
                  have : (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 + (p - 1) * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 =
                    p  * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 := by unfold p; grind
                  simp[this] at eq3
                  have : d + p * (d - 1) ^ 2 * Field51_as_Nat inv ^ 2 ≡ d [MOD p] := by
                    rw[mul_assoc]
                    simp[Nat.modEq_iff_dvd]
                  have eq3:= eq3.trans this
                  have : (Field51_as_Nat constants.SQRT_M1) ^2 ≡ p-1 [MOD p] := by
                      unfold constants.SQRT_M1
                      decide
                  have := this.mul_right  ((d - 1) ^ 2 * Field51_as_Nat inv ^ 2)
                  rw[← mul_assoc, ← mul_assoc] at this
                  have eq3:= this.trans eq3
                  rw[← mul_pow, ← mul_pow] at eq3
                  apply EDWARDS_D_not_square (Field51_as_Nat constants.SQRT_M1 * (d - 1) * Field51_as_Nat inv) eq3
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
                have : Field51_as_Nat s1 =  Field51_as_Nat con.2 := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at hr
                have hp:=h2.left
                rw[←  modEq_zero_iff] at hp
                have :=(hp.pow 2).symm.trans hr
                unfold p at this
                norm_num at this

                -- END TASK


              -- END TASK
            · -- BEGIN TASK
              unfold field.FieldElement51.toField
              simp[← Nat.cast_mul , ZMod.natCast_eq_natCast_iff]
              rw[← Nat.ModEq] at heq_x
              rw[← Nat.ModEq] at heq_y
              rw[← Nat.ModEq] at heq_z
              rw[← Nat.ModEq] at heq_t
              apply (heq_x.mul heq_y).trans
              apply Nat.ModEq.trans _ (heq_t.mul heq_z).symm
              have :Field51_as_Nat fe9 * Field51_as_Nat fe12 * (Field51_as_Nat fe11 * Field51_as_Nat fe10) =
                Field51_as_Nat fe9 * Field51_as_Nat fe11 * (Field51_as_Nat fe10 * Field51_as_Nat fe12) := by grind
              rw[this]
              -- END TASK
            · -- EBEGIN TASK

                simp
                unfold field.FieldElement51.toField
                have :Edwards.Ed25519.d = d := by decide
                rw[this]
                rw[← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow]
                rw[mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul,  ← Nat.cast_mul]
                apply curveField_add
                rw[← Nat.cast_add,← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
                rw[← Nat.ModEq] at heq_x
                rw[← Nat.ModEq] at heq_y
                rw[← Nat.ModEq] at heq_z
                rw[← Nat.ModEq] at heq_t
                apply ((heq_y.pow 2).mul (heq_z.pow 2)).trans
                have := (heq_z.pow 4).add ((((heq_x.pow 2).mul (heq_y.pow 2))).mul_left d)
                have := (this.add ((heq_x.pow 2).mul (heq_z.pow 2)))
                rw[← mul_assoc] at this
                apply Nat.ModEq.trans _ this.symm
                simp[mul_pow]
                have :Field51_as_Nat fe10 ^ 4 * Field51_as_Nat fe12 ^ 4 +
                d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe11 ^ 2 * Field51_as_Nat fe10 ^ 2)) +
                Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2 * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2)
                = (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2 +
                d * (Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat fe11 ^ 2 )) +
                Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe12 ^ 2) * (Field51_as_Nat fe10 ^ 2 * Field51_as_Nat fe12 ^ 2) := by grind
                rw[this]
                apply Nat.ModEq.mul_right
                clear this
                clear this
                clear this
                clear this
                have : Field51_as_Nat fe12 = Field51_as_Nat s_sq +Field51_as_Nat ONE := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  scalar_tac
                rw[this]
                have :Field51_as_Nat ONE=1:= by unfold ONE; decide
                rw[this]
                rw[← Nat.ModEq, this] at fe11_post_2
                have p_add_1:1+ (p-1)= p:= by unfold p; decide
                have := fe11_post_2.add_right ((p-1)* (Field51_as_Nat s_sq))
                rw[add_assoc, (by grind: ∀ a:ℕ , a+ (p-1)*a =(1+(p-1))*a),p_add_1] at this
                simp at this
                have hfe11:=(this.pow 2)
                have hfe10:= fe10_post_1.pow 2
                rw[mul_pow] at hfe10
                have  : (Field51_as_Nat constants.SQRT_AD_MINUS_ONE)^2  ≡ (p-1) * (d +1) [MOD p] := by
                  unfold constants.SQRT_AD_MINUS_ONE
                  decide
                have hfe10:= hfe10.trans (this.mul_left (Field51_as_Nat N_t ^ 2))
                have hfe9:= fe9_post_1.pow 2
                rw[mul_pow] at hfe9
                apply  (hfe11.mul hfe10).trans
                have hfe10_1:=hfe10.mul_right ((Field51_as_Nat s_sq + 1) ^ 2)
                have :=(hfe11.mul_left d).add_right  ((Field51_as_Nat s_sq + 1) ^ 2)
                have re:= hfe10_1.add (hfe9.mul this)
                have : Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 +
                  Field51_as_Nat fe9 ^ 2 * (d * Field51_as_Nat fe11 ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)
                  = Field51_as_Nat fe10 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2 + d * (Field51_as_Nat fe9 ^ 2 * Field51_as_Nat fe11 ^ 2) +
                  Field51_as_Nat fe9 ^ 2 * (Field51_as_Nat s_sq + 1) ^ 2:=by grind
                rw[← this]
                apply Nat.ModEq.trans _ re.symm
                apply Nat.ModEq.add_left_cancel' ((p-1)*(Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2))
                have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
                (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2 +
                Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
                (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2)) =
                (1+(p - 1) ) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
                Field51_as_Nat fe8 ^ 2 * Field51_as_Nat D ^ 2 *
                (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2) := by ring
                rw[this]; clear this
                simp[p_add_1]; clear this
                have : (p - 1) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)) * (Field51_as_Nat s_sq + 1) ^ 2) +
                (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
                ((1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p-1)* (Field51_as_Nat s_sq + 1) ^ 2)* (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) := by ring
                rw[this]; clear this
                have : (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (p - 1) * (Field51_as_Nat s_sq + 1) ^ 2
                = (1+(p-1))+ 4 * (p-1)* Field51_as_Nat s_sq + ((p-1)^2+ (p-1))* Field51_as_Nat s_sq ^ 2 := by ring
                rw[this,p_add_1] ; clear this
                have : (p - 1) ^ 2 + (p - 1) = p*(p -1) := by unfold p; decide
                rw[this]; clear this
                have : p + 4 * (p - 1) * Field51_as_Nat s_sq + p*(p  - 1) * Field51_as_Nat s_sq ^ 2 =
                4 * (p - 1) * Field51_as_Nat s_sq + p*(1+(p  - 1) * Field51_as_Nat s_sq ^ 2) := by ring
                rw[this, add_mul]; clear this
                have : p * (1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
                p *((1 + (p - 1) * Field51_as_Nat s_sq ^ 2) * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1)))) := by ring
                simp[this] ; clear this
                have : 4 * (p - 1) * Field51_as_Nat s_sq * (Field51_as_Nat N_t ^ 2 * ((p - 1) * (d + 1))) =
                4 * (p - 1)^2 * Field51_as_Nat s_sq * Field51_as_Nat N_t ^ 2  * (d + 1) := by ring
                rw[this]; clear this
                have  : Field51_as_Nat fe8 ^ 2 = 4 * Field51_as_Nat con.2 ^ 2 := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  ring
                rw[this]; clear this
                simp[mul_assoc]
                apply Nat.ModEq.mul_left 4
                simp[← mul_assoc]
                have hp:=h2.left
                rw[←  modEq_zero_iff] at hp
                have := (hp.pow 2).mul_right (Field51_as_Nat D ^ 2 *
                (d * (1 + (p - 1) * Field51_as_Nat s_sq) ^ 2 + (Field51_as_Nat s_sq + 1) ^ 2))
                rw[← mul_assoc] at this
                apply Nat.ModEq.trans _ this.symm
                simp
                have : Field51_as_Nat s1 =  Field51_as_Nat con.2 := by
                  simp_all [Field51_as_Nat , Finset.sum_range_succ]
                rw[this] at s_sq_post_1
                have := s_sq_post_1.trans (hp.pow 2)
                have := (this.mul_left ((p-1)^2)).mul_right  (Field51_as_Nat N_t ^ 2 * (d + 1))
                simp[← mul_assoc] at this
                exact this

              -- END TASK
            -- END TASK





-/




          -- END TASK

        · -- BEGIN TASK
          by_cases hD: Field51_as_Nat D % p = 0
          · -- BEGIN TASK
            have := (h3 h hD).left
            simp[this]
            progress*
            · grind
            · grind
            · simp_all[Choice.one]
              grind
            · grind
            · grind
            · unfold constants.EDWARDS_D_MINUS_ONE_SQUARED; decide
            · grind
            · grind
            · grind
            · grind
            · grind
            · grind
            · grind
            · unfold constants.SQRT_AD_MINUS_ONE; decide
            · grind
            · grind
            · unfold ONE; decide
            · grind
            · simp_all; grind
            · simp_all; grind
            · simp_all; grind
            · unfold RistrettoPoint.IsValid
              simp_all[Choice.zero, Choice.one]
              rename_i X heq_x heq_y heq_z heq_t hlt_x hlt_y
              constructor
              · grind
              · grind
              · grind
              · grind
              · -- BEGIN TASK
                intro hz
                unfold field.FieldElement51.toField  at hz
                have hz:=(curveField_mod_eq (Field51_as_Nat X.Z) 0).mp hz
                rw[ ← Nat.ModEq] at hz
                rw[ ← Nat.ModEq] at heq_z
                have := mul_zero_eq_or prime_25519 (heq_z.symm.trans hz)
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
                  have :Field51_as_Nat c2 = Field51_as_Nat r := by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
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
                  have hfe5:= hfe5.mul_left (Field51_as_Nat r)
                  simp[mul_add] at hfe5
                  have := (hfe5.mul_right (Field51_as_Nat constants.EDWARDS_D_MINUS_ONE_SQUARED))
                  have eq1:= eq1.symm.trans this
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
                  have := this.mul_left (Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r * (p - 1))
                  have eq2:= eq2.trans this
                  have :Field51_as_Nat constants.EDWARDS_D = d := by
                    unfold constants.EDWARDS_D
                    decide
                  rw[this] at eq2
                  have eq2:= eq2.add_right (Field51_as_Nat r * (d-1)^2)
                  have : (Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r * (p - 1)) * (d - 1) ^ 2 + Field51_as_Nat r * (d - 1) ^ 2
                    = Field51_as_Nat r^2  * (d - 1) ^ 2 + (p - 1 +1) * (Field51_as_Nat r  * (d - 1) ^ 2) := by grind
                  simp[this] at eq2
                  have :  Field51_as_Nat r ^ 2 * (d - 1) ^ 2 + (p - 1 + 1) * (Field51_as_Nat r * (d - 1) ^ 2) ≡  Field51_as_Nat r ^ 2 * (d - 1) ^ 2  [MOD p] := by
                    have : p-1 +1 =p := by unfold p; decide
                    simp[this]
                  have eq2:=eq2.trans this
                  simp[mul_add, add_mul] at eq2
                  have : (p - 1) * Field51_as_Nat r + (p - 1) * (d * Field51_as_Nat r) * Field51_as_Nat r +
                  ((p - 1) * d + (p - 1) * (d * Field51_as_Nat r) * d) + Field51_as_Nat r * (d - 1) ^ 2 =
                  (p - 1) * (d * Field51_as_Nat r^2)+ ((p - 1) * d + ((p - 1) * (d^2 +1) +(d - 1) ^ 2) * Field51_as_Nat r)  := by  grind
                  rw[this] at eq2
                  have :  (p - 1) * (d * Field51_as_Nat r ^ 2) + ((p - 1) * d + ((p - 1) * (d ^ 2 + 1) + (d - 1) ^ 2) * Field51_as_Nat r)
                  ≡ d * (p-1) * (Field51_as_Nat r +1)^2 [MOD p] := by
                    have :d * (p - 1) * (Field51_as_Nat r + 1) ^ 2 =
                      (p - 1) * (d * Field51_as_Nat r ^ 2) + ((p - 1) * d + ((p - 1) * (2 * d ) * Field51_as_Nat r)):= by grind
                    rw[this]
                    apply Nat.ModEq.add_left
                    apply Nat.ModEq.add_left
                    apply Nat.ModEq.mul_right
                    apply Nat.ModEq.add_right_cancel' (2*d)
                    unfold d p; decide
                  have eq2:=(this.symm.trans eq2).mul_left (p-1)
                  have : (p - 1) * (d * (p - 1) * (Field51_as_Nat r + 1) ^ 2) =
                  (p - 1)^2 * (d *  (Field51_as_Nat r + 1) ^ 2) := by grind
                  rw[this] at eq2
                  have :(p - 1)^2 ≡ 1 [MOD p] := by unfold p; decide
                  have eq2:= (this.mul_right (d *  (Field51_as_Nat r + 1) ^ 2)).symm.trans eq2
                  simp at eq2
                  have  :  p - 1 ≡(Field51_as_Nat constants.SQRT_M1)^2  [MOD p] := by
                    unfold constants.SQRT_M1
                    decide
                  have := this.mul_right ((Field51_as_Nat r ^ 2 * (d - 1) ^ 2))
                  have eq2:= eq2.trans this
                  rw[←  mul_pow] at eq2
                  by_cases h:  (Field51_as_Nat r +1)   ≡ 0 [MOD p]
                  · have := ((((h.pow 2).mul_left d)).symm.trans eq2).symm
                    rw[←  mul_pow] at this
                    simp[(by grind : ∀ a: ℕ , a^2 =a* a)] at this
                    have := mul_zero_eq_or prime_25519 this
                    simp at this
                    have := mul_zero_eq_or prime_25519 this
                    rcases this with h1  | h1
                    · have eq2:= h1.pow 2
                      have : (Field51_as_Nat constants.SQRT_M1)^2 ≡ p-1 [MOD p] := by
                        unfold constants.SQRT_M1
                        decide
                      have := this.symm.trans  eq2
                      congr
                      unfold p at this
                      revert this
                      decide
                    · have := mul_zero_eq_or prime_25519 h1
                      rcases this with h1  | h1
                      · have eq2:= (h1.add_right 1).symm.trans h
                        unfold p at eq2
                        revert eq2
                        decide
                      · revert h1
                        unfold d p; decide
                  · have r_lt:∀ i < 5, r[i]!.val < 2 ^ 53 := by grind
                    have one_lt:(∀ i < 5, ONE[i]!.val < 2 ^ 53) := by unfold ONE; decide
                    obtain ⟨ add_r_1, hr1_ok, hr1, hr1_lt⟩  := field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add_spec  r  ONE  r_lt one_lt
                    have eq_add_r: Field51_as_Nat r + Field51_as_Nat ONE = Field51_as_Nat add_r_1 := by
                      simp_all [Field51_as_Nat , Finset.sum_range_succ]
                      grind
                    have :   Field51_as_Nat ONE =1 := by unfold ONE; decide
                    rw[this] at eq_add_r
                    rw[eq_add_r] at h
                    obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec add_r_1 hr1_lt
                    have : Field51_as_Nat add_r_1 % p ≠ 0 := by
                      intro hu1
                      apply h
                      rw[modEq_zero_iff]
                      apply hu1
                    have inv_1:= inv_1 this
                    rw[← modEq_one_iff] at inv_1
                    have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat add_r_1)).symm.trans inv_1).pow 2
                    simp[mul_comm, mul_pow] at inv_1
                    have eq20:= (inv_1.mul_left d)
                    rw[← mul_assoc] at eq20
                    rw[eq_add_r] at eq2
                    have eq3:= (eq2.mul_right ((Field51_as_Nat inv)^2)).symm.trans eq20
                    simp[← mul_pow] at eq3
                    apply EDWARDS_D_not_square (Field51_as_Nat constants.SQRT_M1 * (Field51_as_Nat r * (d - 1)) * Field51_as_Nat inv) eq3
                  -- END TASK
                · -- BEGIN TASK
                  sorry
/-

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
                  simp_all[Choice.zero]
                  have : Field51_as_Nat s1 =  Field51_as_Nat s_prime := by
                    simp_all [Field51_as_Nat , Finset.sum_range_succ]
                  rw[this] at hr
                  have hr:= (s_prime_post_1.pow 2).symm.trans hr
                  by_cases h: Field51_as_Nat D % p = 0
                  · -- BEGIN TASK
                    have := (hx3 h).right.left
                    rw[← modEq_zero_iff] at this
                    have := ((this.mul_right (Field51_as_Nat r_0)).pow 2).symm.trans hr
                    simp at this
                    revert this
                    unfold p; decide
                    -- END TASK
                  · -- BEGIN TASK
                    rw[mul_comm, mul_pow] at hr
                    have := (__discr_post h).right.left
                    rw[←  Nat.ModEq] at this
                    have := (mod_sq_mod_mul (Field51_as_Nat y.2) (Field51_as_Nat D) p).symm.trans this
                    have := this.mul_left (Field51_as_Nat r_0 ^ 2)
                    rw[← mul_assoc] at this
                    have hr:= ((hr.mul_right (Field51_as_Nat D)).symm.trans this)
                    rw[← mul_assoc] at hr
                    have hr:=hr.trans (N_s_post_1.mul_left (Field51_as_Nat r_0 ^ 2 * Field51_as_Nat constants.SQRT_M1))
                    have hr:= (D_post_1.mul_left (p-1)).symm.trans hr
                    have hfe4:Field51_as_Nat fe4 = Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D:= by
                      simp_all [Field51_as_Nat , Finset.sum_range_succ]
                      grind
                    rw[hfe4] at hr
                    have :Field51_as_Nat fe1 = Field51_as_Nat r + Field51_as_Nat ONE:= by
                      simp_all [Field51_as_Nat , Finset.sum_range_succ]
                      grind
                    rw[this] at hr
                    have :Field51_as_Nat ONE =1 := by
                      unfold ONE
                      decide
                    rw[this, ← mul_assoc] at hr
                    rw[← Nat.ModEq] at fe3_post_2
                    have :Field51_as_Nat constants.MINUS_ONE =p-1 := by
                      unfold constants.MINUS_ONE
                      decide
                    rw[this] at fe3_post_2
                    have hl:= fe3_post_2.add_right 1
                    have p_eq:(p-1) +1=p :=by unfold p; simp
                    simp[p_eq] at hl
                    have hl:=hl.add_left ((p-1)* (Field51_as_Nat fe3))
                    rw[← add_assoc, ← add_assoc] at hl
                    simp[(by grind : (p - 1) * Field51_as_Nat fe3 + Field51_as_Nat fe3= ((p-1)+1)* Field51_as_Nat fe3), p_eq] at hl
                    simp[add_assoc] at hl
                    have hl_1:= (fe2_post_1.add_right 1).symm.trans hl
                    have hl:= (hl_1.mul_right ((Field51_as_Nat r + Field51_as_Nat constants.EDWARDS_D))).trans hr
                    have hd10: Field51_as_Nat constants.EDWARDS_D = d:= by
                      unfold constants.EDWARDS_D
                      decide
                    rw[hd10, ← mul_assoc] at hl
                    have :=r_post_1.trans (fe_post_1.mul_left (Field51_as_Nat constants.SQRT_M1))
                    rw[mul_comm] at this
                    have hl:=hl.trans ((this.mul_right  (Field51_as_Nat r + 1)).mul_right ( Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED)).symm
                    have : Field51_as_Nat constants.ONE_MINUS_EDWARDS_D_SQUARED ≡ (1 + p - (d^2 % p)) [MOD p] := by
                        unfold constants.ONE_MINUS_EDWARDS_D_SQUARED
                        decide
                    have := this.mul_left (Field51_as_Nat r *(Field51_as_Nat r + 1))
                    have hl:= hl.trans this
                    have :d ^ 2  ≡ d^2 % p [MOD p] :=by simp[Nat.ModEq]
                    have := this.mul_left (Field51_as_Nat r *(Field51_as_Nat r + 1))
                    have hl:= hl.add this
                    have :  Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p - d ^ 2 % p) +
                    Field51_as_Nat r * (Field51_as_Nat r + 1) * (d ^ 2 % p) =
                    Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p - d ^ 2 % p + d ^ 2 % p) := by ring
                    rw[this] at hl
                    have : 1 + p - d ^ 2 % p + d ^ 2 % p = 1+p := by
                      unfold p d
                      simp
                    rw[this] at hl
                    have : Field51_as_Nat r * (Field51_as_Nat r + 1) * (1 + p) ≡Field51_as_Nat r * (Field51_as_Nat r + 1) [MOD p] := by
                      simp[mul_add, Nat.modEq_iff_dvd ]
                    have hl:=hl.trans this
                    simp[add_mul, mul_add] at hl
                    have : d * Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r + (d * Field51_as_Nat r * d + d) +
                      (Field51_as_Nat r * Field51_as_Nat r * d ^ 2 + Field51_as_Nat r * d ^ 2) =
                      Field51_as_Nat r +(        d *((d+1) * Field51_as_Nat r^2 + 2* d * Field51_as_Nat r  + 1))  := by ring
                    rw[this, (by ring : Field51_as_Nat r * Field51_as_Nat r + Field51_as_Nat r
                    =Field51_as_Nat r + Field51_as_Nat r^2)] at hl
                    have hl:= Nat.ModEq.add_left_cancel' _ hl
                    have hl:= hl.add_right ((d^3 -d^2 -d) * Field51_as_Nat r^2)
                    have eq1:  d * ((d + 1) * Field51_as_Nat r ^ 2 + 2 * d * Field51_as_Nat r + 1) + (d ^ 3 - d ^ 2 - d) * Field51_as_Nat r ^ 2
                    =  ((d^3 -d^2 -d) + d^2 +d) * Field51_as_Nat r ^ 2 + d*(2 * d * Field51_as_Nat r + 1) := by ring
                    have : (d^3 -d^2 -d) + d^2 +d =d^3 := by unfold d; decide
                    rw[this] at eq1
                    have :d ^ 3 * Field51_as_Nat r ^ 2 + d * (2 * d * Field51_as_Nat r + 1) =
                    d*(d* Field51_as_Nat r +1)^2:= by ring
                    rw[this] at eq1
                    rw[eq1] at hl
                    have : Field51_as_Nat r ^ 2 + (d ^ 3 - d ^ 2 - d) * Field51_as_Nat r ^ 2
                    = (d ^ 3 - d ^ 2 - d+1) * Field51_as_Nat r ^ 2 := by ring
                    rw[this] at hl
                    have :d ^ 3 - d^2 - d +1 = (d+1)*(d-1)^2 := by
                      unfold d
                      simp
                    rw[this] at hl
                    by_cases  h: d*Field51_as_Nat r + 1  ≡ 0 [MOD p]
                    · have := (((h.pow 2).mul_left d).symm.trans hl).symm
                      simp at this
                      have := mul_zero_eq_or prime_25519 this
                      rcases this with h | h1
                      · rw[Nat.ModEq] at h
                        unfold d p at h
                        grind
                      · rw[(by grind : ∀ a, a^2 =a*a)] at h1
                        have := mul_zero_eq_or prime_25519 h1
                        simp at this
                        have := ((this.mul_left d).add_right 1).symm.trans h
                        simp at this
                        revert this
                        unfold p
                        decide
                    · rw[hd10] at hl_1
                      have : (d * Field51_as_Nat r + 1) ^ 2 ≡ (Field51_as_Nat fe3)^2 [MOD p]:= by
                        apply Nat.ModEq.trans (hl_1.pow 2)
                        rw[mul_pow]
                        conv =>
                          rhs
                          rw [(by simp : Field51_as_Nat fe3 ^ 2  = 1* Field51_as_Nat fe3 ^ 2)]
                        apply Nat.ModEq.mul_right
                        unfold p
                        decide
                      have hl:= (this.mul_left d).symm.trans hl

                      have h: ¬ Field51_as_Nat fe3 ≡ 0 [MOD p] := by
                        intro h1
                        have := h1.mul_left (p-1)
                        simp at this
                        apply h
                        apply Nat.ModEq.trans hl_1 this
                      have : (∀ i < 5, fe3[i]!.val < 2 ^ 54) := by grind
                      obtain ⟨ inv, inv_ok, inv_1, inv_2 ⟩  := invert_spec fe3 this
                      have : Field51_as_Nat fe3 % p ≠ 0 := by
                        intro hu1
                        apply h
                        rw[modEq_zero_iff]
                        apply hu1
                      have inv_1:= inv_1 this
                      rw[← modEq_one_iff] at inv_1
                      have inv_1:= ((mod_mul_mod (Field51_as_Nat inv) (Field51_as_Nat fe3)).symm.trans inv_1).pow 2
                      simp[mul_comm, mul_pow] at inv_1
                      have inv_1:= inv_1.mul_left d
                      rw[← mul_assoc] at inv_1
                      have hl:=inv_1.symm.trans (hl.mul_right (Field51_as_Nat inv ^ 2))
                      simp at hl
                      obtain ⟨ dx, hdx⟩  :=EDWARDS_D_one_square
                      have := hdx.mul_right ((d - 1) ^ 2 *  Field51_as_Nat r ^ 2 * Field51_as_Nat inv ^ 2)
                      simp [← mul_assoc] at this
                      have := this.trans hl.symm
                      simp[← mul_pow] at this
                      apply EDWARDS_D_not_square _ this
                    -- END TASK

-/

                -- END TASK
              · sorry
              · sorry











            -- END TASK
          · -- BEGIN TASK
            sorry
            -- END TASK





          -- END TASK











      -- END TASK


















    -- END TASK













end curve25519_dalek.ristretto.RistrettoPoint
