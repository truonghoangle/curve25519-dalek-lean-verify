/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Field.FieldElement51.PowP58
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.SQRT_M1
/-! # Spec Theorem for `FieldElement51::sqrt_ratio_i`

Specification and proof for `FieldElement51::sqrt_ratio_i`.

This function computes a nonnegative square root of u/v or i*u/v (where i = sqrt(-1) = SQRT_M1 constant),
returning a flag indicating which case occurred and handling zero inputs specially.

**Source**: curve25519-dalek/src/field.rs

## TODO
- Complete proof
-/



open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.field.FieldElement51


theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

theorem mod_two_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  a % 2 = 1 := by simp [Nat.ModEq]

theorem mod_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  ¬(a ≡ 0 [MOD 2]) := by simp [Nat.ModEq]

theorem mod_two_zero_or_one (a : ℕ) : (a ≡ 1 [MOD 2]) ∨  (a ≡ 0 [MOD 2]) := by
  simp [Nat.ModEq]
  grind


theorem pow_add_one (a n : ℕ) : a ^ n * a = a^ (n + 1) := by
  grind


theorem nat_sq_of_add_modeq_zero {a b p : ℕ}
  (h : a + b ≡ 0 [MOD p]) :
  a ^ 2 ≡ b ^ 2 [MOD p] := by
  have h1  := h.mul_left a
  have h2  := h.mul_right b
  simp at h2
  have h1' : a * a + a * b ≡ 0 [MOD p] := by simpa [Nat.mul_add, pow_two] using h1
  have h2' : a * b + b * b ≡ 0 [MOD p] := by simpa [Nat.add_mul, pow_two] using h2
  have hsum : a * b + a * a ≡ a * b + b * b [MOD p] := by
    rw[add_comm]
    apply Nat.ModEq.symm at h2'
    apply Nat.ModEq.trans h1' h2'
  apply Nat.ModEq.add_left_cancel' at hsum
  simp[pow_two]
  exact hsum

theorem nat_sqrt_m1_sq_of_add_modeq_zero {a b : ℕ}
  (h : a + b ≡ 0 [MOD p]) :
  a ≡ (Field51_as_Nat constants.SQRT_M1) ^ 2 * b [MOD p] := by
  have h_sqrt_eq : (Field51_as_Nat constants.SQRT_M1) ^ 2 % p = p - 1 :=
    constants.SQRT_M1_spec
  have h_sqrt_mod : (Field51_as_Nat constants.SQRT_M1) ^ 2 ≡ p - 1 [MOD p] := by
    simp [Nat.ModEq, h_sqrt_eq]
  have h1 : (Field51_as_Nat constants.SQRT_M1) ^ 2 * b ≡ (p - 1) * b [MOD p] := by
    exact h_sqrt_mod.mul_right b
  have hp_pos : 1 ≤ p := by unfold p; simp
  have h2 : (p - 1) * b = p * b - b := by
      rw [Nat.sub_mul _ _ _, Nat.one_mul]
  have h3 : 0 ≡ p * b  [MOD p] := by
      simp [Nat.ModEq]
  have : p *b =  b + (p-1) *b  := by unfold p; grind
  rw[this] at h3
  have h4:=h3.add_left a
  have : a + (b + (p - 1) * b) =(a + b) + (p - 1) * b := by grind
  simp[this] at h4
  have h5:=h.add_right ((p - 1) * b)
  have h6:=h4.trans h5
  simp at h6
  exact h6.trans (h1.symm)


theorem eq_to_bytes_eq_Field51_as_Nat
    (u v : backend.serial.u64.field.FieldElement51)
    (h : u.to_bytes = v.to_bytes) :
  Field51_as_Nat u % p = Field51_as_Nat v % p := by
  classical
  obtain ⟨ru, hu, hru_mod, _⟩ := to_bytes_spec u
  obtain ⟨rv, hv, hrv_mod, _⟩ := to_bytes_spec v
  -- From the equality of the Result values, and the spec that they are ok, we get ru = rv
  have hrr : ru = rv := by
    have : ok ru = ok rv := by simpa [hu, hv] using h
    cases this
    rfl
  -- Chain the two congruences via the common bytes value
  have huv_mod : Nat.ModEq p (Field51_as_Nat u) (Field51_as_Nat v) := by
    have h1 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat u) := by
      simpa [hrr] using hru_mod
    have h2 : Nat.ModEq p (U8x32_as_Nat rv) (Field51_as_Nat v) := hrv_mod
    exact (Nat.ModEq.symm h1).trans h2
  -- Turn ModEq into equality of remainders
  simpa [Nat.ModEq] using huv_mod


theorem mod_sq_mod (a p : ℕ) : (a % p) ^ 2 ≡ a ^ 2 [MOD p] := by
  exact (Nat.mod_modEq a p).pow 2


theorem mod_sq_mod_mul (a b p : ℕ) : (a % p) ^ 2 * b ≡ a ^ 2 * b[MOD p] := by
  exact (Nat.ModEq.mul_right  b (mod_sq_mod a p))

theorem mod_sq_mod_mul_eq (a b p : ℕ) : ((a % p) ^ 2 * b) % p = (a ^ 2 * b) % p := by
  rw[← Nat.ModEq]
  apply mod_sq_mod_mul


/-- The square of (a mod p) mod p equals (a^2) mod p -/
theorem mod_sq_mod_eq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p := by
  exact (Nat.mod_modEq a p).pow 2

/-- Alternative formulation using explicit modulo equality -/
theorem sq_mod_eq_mod_sq (a p : ℕ) : ((a % p) ^ 2) % p = (a ^ 2) % p :=
  mod_sq_mod_eq a p





/-
Natural language description:

    This function takes two field elements u and v and returns

    - (Choice(1), +sqrt(u/v))       if v is nonzero and u/v is square;
    - (Choice(1), zero)             if u is zero;
    - (Choice(0), zero)             if v is zero and u is nonzero;
    - (Choice(0), +sqrt(i * u/v))   if u/v is nonsquare (so i*u/v is square).

Here i represents a square root of -1 in the field (mod p) and is stored as the constant SQRT_M1.
Every returned square root is nonnegative.

Natural language specs:

    • The function succeeds (no panic) for all field element inputs
    • The result (c, r) satisfies four mutually exclusive cases:

      - If u = 0 (mod p), then (c, r) = (Choice(1), 0)

      - If u ≠ 0 (mod p) and v = 0 (mod p), then (c, r) = (Choice(0), 0)

      - If u ≠ 0 (mod p) and v ≠ 0 (mod p) and (u/v) is a square, then (c, r) = (Choice(1), sqrt(u/v))

      - If u ≠ 0 (mod p) and v ≠ 0 (mod p) and (u/v) is not a square, then (c, r) = (Choice(0), sqrt(SQRT_M1 * u/v))

    • In all cases, r is non-negative
-/

/- **Spec and proof concerning `field.FieldElement51.sqrt_ratio_i`**:
- No panic for field element inputs u and v (always returns (c, r) successfully)
- The result satisfies exactly one of four mutually exclusive cases:
  1. If u ≡ 0 (mod p), then c.val = 1 and r ≡ 0 (mod p)
  2. If u ≢ 0 (mod p) and v ≡ 0 (mod p), then c.val = 0 and r ≡ 0 (mod p)
  3. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 1 and r^2 ≡ u * v^(-1) (mod p)
  4. If u ≢ 0 (mod p) and v ≢ 0 (mod p) and ¬∃ x, x^2 ≡ u * v^(-1) (mod p), then c.val = 0 and r^2 ≡ SQRT_M1 * u * v^(-1) (mod p)
-/

set_option maxHeartbeats  10000000 in
-- progress heavy

@[progress]
theorem sqrt_ratio_i_spec

    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 51 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1) :

    ∃ c, sqrt_ratio_i u v = ok c ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat c.2 % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p

    -- Case 1: u is zero
    (u_nat = 0 →
    c.1.val = 1#u8 ∧ r_nat = 0) ∧

    -- Case 2: u is nonzero and v is zero
    (u_nat ≠ 0 ∧ v_nat = 0 →
    c.1.val = 0#u8 ∧ r_nat = 0) ∧

    -- Case 3: u and v are nonzero and u/v is a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.1.val = 1#u8 ∧ (r_nat ^ 2 * v_nat) % p = u_nat ∧
    (∀ i < 5,  r_nat ≤ 2 ^ 54 - 1)) ∧

    -- Case 4: u and v are nonzero and u/v is not a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.1.val = 0#u8 ∧ (r_nat ^2 * v_nat) % p = (i_nat * u_nat) % p ∧
    (∀ i < 5,  r_nat ≤ 2 ^ 54 - 1))

    := by
    sorry
/-
    unfold sqrt_ratio_i subtle.BitOrsubtleChoicesubtleChoicesubtleChoice.bitor
    unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
    progress*
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK
      unfold constants.SQRT_M1
      decide
      -- END TASK
    · -- BEGIN TASK
      unfold constants.SQRT_M1
      decide
      -- END TASK
    · -- BEGIN TASK
      grind
      -- END TASK
    · -- BEGIN TASK

      have eq1_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
        ≡ (Field51_as_Nat constants.SQRT_M1) ^2 * (Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35))
        [MOD p]:= by
        have := r_prime_post_1.pow 2
        rw[mul_pow] at this
        have := this.mul_right (Field51_as_Nat v)
        apply this.trans
        rw[mul_assoc]
        apply Nat.ModEq.mul_left
        have := Nat.ModEq.pow 2 r_post_1
        rw[mul_pow] at this
        have := this.mul_right (Field51_as_Nat v)
        apply this.trans
        rw[← Nat.ModEq] at fe4_post_1
        have eq1:= fe4_post_1.pow 2
        rw[← pow_mul] at eq1
        have :=fe3_post_1.pow ((2 ^ 252 - 3) * 2)
        have eq2:= eq1.trans  this
        rw[mul_pow] at eq2

        have := fe_post_1.mul_right (Field51_as_Nat v)
        have eq_v3:= v3_post_1.trans this
        rw[pow_add_one] at eq_v3
        have := eq_v3.pow 2
        rw[← pow_mul] at this
        have := fe1_post_1.trans  this
        have := this.mul_right (Field51_as_Nat v)
        rw[pow_add_one] at this
        have := v7_post_1.trans  this
        have := this.pow ((2 ^ 252 - 3) * 2)
        rw[← pow_mul] at this
        have := this.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2))
        have eq3:= eq2.trans  this
        have := eq_v3.mul_left (Field51_as_Nat u)
        have := fe2_post_1.trans  this
        have eq4:= this.pow 2
        rw[mul_pow] at eq4
        have := eq4.mul  eq3
        have := this.mul_right (Field51_as_Nat v)
        apply this.trans
        have :  Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
         (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))) * Field51_as_Nat v
          =  (Field51_as_Nat u ^ 2 * Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2)) *
          ((Field51_as_Nat v ^ (2 + 1)) ^ 2 *
           Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2)) *
          Field51_as_Nat v)
            := by
            simp
            ring
        rw[this]
        clear this
        rw[← pow_add, ← pow_mul, ← pow_add, pow_add_one,
        (by simp : (2 + 1) * 2 + ((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2) + 1= 7 * 2 ^ 253 - 35)]


      have check_eq_v: Field51_as_Nat check ≡    Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) [MOD p] := by
        apply check_post_1.trans
        have := fe5_post_1.mul_left (Field51_as_Nat v)
        apply this.trans
        have := r_post_1.pow 2
        rw[mul_pow] at this
        have := this.mul_left (Field51_as_Nat v)
        apply this.trans
        rw[← Nat.ModEq] at fe4_post_1
        have eq1:= Nat.ModEq.pow 2 fe4_post_1
        rw[← pow_mul] at eq1
        have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) fe3_post_1
        have eq2:= Nat.ModEq.trans eq1 this
        rw[mul_pow] at eq2
        have := Nat.ModEq.mul_right (Field51_as_Nat v) fe_post_1
        have eq_v3:= Nat.ModEq.trans v3_post_1 this
        rw[pow_add_one] at eq_v3
        have := Nat.ModEq.pow 2 eq_v3
        rw[← pow_mul] at this
        have := Nat.ModEq.trans fe1_post_1 this
        have := Nat.ModEq.mul_right (Field51_as_Nat v) this
        rw[pow_add_one] at this
        have := Nat.ModEq.trans v7_post_1 this
        have := Nat.ModEq.pow ((2 ^ 252 - 3) * 2) this
        rw[← pow_mul] at this
        have := Nat.ModEq.mul_left  ((Field51_as_Nat u)^ ((2 ^ 252 - 3) * 2)) this
        have eq3:= Nat.ModEq.trans eq2 this
        have := Nat.ModEq.mul_left (Field51_as_Nat u) eq_v3
        have := Nat.ModEq.trans fe2_post_1 this
        have eq4:= Nat.ModEq.pow 2 this
        rw[mul_pow] at eq4
        have := Nat.ModEq.mul eq4 eq3
        have := Nat.ModEq.mul_left (Field51_as_Nat v) this
        apply Nat.ModEq.trans this
        have :  Field51_as_Nat v *
          (Field51_as_Nat u ^ 2 * (Field51_as_Nat v ^ (2 + 1)) ^ 2 *
          (Field51_as_Nat u ^ ((2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (((2 + 1) * 2 + 1) * ((2 ^ 252 - 3) * 2))))
          =  Field51_as_Nat u ^ (2 + (2 ^ 252 - 3) * 2) * Field51_as_Nat v ^ (7 * 2 ^ 253 - 35)
            := by
            simp
            ring
        rw[this]


      have check_eq_mod: (Field51_as_Nat r_prime)^2 *  (Field51_as_Nat v)
        ≡ (Field51_as_Nat constants.SQRT_M1) ^2 *Field51_as_Nat check [MOD p] := by
        have := Nat.ModEq.mul_left ((Field51_as_Nat constants.SQRT_M1) ^2) check_eq_v
        apply Nat.ModEq.trans eq1_mod
        apply Nat.ModEq.symm this


      have :=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1





      by_cases first_choice :  flipped_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt_i.val = 1#u8
      · -- BEGIN TASK
        simp[first_choice]
        progress*
        · -- BEGIN TASK
          simp[Choice.one] at r1_post
          simp_all
          clear check_eq_mod check_eq_v eq1_mod
          grind
          -- END TASK
        · -- BEGIN TASK
          simp[Choice.one] at r1_post
          by_cases second_choice : correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8
          · -- BEGIN TASK
            simp[second_choice]
            progress*
            simp[Choice.one]
            have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
                simp[Field51_as_Nat, Finset.sum_range_succ]
                simp_all
            simp[← modEq_zero_iff]
            constructor
            · -- BEGIN TASK
              intro hu
              have := Nat.ModEq.mul_right (Field51_as_Nat v3) hu
              simp at this
              have := Nat.ModEq.trans fe2_post_1 this
              have := Nat.ModEq.mul_right (Field51_as_Nat fe4) this
              simp at this
              have := Nat.ModEq.trans r_post_1 this
              have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1) this
              have r_prime_eq0:= Nat.ModEq.trans r_prime_post_1 this
              simp at r_prime_eq0
              have : Field51_as_Nat r_prime % p % 2 = 0 := by
                      simp[Nat.ModEq] at r_prime_eq0
                      rw[r_prime_eq0]

              simp[r_is_negative_post] at r2_post
              have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
                simp[Field51_as_Nat, Finset.sum_range_succ]
                simp_all
              rw[this]
              apply  r_prime_eq0
              -- END TASK
            · -- BEGIN TASK
              constructor
              · -- BEGIN TASK
                intro hu hv
                simp_all
                apply hu
                have := Nat.ModEq.mul_right (Field51_as_Nat fe5) hv
                have check0:= Nat.ModEq.trans  check_post_1 this
                simp at check0
                rcases second_choice with second_choice | second_choice
                · -- BEGIN TASK
                  have : correct_sign_sqrt = Choice.one := by
                    exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp second_choice
                  simp[this] at correct_sign_sqrt_post
                  have := eq_to_bytes_eq_Field51_as_Nat check u correct_sign_sqrt_post
                  rw[← Nat.ModEq] at this
                  apply Nat.ModEq.trans (Nat.ModEq.symm this) check0
                  -- END TASK
                · -- BEGIN TASK
                  have : flipped_sign_sqrt = Choice.one := by
                    exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp second_choice
                  simp[this] at flipped_sign_sqrt_post
                  have := eq_to_bytes_eq_Field51_as_Nat check fe6 flipped_sign_sqrt_post
                  rw[← Nat.ModEq] at this
                  have :=  Nat.ModEq.trans (Nat.ModEq.symm this) check0
                  have := Nat.ModEq.add_left (Field51_as_Nat u) this
                  rw[← modEq_zero_iff] at fe6_post_1
                  have :=  Nat.ModEq.trans (Nat.ModEq.symm this) fe6_post_1
                  simp at this
                  apply this
                  -- END TASK
                -- END TASK
              · -- BEGIN TASK
                have r2_eq: (Field51_as_Nat r2 )^2 ≡ (Field51_as_Nat r_prime) ^2 [MOD p] := by
                      rcases (mod_two_zero_or_one (Field51_as_Nat r_prime % p)) with one | zero
                      · -- BEGIN TASK
                        rw[mod_two_Eq_one_iff] at one
                        simp[this, one] at r_is_negative_post
                        simp[r_is_negative_post] at r2_post
                        have : Field51_as_Nat r2 = Field51_as_Nat x:= by
                          simp[Field51_as_Nat, Finset.sum_range_succ]
                          simp_all
                        rw[← this] at x_post_1
                        simp_all
                        rw[← modEq_zero_iff] at x_post_1
                        apply nat_sq_of_add_modeq_zero
                        rw[add_comm]
                        apply  x_post_1
                        -- END TASK
                      · -- BEGIN TASK
                        rw[modEq_zero_iff] at zero
                        simp[this, zero] at r_is_negative_post
                        simp[r_is_negative_post] at r2_post
                        have : Field51_as_Nat r2 = Field51_as_Nat r_prime:= by
                          simp[Field51_as_Nat, Finset.sum_range_succ]
                          simp_all
                        rw[this]
                        -- END TASK
                constructor
                · -- BEGIN TASK
                  intro hu hv xx hxx
                  constructor
                  · -- BEGIN TASK
                    have := Nat.ModEq.mul_right (Field51_as_Nat v) r2_eq
                    rw[mod_sq_mod_mul_eq, ← Nat.ModEq]
                    have := Nat.ModEq.trans this check_eq_mod
                    apply Nat.ModEq.trans this
                    rcases first_choice with co | fi
                    · -- BEGIN TASK
                      have : flipped_sign_sqrt = Choice.one := by
                        exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp co
                      simp[this] at flipped_sign_sqrt_post
                      have this:= eq_to_bytes_eq_Field51_as_Nat check fe6 flipped_sign_sqrt_post
                      rw[← Nat.ModEq] at this
                      have :=this.mul_left  (Field51_as_Nat constants.SQRT_M1 ^ 2)
                      rw[← modEq_zero_iff] at fe6_post_1
                      have :=this.trans  (nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1).symm
                      apply this
                      -- END TASK
                    · have : flipped_sign_sqrt_i = Choice.one := by
                        exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp fi
                      simp[this] at flipped_sign_sqrt_i_post
                      have := eq_to_bytes_eq_Field51_as_Nat check fe7 flipped_sign_sqrt_i_post
                      rw[← Nat.ModEq] at this
                      have := this.trans fe7_post_1
                      have :=this.mul_left  (Field51_as_Nat constants.SQRT_M1 ^ 2)
                      apply this.trans
                      have :=nat_sqrt_m1_sq_of_add_modeq_zero fe6_post_1


                      apply this




                  -- END TASK

                -- END TASK
              -- END TASK

            -- END TASK




          -- END TASK


        -- END TASK

        -- END TASK

      -- END TASK

-/
end curve25519_dalek.field.FieldElement51
