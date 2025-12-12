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

set_option maxHeartbeats 100000000

set_option exponentiation.threshold 400

theorem modEq_zero_iff (a n : ℕ) : a ≡ 0 [MOD n] ↔  a % n = 0 := by simp [Nat.ModEq]

theorem mod_two_Eq_one_iff (a : ℕ) : a ≡ 1 [MOD 2] ↔  a % 2 = 1 := by simp [Nat.ModEq]


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





lemma mod_idem (a p : Nat) : (a % p) % p = a % p := by
   by_cases h0 : p = 0
   · simp [h0]
   · have hp : 0 < p := Nat.pos_of_ne_zero h0
     exact Nat.mod_eq_of_lt (Nat.mod_lt _ hp)

/-- (p − 1)^2 ≡ 1 (mod p). Useful to turn two "−1" congruences into 1. -/
lemma pm1_sq_modeq_one : (p - 1) * (p - 1) ≡ 1 [MOD p] := by
  -- Since (p-1) + 1 = p ≡ 0 (mod p), squaring both sides gives the claim.
  have h0 : (p - 1) + 1 ≡ 0 [MOD p] := by
    have hsucc : (p - 1) + 1 = p := by
      -- p = 2^255 - 19 ≥ 1
      have : (1 : Nat) ≤ p := by decide
      simpa using Nat.sub_add_cancel this
    simp [Nat.ModEq, hsucc]
  simpa [pow_two] using nat_sq_of_add_modeq_zero h0

/-- If A ≡ p−1 (mod p) and i^2 ≡ p−1 (mod p) then A * i^2 ≡ 1 (mod p). -/
lemma mul_of_pm1s_to_one {A i : Nat}
  (hA : A ≡ p - 1 [MOD p])
  (hi : i ^ 2 ≡ p - 1 [MOD p]) :
  A * i ^ 2 ≡ 1 [MOD p] := by
  -- A * i^2 ≡ A * (p-1)
  have h1 := Nat.ModEq.mul_left A hi
  -- A * (p-1) ≡ (p-1) * (p-1)
  have h2 := Nat.ModEq.mul_right (p - 1) hA
  exact (h1.trans h2).trans pm1_sq_modeq_one

/-- Core step used in the flip-branch: if A^(e+1) ≡ p-1 and i^2 ≡ p-1, then
    A^(e+1) * i^2 ≡ 1 (mod p). -/
lemma pow_e1_mul_i2_eq_one_of_A_pow_e1_eq_pm1 {A i e : Nat}
  (hA : A ^ (e + 1) ≡ p - 1 [MOD p])
  (hi : i ^ 2 ≡ p - 1 [MOD p]) :
  (A ^ (e + 1)) * i ^ 2 ≡ 1 [MOD p] := by
  exact mul_of_pm1s_to_one hA hi

/-- If A^(e+1) * i^2 ≡ 1 and i^2 ≡ p-1, then A^(e+1) ≡ p-1 (mod p). -/
lemma A_pow_e1_eq_pm1_of_mul_i2_eq_one {A i e : Nat}
  (hmul : (A ^ (e + 1)) * i ^ 2 ≡ 1 [MOD p])
  (hi   : i ^ 2 ≡ p - 1 [MOD p]) :
  A ^ (e + 1) ≡ p - 1 [MOD p] := by
  -- Multiply by (p-1) on the right, then use i^2 ≡ p-1 and (p-1)^2 ≡ 1
  have h1 := Nat.ModEq.mul_right (p - 1) hmul
  have h2 : (A ^ (e + 1)) * (i ^ 2) * (p - 1) ≡
            (A ^ (e + 1)) * ((p - 1) * (p - 1)) [MOD p] := by
    have := Nat.ModEq.mul_left (A ^ (e + 1)) hi
    have := Nat.ModEq.mul_right (p - 1) this
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have h3 : (A ^ (e + 1)) * ((p - 1) * (p - 1)) ≡
            (A ^ (e + 1)) * 1 [MOD p] := by
    have := Nat.ModEq.mul_left (A ^ (e + 1)) pm1_sq_modeq_one
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hL : (A ^ (e + 1)) * (i ^ 2) * (p - 1) ≡ A ^ (e + 1) [MOD p] := by
    have := h2.trans h3
    simpa using this
  exact (Nat.ModEq.symm hL).trans h1

/-- Specialization: recover the flipped-branch exponent congruence. -/
lemma pow_target_from_flip
  (u v : backend.serial.u64.field.FieldElement51)
  (hmul :
    (Field51_as_Nat u * (Field51_as_Nat v) ^ 7) ^ (2 ^ 253 - 6 + 1) *
    (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) ^ 2 ≡ 1 [MOD p])
  (hi2 :
    (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) ^ 2 ≡ p - 1 [MOD p]) :
  (Field51_as_Nat u * (Field51_as_Nat v) ^ 7) ^ (2 ^ 253 - 6 + 1) ≡ p - 1 [MOD p] := by
  exact A_pow_e1_eq_pm1_of_mul_i2_eq_one hmul hi2

/-- Specialization for the concrete A = Field51_as_Nat u * (Field51_as_Nat v)^7
    and i = SQRT_M1 used in curve25519-dalek. -/
lemma flip_goal_from_branch
  (u v : backend.serial.u64.field.FieldElement51)
  (h_i : (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) ^ 2 ≡ p - 1 [MOD p])
  (h_Apm1 :
     (Field51_as_Nat u * (Field51_as_Nat v) ^ 7) ^ (2 ^ 253 - 6 + 1) ≡ p - 1 [MOD p]) :
  (Field51_as_Nat u * (Field51_as_Nat v) ^ 7) ^ (2 ^ 253 - 6 + 1) *
  (Field51_as_Nat backend.serial.u64.constants.SQRT_M1) ^ 2 ≡ 1 [MOD p] := by
  exact pow_e1_mul_i2_eq_one_of_A_pow_e1_eq_pm1 h_Apm1 h_i


-- Helper: equality of to_bytes implies equality modulo p of Field51_as_Nat
/-- If two FieldElement51 values produce identical canonical byte encodings,
then their natural-number interpretations are congruent modulo p. In particular,
(normal form) remainders modulo p are equal. -/
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


theorem mod_pow_mul_mod_modEq (a b p : ℕ) :
(a % p)^2 * (b % p) ≡ a^2 * b [MOD p] := by
have ha : a % p ≡ a [MOD p] := Nat.mod_modEq a p
have hb : b % p ≡ b [MOD p] := Nat.mod_modEq b p
exact (ha.pow 2).mul hb

lemma mod_pow_mul_mod_eq_mod (a b p : ℕ) :
((a % p)^2 * (b % p)) % p = (a^2 * b) % p := by
simpa [Nat.ModEq] using mod_pow_mul_mod_modEq a b p

/-- Helper lemma to conclude r^2 * v ≡ u (mod p) from a factorized congruence.
Let e = 2^253 - 6 in the application. Given
  h  : r^2 ≡ u^(e+2) * v^(7*(e+1)) * i^2 (mod p)
and the branch-specific sign relation
  hs : ((u * v^7)^(e+1)) * i^2 ≡ 1 (mod p),
we obtain r^2 * v ≡ u (mod p). -/
lemma conclude_from_eqr
  {u v r  : Nat} (e  i: Nat)
  (h : r ^ 2 ≡ u ^ (e + 2) * v ^ (6 + 7 * e) * i ^ 2 [MOD p])
  (hs : ((u * v ^ 7) ^ (e + 1)) * i ^ 2 ≡ 1 [MOD p]) :
  r ^ 2 * v ≡ u [MOD p] := by
  have hv := Nat.ModEq.mul_right v h
  have hv' :
      r ^ 2 * v ≡ u ^ (e + 2) * v ^ (7 * (e + 1)) * i ^ 2 [MOD p] := by
    have : (u ^ (e + 2) * v ^ (6 + 7 * e) * i ^ 2) * v =
            u ^ (e + 2) * v ^ ((6 + 7 * e) + 1) * i ^ 2 := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_add, pow_one]
    have : (6 + 7 * e) + 1 = 7 * (e + 1) := by
      scalar_tac
    scalar_tac
  have hu : u ^ (e + 2) = u ^ (e + 1) * u := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (pow_add u (e + 1) 1)
  have hvpow : v ^ (7 * (e + 1)) = (v ^ 7) ^ (e + 1) := by
    simp [pow_mul]
  have hpacked :
      r ^ 2 * v ≡ u * (((u * v ^ 7) ^ (e + 1)) * i ^ 2) [MOD p] := by
      apply Nat.ModEq.trans hv'
      have : u ^ (e + 2) * v ^ (7 * (e + 1)) * i ^ 2 = u * ((u * v ^ 7) ^ (e + 1) * i ^ 2) := by
       ring
      rw[this]

  -- Apply the sign relation to collapse to u
  have := Nat.ModEq.mul_left u hs
  exact (Nat.ModEq.trans hpacked (by
           simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this))


/-Natural language description:

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



@[progress]
theorem sqrt_ratio_i_spec

    (u : backend.serial.u64.field.FieldElement51)
    (v : backend.serial.u64.field.FieldElement51)
    (h_u_bounds : ∀ i, i < 5 → (u[i]!).val ≤ 2 ^ 51 - 1)
    (h_v_bounds : ∀ i, i < 5 → (v[i]!).val ≤ 2 ^ 51 - 1) :

    ∃ c r, sqrt_ratio_i u v = ok (c, r) ∧
    let u_nat := Field51_as_Nat u % p
    let v_nat := Field51_as_Nat v % p
    let r_nat := Field51_as_Nat r % p
    let i_nat := Field51_as_Nat backend.serial.u64.constants.SQRT_M1 % p

    -- Case 1: u is zero
    (u_nat = 0 →
    c.val = 1#u8 ∧ r_nat = 0) ∧

    -- Case 2: u is nonzero and v is zero
    (u_nat ≠ 0 ∧ v_nat = 0 →
    c.val = 0#u8 ∧ r_nat = 0) ∧

    -- Case 3: u and v are nonzero and u/v is a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ (∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 1#u8 ∧ (r_nat^2 * v_nat) % p = u_nat) ∧

    -- Case 4: u and v are nonzero and u/v is not a square
    (u_nat ≠ 0 ∧ v_nat ≠ 0 ∧ ¬(∃ x : Nat, (x^2 * v_nat) % p = u_nat) →
    c.val = 0#u8 ∧ (r_nat^2 * v_nat) % p = (i_nat * u_nat) % p)

    := by
    unfold sqrt_ratio_i
    progress*
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (fe_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v3_post_2 i hi)
      simp
    · intro i hi
      apply lt_trans (fe1_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v3_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (v7_post_2 i hi)
      simp
    · intro i hi
      apply Nat.le_pred_of_lt (fe3_post_2 i hi)
    · intro i hi
      apply lt_trans (fe2_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (fe4_post_2 i hi)
      simp
    · intro i hi
      apply lt_trans (r_post_2  i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_v_bounds i hi)
      simp
    · intro i hi
      apply lt_trans (fe5_post_2 i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (h_u_bounds i hi)
      simp
    · intro i hi
      apply lt_of_le_of_lt (fe6_post_2  i hi)
      simp
    · unfold constants.SQRT_M1
      decide
    · unfold constants.SQRT_M1
      decide
    · intro i hi
      apply lt_trans (r_post_2  i hi)
      simp
    unfold   subtle.BitOrsubtleChoicesubtleChoicesubtleChoice.bitor
    by_cases h : flipped_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt_i.val = 1#u8
    · simp[h]
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · simp_all
        intro i a
        simp[Choice.one]
        apply lt_trans (r_prime_post_2  i a)
        simp
      ·  by_cases hs :correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8
         · simp[hs, Choice.one]
           constructor
           · intro hu
             simp_all
             simp[Choice.one] at r1_post
             have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
               simp[Field51_as_Nat, Finset.sum_range_succ]
               simp_all
             simp[Choice.one, this] at r2_post
             rw[← modEq_zero_iff]
             rw[← modEq_zero_iff] at hu
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
             simp[this] at r2_post
             have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
               simp[Field51_as_Nat, Finset.sum_range_succ]
               simp_all
             rw[this]
             apply r_prime_eq0
           · constructor
             · intro hup hvp
               apply hup
               rw[← modEq_zero_iff]
               rw[← modEq_zero_iff] at hvp
               have := Nat.ModEq.mul_right (Field51_as_Nat fe5) hvp
               simp at this
               have check0:= Nat.ModEq.trans check_post_1 this
               rcases hs with hs | hs
               · have : correct_sign_sqrt = Choice.one := by
                   exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp hs
                 simp[this] at correct_sign_sqrt_post
                 have := eq_to_bytes_eq_Field51_as_Nat check u correct_sign_sqrt_post
                 rw[← Nat.ModEq] at this
                 apply Nat.ModEq.trans (Nat.ModEq.symm this) check0
               · have : flipped_sign_sqrt = Choice.one := by
                   exact (curve25519_dalek.field.FieldElement51.Choice.val_eq_one_iff _).mp hs
                 simp[this] at flipped_sign_sqrt_post
                 have := eq_to_bytes_eq_Field51_as_Nat check fe6 flipped_sign_sqrt_post
                 rw[← Nat.ModEq] at this
                 have := Nat.ModEq.trans (Nat.ModEq.symm this) check0
                 have := Nat.ModEq.add_left (Field51_as_Nat u) this
                 rw[← modEq_zero_iff] at fe6_post_1
                 have := Nat.ModEq.trans (Nat.ModEq.symm this) fe6_post_1
                 simp at this
                 exact this
             · have : ¬Field51_as_Nat u % p = 0 →
                      ¬Field51_as_Nat v % p = 0 →
                      (Field51_as_Nat r2 % p) ^ 2 * (Field51_as_Nat v % p) %p = Field51_as_Nat u % p := by
                       intro hup hvp
                       have := mod_pow_mul_mod_eq_mod (Field51_as_Nat r2) (Field51_as_Nat v) p
                       rw[this, ← Nat.ModEq]
                       simp_all
                       simp[Choice.one] at r2_post
                       have hs1:  Field51_as_Nat r_prime ^ 2 * Field51_as_Nat v ≡ Field51_as_Nat u [MOD p]
                       →  Field51_as_Nat r2 ^ 2 * Field51_as_Nat v ≡ Field51_as_Nat u [MOD p] := by
                         intro hs2
                         by_cases hs1 : Field51_as_Nat r1 % p % 2 = 1
                         · simp[hs1] at r2_post
                           have : Field51_as_Nat r2 = Field51_as_Nat x := by
                            simp[Field51_as_Nat, Finset.sum_range_succ]
                            simp_all
                           rw[this]
                           have := nat_sq_of_add_modeq_zero x_post_1
                           have := Nat.ModEq.mul_right (Field51_as_Nat v) this
                           apply Nat.ModEq.trans ( Nat.ModEq.symm this)
                           have : Field51_as_Nat r1 = Field51_as_Nat r_prime := by
                            simp[Field51_as_Nat, Finset.sum_range_succ]
                            simp_all
                           rw[this]
                           simp_all
                         · simp[hs1] at r2_post
                           have : Field51_as_Nat r2 = Field51_as_Nat r_prime := by
                            simp[Field51_as_Nat, Finset.sum_range_succ]
                            simp_all
                           rw[this]
                           have := Nat.ModEq.pow 2 r_prime_post_1
                           rw[mul_pow] at this
                           simp_all
                       apply hs1
                       have eq1 := Nat.ModEq.pow 2 r_prime_post_1
                       rw[mul_pow] at eq1
                       have := Nat.ModEq.pow 2 r_post_1
                       rw[mul_pow] at this
                       have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1 ^ 2) this
                       have eq2:= Nat.ModEq.trans eq1 this
                       have fe20:= Nat.ModEq.pow 2 fe2_post_1
                       rw[mul_pow] at fe20
                       have v30:= Nat.ModEq.pow 2 v3_post_1
                       rw[mul_pow] at v30
                       have := Nat.ModEq.pow 2 fe_post_1
                       have := Nat.ModEq.mul_right (Field51_as_Nat v ^ 2) this
                       have v3v:= Nat.ModEq.trans v30 this
                       have := Nat.ModEq.mul_left (Field51_as_Nat u ^2) v3v
                       have := Nat.ModEq.trans fe20 this
                       rw[← pow_mul, ← pow_add] at this
                       have := Nat.ModEq.pow 2 fe4_post_1
                       rw[← pow_mul] at this
                       have fe3v7:= Nat.ModEq.pow (2 ^ 253 - 6) fe3_post_1
                       rw[mul_pow] at fe3v7
                       have := Nat.ModEq.pow (2 ^ 253 - 6) v7_post_1
                       have := Nat.ModEq.mul_left (Field51_as_Nat u ^ (2 ^ 253 - 6)) this
                       rw[mul_pow] at this
                       have fe3v70:= Nat.ModEq.trans fe3v7 this
                       rw[← mul_assoc] at fe3v70
                       have v3v0:= Nat.ModEq.pow (2 ^ 253 - 6) v3v
                       have := Nat.ModEq.pow (2 ^ 253 - 6) fe1_post_1
                       have := Nat.ModEq.trans this v3v0
                       rw[← pow_mul, ← pow_add, ← pow_mul]at this
                       have := Nat.ModEq.mul_right (Field51_as_Nat v ^ (2 ^ 253 - 6)) this
                       rw[ ← pow_add]at this
                       have := Nat.ModEq.mul_left (Field51_as_Nat u ^ (2 ^ 253 - 6)) this
                       rw[← mul_assoc] at this
                       have eq123 := Nat.ModEq.trans fe3v70 this
                       clear this
                       clear this
                       clear this
                       clear this
                       clear this
                       clear v3v0
                       clear fe3v70
                       clear this
                       clear fe3v7
                       have fe4v:= Nat.ModEq.trans this eq123
                       clear this
                       have eq21:= Nat.ModEq.mul this fe4v
                       clear this
                       clear this
                       clear this
                       clear v3v
                       clear fe4v
                       clear eq123
                       clear this
                       clear v30
                       clear fe20
                       have := Nat.ModEq.mul_left (Field51_as_Nat constants.SQRT_M1 ^ 2) eq21
                       have eqr:= Nat.ModEq.trans  eq2  this
                       rw[mul_comm] at eqr
                       have :  Field51_as_Nat u ^ 2 *
                        Field51_as_Nat v ^ (2 * 2 + 2) *
                        (Field51_as_Nat u ^ (2 ^ 253 - 6) *
                        Field51_as_Nat v ^ ((2 * 2 + 2) * (2 ^ 253 - 6) + (2 ^ 253 - 6)))=
                        Field51_as_Nat u ^ (2 ^ 253 - 4) *
                        Field51_as_Nat v ^ (7 * 2 ^ 253  - 36)
                        := by ring
                       rw[this] at eqr
                       clear this
                       have h_mul_v := Nat.ModEq.mul_right (Field51_as_Nat v) eqr
                       apply Nat.ModEq.trans h_mul_v
                       have : Field51_as_Nat u ^ (2 ^ 253 - 4) *
                       Field51_as_Nat v ^ (7 * 2 ^ 253 - 36) *
                        Field51_as_Nat constants.SQRT_M1 ^ 2 *
                        Field51_as_Nat v = Field51_as_Nat u ^ (2 ^ 253 - 4) *
                       Field51_as_Nat v ^ (7 * 2 ^ 253 - 35) *
                        Field51_as_Nat constants.SQRT_M1 ^ 2 := by ring
                       rw[this]
                       sorry










































               simp_all
               intro hup hvp
               have := this hup hvp
               use Field51_as_Nat r2 % p
         · simp[hs, Choice.zero]
           constructor
           · intro hu
             apply hs

           · constructor
             · sorry
             · sorry
    · simp[h]
      unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
      progress*
      · simp_all
        intro i a
        simp[Choice.zero]
        apply lt_trans (r_post_2  i a)
        simp
      ·  by_cases hs :correct_sign_sqrt.val = 1#u8 ∨ flipped_sign_sqrt.val = 1#u8
         · simp[hs, Choice.one]
           constructor
           · sorry
           · constructor
             · sorry
             · sorry
         · simp[hs, Choice.zero]
           constructor
           · sorry
           · sorry







































end curve25519_dalek.field.FieldElement51
