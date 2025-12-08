/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Mathlib.Data.Int.ModEq
/-! # Spec Theorem for `Scalar52::add`

Specification and proof for `Scalar52::add`.

This function adds two elements.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 100000
open scoped BigOperators

/-- Bound the natural interpretation of a Scalar52 by 2^(5*52) given per-limb bounds. -/

theorem Scalar52_as_Nat_bound (a : Scalar52) (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) :
    Scalar52_as_Nat a < 2 ^ (5 * 52) := by
  -- Prove by bounding the partial sums S k = ∑_{i<k} 2^(52*i) * a[i]
  have hstep : ∀ k ≤ 5,
      (∑ i ∈  Finset.range k, 2 ^ (52 * i) * (a[i]!).val) < 2 ^ (52 * k) := by
    intro k hk
    induction' k with k ih
    · -- k = 0
      simp
    · -- k+1 step
      have hklt : k < 5 := Nat.succ_le.mp hk
      have ih' : (∑ i ∈  Finset.range k, 2 ^ (52 * i) * (a[i]!).val) < 2 ^ (52 * k) :=
        ih (Nat.le_of_lt hklt)
      -- Bound the last limb contribution using ha
      have last_le : 2 ^ (52 * k) * (a[k]!).val ≤ 2 ^ (52 * k) * (2 ^ 52 - 1) := by
        exact Nat.mul_le_mul_left _ (Nat.le_pred_of_lt (ha k hklt))
      -- Combine the bounds: S(k+1) = S k + 2^(52k) * a[k]
      have :
        (∑ i ∈  Finset.range (Nat.succ k), 2 ^ (52 * i) * (a[i]!).val)
          < 2 ^ (52 * k) + 2 ^ (52 * k) * (2 ^ 52 - 1) := by
        simpa [Finset.sum_range_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using Nat.add_lt_add_of_lt_of_le ih' last_le
      -- Show the RHS equals 2^(52*(k+1))
      have hpos : 0 < 2 ^ 52 := by decide
      have h1 : 1 + (2 ^ 52 - 1) = 2 ^ 52 := by
        simp
      have hrhs : 2 ^ (52 * k) + 2 ^ (52 * k) * (2 ^ 52 - 1) = 2 ^ (52 * (k + 1)) := by
        calc
          2 ^ (52 * k) + 2 ^ (52 * k) * (2 ^ 52 - 1)
              = 2 ^ (52 * k) * 1 + 2 ^ (52 * k) * (2 ^ 52 - 1) := by
                  simp
          _ = 2 ^ (52 * k) * (1 + (2 ^ 52 - 1)) := by
                  rw [Nat.mul_add, Nat.add_comm]
          _ = 2 ^ (52 * k) * 2 ^ 52 := by simp
          _ = 2 ^ (52 * k + 52) := by
                simp [pow_add, Nat.mul_comm]
          _ = 2 ^ (52 * (k + 1)) := by
                simp [Nat.mul_succ, Nat.add_comm]
      exact lt_of_lt_of_eq this hrhs
  simpa [Scalar52_as_Nat] using hstep 5 (le_rfl)



lemma add_lt_add_of_lt_of_lt_nat {a b c d : Nat}
  (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
   calc a + c < b + c := Nat.add_lt_add_right h₁ _
    _ < b + d := Nat.add_lt_add_left h₂ _

theorem land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  · simp
    scalar_tac
  · simp

theorem eq1 (a b m : ℕ) :
  a % 2^m + 2^m * ((b + a >>> m) % 2^m)
  ≡ a + 2^m *(b % 2^m) [MOD 2^ (2* m)] := by
  -- Rewrite shiftRight and expand the right-hand side using the Euclidean division of a
  rw [Nat.shiftRight_eq_div_pow]
  have hdecomp := Nat.mod_add_div a (2 ^ m)
  have hrhs :
      a + 2 ^ m * (b % 2 ^ m)
        = a % 2 ^ m + 2 ^ m * (a / 2 ^ m) + 2 ^ m * (b % 2 ^ m) := by
    calc
      a + 2 ^ m * (b % 2 ^ m)
          = (a % 2 ^ m + 2 ^ m * (a / 2 ^ m)) + 2 ^ m * (b % 2 ^ m) := by
              simp [hdecomp]
      _ = a % 2 ^ m + 2 ^ m * (a / 2 ^ m) + 2 ^ m * (b % 2 ^ m) := by
              ac_rfl
  rw [hrhs, add_assoc]
  -- Reduce to proving a congruence on the 2^m-multiples
  apply Nat.ModEq.add_left
  -- Show: 2^m * ((b + a/2^m) % 2^m) ≡ 2^m*(a/2^m) + 2^m*(b % 2^m) [MOD 2^(2m)]
  -- First lift ((b + a/2^m) % 2^m) to (b + a/2^m)
  have h1 : 2 ^ m * ((b + a / 2 ^ m) % 2 ^ m)
      ≡ 2 ^ m * (b + a / 2 ^ m) [MOD 2 ^ (2 * m)] := by
    have h := (Nat.mod_modEq (b + a / 2 ^ m) (2 ^ m)).mul_left' (2 ^ m)
    simpa [two_mul, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  -- Replace 2^m * b by 2^m * (b % 2^m) modulo 2^(2m)
  have h2 : 2 ^ m * b ≡ 2 ^ m * (b % 2 ^ m) [MOD 2 ^ (2 * m)] := by
    have h := (Nat.mod_modEq b (2 ^ m)).mul_left' (2 ^ m)
    simpa [two_mul, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm
  -- Combine
  calc
    2 ^ m * ((b + a / 2 ^ m) % 2 ^ m)
        ≡ 2 ^ m * (b + a / 2 ^ m) [MOD 2 ^ (2 * m)] := h1
    _ = 2 ^ m * b + 2 ^ m * (a / 2 ^ m) := by
        simp [Nat.mul_add]
    _ ≡ 2 ^ m * (b % 2 ^ m) + 2 ^ m * (a / 2 ^ m) [MOD 2 ^ (2 * m)] := by
        exact h2.add_right (2 ^ m * (a / 2 ^ m))
    _ = 2 ^ m * (a / 2 ^ m) + 2 ^ m * (b % 2 ^ m) := by
        ac_rfl

theorem eq2 (a1 a2 a3 m : ℕ) :
  a1 % 2^m +
  2^m * ((a2 + a1 >>> m) % 2^m) +
  2^(2*m) * ( (a3 + (a2 + a1 >>> m) >>> m) % 2^m)
  ≡ a1 + 2^m * a2 + 2^(2*m) * (a3 % 2^m) [MOD 2^ (3* m)] := by
  -- Let c1 be the carry after adding a1 and a2 at limb m
  set c1 := a2 + a1 >>> m
  -- Apply eq1 to (c1, a3), scale by 2^m, then add a1 % 2^m
  have h0 := (eq1 c1 a3 m).mul_left' (2 ^ m)
  have h1 := h0.add_left (a1 % 2 ^ m)
  -- Distribute and normalize products; keep modulus as 2^m * 2^(2*m)
  have h2 :
      a1 % 2 ^ m + (2 ^ m * (c1 % 2 ^ m) + 2 ^ (2 * m) * ((a3 + c1 >>> m) % 2 ^ m))
        ≡ a1 % 2 ^ m + (2 ^ m * c1 + 2 ^ (2 * m) * (a3 % 2 ^ m)) [MOD 2 ^ m * 2 ^ (2 * m)] := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_add, two_mul] using h1
  -- Reassociate to a1%2^m + ... + ...
  have h3 :
      a1 % 2 ^ m + 2 ^ m * (c1 % 2 ^ m) + 2 ^ (2 * m) * ((a3 + c1 >>> m) % 2 ^ m)
        ≡ a1 % 2 ^ m + 2 ^ m * c1 + 2 ^ (2 * m) * (a3 % 2 ^ m) [MOD 2 ^ m * 2 ^ (2 * m)] := by
    simpa [Nat.add_assoc] using h2
  -- Simplify the RHS using the Euclidean division of a1 and the definition of c1
  have hrhs : a1 % 2 ^ m + 2 ^ m * c1 = a1 + 2 ^ m * a2 := by
    have hdecomp := Nat.mod_add_div a1 (2 ^ m)
    have hshift : a1 >>> m = a1 / 2 ^ m := by
      simp [Nat.shiftRight_eq_div_pow]
    calc
      a1 % 2 ^ m + 2 ^ m * c1
          = a1 % 2 ^ m + 2 ^ m * (a2 + a1 / 2 ^ m) := by simp [c1, hshift]
      _ = a1 % 2 ^ m + 2 ^ m * a2 + 2 ^ m * (a1 / 2 ^ m) := by
          simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 ^ m * a2 + (a1 % 2 ^ m + 2 ^ m * (a1 / 2 ^ m)) := by
          ac_rfl
      _ = 2 ^ m * a2 + a1 := by
          simp [hdecomp]
      _ = a1 + 2 ^ m * a2 := by
          ac_rfl
  -- Use hrhs to rewrite the right-hand side, still modulo 2^m * 2^(2*m)
  have h4 :
      a1 % 2 ^ m + 2 ^ m * (c1 % 2 ^ m) + 2 ^ (2 * m) * ((a3 + c1 >>> m) % 2 ^ m)
        ≡ a1 + 2 ^ m * a2 + 2 ^ (2 * m) * (a3 % 2 ^ m) [MOD 2 ^ m * 2 ^ (2 * m)] := by
    simpa [c1, hrhs, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h3
  -- Finally, rewrite modulus 2^m * 2^(2*m) as 2^(3*m)
  have h3m : 3 * m = m + 2 * m := by
    -- Using succ_mul: (2+1)*m = 2*m + m
    have h := Nat.succ_mul 2 m
    -- h: (2 + 1) * m = 2 * m + m
    have h' : 3 * m = 2 * m + m := by simpa using h
    simpa [Nat.add_comm] using h'
  simpa [h3m, pow_add] using h4

theorem eq3 (a0 a1 a2 a3 m : ℕ) :
  a0 % 2^m +
  2^m * ((a1 + a0 >>> m) % 2^m) +
  2^(2*m) * ( (a2 + (a1 + a0 >>> m) >>> m) % 2^m) +
  2^(3*m) * ( (a3 +(a2 + (a1 + a0 >>> m) >>> m) >>> m) % 2^m)
  ≡ a0 + 2^m * a1 + 2^(2*m) * a2 + 2^(3*m) * (a3 % 2^m) [MOD 2^ (4* m)] := by
  set c1 := a1 + a0 >>> m with hc1
  have h0 := (eq2 c1 a2 a3 m).mul_left' (2 ^ m)
  have h1 := h0.add_left (a0 % 2 ^ m)
  simp[mul_add,← add_assoc, mul_add, ← add_assoc, mul_add,
  ← add_assoc, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
  ← mul_assoc, ← pow_add, ← pow_add, ← pow_add,
  (by scalar_tac : m + m = 2 * m), (by scalar_tac : m + 2 * m = 3 * m),
  (by scalar_tac : m + 3 * m = 4 * m)] at h1
  apply Nat.ModEq.trans h1
  apply Nat.ModEq.add_right
  apply Nat.ModEq.add_right
  have hrhs : a0 % 2 ^ m + 2 ^ m * c1 = a0 + 2 ^ m * a1 := by
    have hdecomp := Nat.mod_add_div a0 (2 ^ m)
    have hshift : a0 >>> m = a0 / 2 ^ m := by
      simp [Nat.shiftRight_eq_div_pow]
    calc
      a0 % 2 ^ m + 2 ^ m * c1
          = a0 % 2 ^ m + 2 ^ m * (a1 + a0 / 2 ^ m) := by simp [c1, hshift]
      _ = a0 % 2 ^ m + 2 ^ m * a1 + 2 ^ m * (a0 / 2 ^ m) := by
          simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 ^ m * a1 + (a0 % 2 ^ m + 2 ^ m * (a0 / 2 ^ m)) := by
          ac_rfl
      _ = 2 ^ m * a1 + a0 := by
          simp [hdecomp]
      _ = a0 + 2 ^ m * a1 := by
          ac_rfl
  rw[hrhs]


theorem eq4 (a0 a1 a2 a3 a4 m : ℕ) :
  a0 % 2^m +
  2^m * ((a1 + a0 >>> m) % 2^m) +
  2^(2*m) * ( (a2 + (a1 + a0 >>> m) >>> m) % 2^m) +
  2^(3*m) * ( (a3 + (a2 + (a1 + a0 >>> m) >>> m) >>> m) % 2^m) +
  2^(4*m) * ( (a4 + (a3 + (a2 + (a1 + a0 >>> m) >>> m) >>> m) >>> m) % 2^m)
  ≡ a0 + 2^m * a1 + 2^(2 * m) * a2 + 2^(3 * m) * a3 + 2^(4 * m) * (a4 % 2^m) [MOD 2^ (5 * m)] := by
  set c1 := a1 + a0 >>> m with hc1
  have h0 := (eq3 c1 a2 a3 a4 m).mul_left' (2 ^ m)
  have h1 := h0.add_left (a0 % 2 ^ m)
  simp[mul_add, ← add_assoc, mul_add, ← add_assoc, mul_add,
  ← add_assoc, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
  ← mul_assoc, ← pow_add, ← pow_add, ← pow_add,
  (by scalar_tac : m + m = 2 * m), (by scalar_tac : m + 2 * m = 3 * m),
  (by scalar_tac : m + 3 * m = 4 * m), (by scalar_tac : m + 4 * m = 5 * m),
  mul_add, ← add_assoc, mul_add, ← add_assoc] at h1
  apply Nat.ModEq.trans h1
  apply Nat.ModEq.add_right
  apply Nat.ModEq.add_right
  apply Nat.ModEq.add_right
  have hrhs : a0 % 2 ^ m + 2 ^ m * c1 = a0 + 2 ^ m * a1 := by
    have hdecomp := Nat.mod_add_div a0 (2 ^ m)
    have hshift : a0 >>> m = a0 / 2 ^ m := by
      simp [Nat.shiftRight_eq_div_pow]
    calc
      a0 % 2 ^ m + 2 ^ m * c1
          = a0 % 2 ^ m + 2 ^ m * (a1 + a0 / 2 ^ m) := by simp [c1, hshift]
      _ = a0 % 2 ^ m + 2 ^ m * a1 + 2 ^ m * (a0 / 2 ^ m) := by
          simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 ^ m * a1 + (a0 % 2 ^ m + 2 ^ m * (a0 / 2 ^ m)) := by
          ac_rfl
      _ = 2 ^ m * a1 + a0 := by
          simp [hdecomp]
      _ = a0 + 2 ^ m * a1 := by
          ac_rfl
  rw[hrhs]






theorem eq5 (a0 a1 a2 a3 a4 : ℕ) :
  a0 % 2 ^ 52 +
  2^ 52 * ((a1 + a0 >>> 52) % 2 ^ 52) +
  2^(2 * 52) * ( (a2 + (a1 + a0 >>> 52) >>> 52) % 2 ^ 52) +
  2^(3 * 52) * ( (a3 + (a2 + (a1 + a0 >>> 52) >>> 52) >>> 52) % 2 ^ 52) +
  2^(4 * 52) * ( (a4 + (a3 + (a2 + (a1 + a0 >>> 52) >>> 52) >>> 52) >>> 52) % 2 ^ 52)
  ≡ a0 + 2 ^ 52 * a1 + 2 ^ (2 * 52) * a2 + 2 ^ (3 * 52) * a3 + 2^(4 * 52) * (a4 % 2 ^ 52) [MOD L] := by
   have :=eq3 a0 a1 a2 a3 52
   sorry






set_option maxHeartbeats 10000000 in
-- progress simp_all is heavy


/-- Spec for one full pass of `add_loop` starting at i = 0 with a zero
accumulator and zero incoming carry. It states that the routine computes the
low-260-bit sum of `a` and `b` (i.e., addition modulo 2^(52*5)), and the result
has properly bounded limbs.

We keep the proof as a TODO, mirroring the style of other spec files. -/

@[progress]
theorem add_loop_full_spec (a b : Scalar52) (mask : U64)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1) :
    ∃ s,
      add_loop a b ZERO mask 0#u64 0#usize = ok s ∧
      Scalar52_as_Nat s ≡ (Scalar52_as_Nat a + Scalar52_as_Nat b) [MOD (2^ (5 *52))] ∧
      (∀ j < 5, s[j]!.val < 2 ^ 52)
       := by
  -- Outline: unfold `add_loop` and proceed by induction on the remaining limb
  -- count, tracking the carry and using the mask hypothesis to show each limb
  -- is reduced modulo 2^52. The numeric relation follows by summing the limb
  -- contributions and noting the recursion implements base-2^52 addition.
  -- TODO: complete proof
  have sum0 := add_lt_add_of_lt_of_lt_nat  (ha 0 (by simp)) (hb 0 (by simp))
  have sum1 := add_lt_add_of_lt_of_lt_nat  (ha 1 (by simp)) (hb 1 (by simp))
  have sum2 := add_lt_add_of_lt_of_lt_nat  (ha 2 (by simp)) (hb 2 (by simp))
  have sum3 := add_lt_add_of_lt_of_lt_nat  (ha 3 (by simp)) (hb 3 (by simp))
  have sum4 := add_lt_add_of_lt_of_lt_nat  (ha 4 (by simp)) (hb 4 (by simp))
  have i0_lt: ((a[0]!).val + (b[0]!).val) >>> 52 < 3 := by
      simp[Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      simp_all
      apply lt_trans sum0
      simp
  have i1_lt: ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52 < 3 := by
       simp[Nat.shiftRight_eq_div_pow]
       apply Nat.div_lt_of_lt_mul
       have := add_lt_add_of_lt_of_lt_nat  sum1 i0_lt
       simp[Nat.shiftRight_eq_div_pow] at this
       apply lt_trans this
       simp
  have i2_lt: ((a[2]!).val + (b[2]!).val +
    ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52) >>> 52 < 3 := by
       simp[Nat.shiftRight_eq_div_pow]
       apply Nat.div_lt_of_lt_mul
       have := add_lt_add_of_lt_of_lt_nat  sum2 i1_lt
       simp[Nat.shiftRight_eq_div_pow] at this
       apply lt_trans this
       simp
  have i3_lt: ((a[3]!).val + (b[3]!).val +
    ((a[2]!).val + (b[2]!).val +
    ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52)
     >>> 52) >>> 52 < 3 := by
       simp[Nat.shiftRight_eq_div_pow]
       apply Nat.div_lt_of_lt_mul
       have := add_lt_add_of_lt_of_lt_nat  sum3 i2_lt
       simp[Nat.shiftRight_eq_div_pow] at this
       apply lt_trans this
       simp
  unfold add_loop
  simp[Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index, IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut]
  progress*
  have i0_eq:  ((a[0]!).val + (b[0]!).val) % 2^52 =  i5.val := by
    have := land_pow_two_sub_one_eq_mod carry1 52
    simp_all
  unfold add_loop
  simp[Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index, IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut]
  progress*
  have i1_eq:   ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) % 2^52 = i5.val:= by
    have := land_pow_two_sub_one_eq_mod carry1 52
    simp_all
  unfold add_loop
  simp[Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index, IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut]
  simp_all
  progress*
  · simp_all
    apply le_trans (le_of_lt sum2)
    scalar_tac
  · simp_all
    have := add_lt_add_of_lt_of_lt_nat  sum2 i1_lt
    simp[Nat.shiftRight_eq_div_pow] at this
    simp[Nat.shiftRight_eq_div_pow]
    apply le_trans (le_of_lt this)
    scalar_tac
  have i2_eq:  ((a[2]!).val + (b[2]!).val +
    ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52) % 2^52 = i5.val := by
    have := land_pow_two_sub_one_eq_mod carry1 52
    simp_all
  unfold add_loop
  simp_all[Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index, IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut]
  progress*
  · simp_all
    apply le_trans (le_of_lt sum3)
    scalar_tac
  · simp_all
    have := add_lt_add_of_lt_of_lt_nat  sum3 i2_lt
    simp[Nat.shiftRight_eq_div_pow] at this
    simp[Nat.shiftRight_eq_div_pow]
    apply le_trans (le_of_lt this)
    scalar_tac
  have i3_eq:  ((a[3]!).val + (b[3]!).val +
    ((a[2]!).val + (b[2]!).val +
    ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52)
     >>> 52) % 2^52 = i5.val := by
    have := land_pow_two_sub_one_eq_mod carry1 52
    simp_all
  unfold add_loop
  simp_all[Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index, IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut]
  progress*
  · simp_all
    apply le_trans (le_of_lt sum4)
    scalar_tac
  · simp_all
    have := add_lt_add_of_lt_of_lt_nat  sum4 i3_lt
    simp[Nat.shiftRight_eq_div_pow] at this
    simp[Nat.shiftRight_eq_div_pow]
    apply le_trans (le_of_lt this)
    scalar_tac
  have i4_eq: ((a[4]!).val + (b[4]!).val + ((a[3]!).val + (b[3]!).val +
    ((a[2]!).val + (b[2]!).val +
    ((a[1]!).val + (b[1]!).val +
    ((a[0]!).val + (b[0]!).val) >>> 52) >>> 52)
     >>> 52) >>> 52) % 2^52 = i5.val := by
    have := land_pow_two_sub_one_eq_mod carry1 52
    simp_all
  unfold add_loop
  simp_all
  constructor
  · simp_all[Scalar52_as_Nat, Finset.sum_range_succ]
    rw[← i0_eq, ← i1_eq, ← i2_eq, ← i3_eq, ← i4_eq]
    have := eq4 ((a[0]!).val + (b[0]!).val) ((a[1]!).val + (b[1]!).val) ((a[2]!).val + (b[2]!).val)
     ((a[3]!).val + (b[3]!).val) ((a[4]!).val + (b[4]!).val) 52
    simp at this
    apply Nat.ModEq.trans this
    have : Scalar52_as_Nat a + Scalar52_as_Nat b=
    ((a[0]!).val + (b[0]!).val) +
    2 ^ 52 * ((a[1]!).val + (b[1]!).val) +
    2 ^ (2 * 52) * ((a[2]!).val + (b[2]!).val) +
    2 ^ (3 * 52) * ((a[3]!).val + (b[3]!).val)  +
    2 ^ (4 * 52) * ((a[4]!).val + (b[4]!).val) := by
      simp_all[Scalar52_as_Nat, Finset.sum_range_succ]
      scalar_tac
    simp[Scalar52_as_Nat, Finset.sum_range_succ] at this
    rw[this]
    apply Nat.ModEq.add_left
    have := (@Nat.ModEq.mul_left_cancel_iff'  (((a[4]!).val + (b[4]!).val) % 2 ^ 52) ((a[4]!).val + (b[4]!).val) (2 ^ (4 * 52)) ( 2 ^ 52) (by simp)).mpr
    simp at this
    apply this
    rw[Nat.ModEq]
    apply Nat.mod_modEq
  · intro j hj
    unfold ZERO ZERO_body eval_global
    simp[Array.repeat]
    cases j
    · simp_all
      rw[← i0_eq]
      apply Nat.mod_lt
      simp
    · rename_i j
      cases j
      · simp_all
        rw[← i1_eq]
        apply Nat.mod_lt
        simp
      · rename_i j
        cases j
        · simp_all
          rw[← i2_eq]
          apply Nat.mod_lt
          simp
        · rename_i j
          cases j
          · simp_all
            rw[← i3_eq]
            apply Nat.mod_lt
            simp
          · rename_i j
            cases j
            · simp_all
              rw[← i4_eq]
              apply Nat.mod_lt
              simp
            · contradiction





/-
natural language description:

    • Takes two input unpacked scalars a and a and returns an unpacked scalar v representing
      the sum (a + a) mod L where L is the group order.

natural language specs:

    • scalar_to_nat(c) = (scalar_to_nat(a) + scalar_to_nat(a)) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.add`**:
- No panic (always returns successfully)
- The result represents the sum of the two input scalars modulo L
-/
@[progress]
theorem add_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52) :
    ∃ c,
    add a b = ok c ∧
    Scalar52_as_Nat c = (Scalar52_as_Nat a + Scalar52_as_Nat b) % L
    := by
  unfold add
  progress*
  · unfold  constants.L; decide
  · have : Scalar52_as_Nat constants.L = L := by
      unfold constants.L
      decide
    rw[this,add_comm] at res_post_1
    rw[(by simp: Scalar52_as_Nat sum  = 0 + Scalar52_as_Nat sum )] at res_post_1
    have eq_mod := Nat.ModEq.add_left_cancel  ( by decide : L ≡ 0 [MOD L] ) res_post_1

    have := Scalar52_as_Nat_bound sum sum_post_2
    have := Nat.mod_eq_of_lt this
    rw[Nat.ModEq] at sum_post_1
    have : Scalar52_as_Nat sum =  (Scalar52_as_Nat a + Scalar52_as_Nat b) % (2 ^ (5 * 52)) := by
      simp_all
    rw[this] at eq_mod
    have := Scalar52_as_Nat_bound res res_post_2
    have := Nat.mod_eq_of_lt this





















end curve25519_dalek.backend.serial.u64.scalar.Scalar52
