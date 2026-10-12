/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Spec theorem for `curve25519_dalek::scalar::clamp_integer`

Applies bitwise clamping to a 32-byte little-endian scalar representation:
• clears the three lowest bits of byte[0] (ensuring divisibility by the cofactor h = 8),
• clears the highest bit of byte[31] (ensuring the value < 2^255),
• sets bit 6 of byte[31] (ensuring the value ≥ 2^254).

The result is a properly clamped scalar in the range [2^254, 2^255) divisible by h = 8,
suitable for use in X25519 scalar multiplication.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek scalar

attribute [-simp] Int.reducePow Nat.reducePow

namespace curve25519_dalek.scalar

/-- **Spec theorem for `curve25519_dalek::scalar::clamp_integer`**
• The function always succeeds (no panic) for any 32-byte input
• h divides U8x32_as_Nat result (the result is divisible by the cofactor h = 8)
• U8x32_as_Nat result < 2^255
• 2^254 ≤ U8x32_as_Nat result
• Functional characterization: the result is a *deterministic function* of the input
  bytes, matching RFC 7748's `decodeScalar25519`:
  `U8x32_as_Nat result = 2^254 + 8 * ((U8x32_as_Nat bytes / 8) % 2^251)`,
  i.e. clear the low 3 bits, keep bits 3..253, force bit 254, clear bit 255.
  The divisibility and range bounds above are corollaries of this equality.
-/
@[step]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Array U8 32#usize) =>
      h ∣ U8x32_as_Nat result ∧
      U8x32_as_Nat result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat result ∧
      U8x32_as_Nat result = 2 ^ 254 + 8 * (U8x32_as_Nat bytes / 8 % 2 ^ 251) ⦄ := by
  unfold clamp_integer h
  step*
  subst_vars
  unfold U8x32_as_Nat
  have hlen : ((bytes : List U8)).length = 32 := by scalar_tac
  have get_set_self : ∀ (l : List U8) (i : ℕ) (v : U8), i < l.length →
      (l.set i v)[i]! = v := by
    intro l i v hi
    rw [getElem!_pos _ _ (by simpa using hi), List.getElem_set_self]
  have get_set_ne : ∀ (l : List U8) (i j : ℕ) (v : U8), i ≠ j → j < l.length →
      (l.set i v)[j]! = l[j]! := by
    intro l i j v hne hj
    rw [getElem!_pos (l.set i v) j (by simpa using hj), getElem!_pos l j hj,
      List.getElem_set_ne hne]
  have hand : ∀ n < 256, n &&& 248 = 8 * (n / 8) := by decide
  have hor : ∀ n < 256, n &&& 127 ||| 64 = 64 + n % 64 := by decide
  have h0 : i1.val = 8 * (((bytes : List U8)[0]!).val / 8) := by
    rw [i1_post1, UScalar.val_and]
    exact hand _ (by scalar_tac)
  have h31 : i5.val = 64 + ((bytes : List U8)[31]!).val % 64 := by
    rw [i5_post1, UScalar.val_or]
    simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq]
    rw [get_set_self _ _ _ (by simp [hlen]), i3_post1, UScalar.val_and]
    simp only [Array.set_val_eq, UScalar.ofNatCore_val_eq]
    rw [get_set_ne _ _ _ _ (by omega) (by omega)]
    exact hor _ (by scalar_tac)
  have hsplit : ∀ l : List U8,
      ∑ x ∈ Finset.range 32, 2 ^ (8 * x) * (l[x]!).val =
      (l[0]!).val + (∑ x ∈ Finset.Ico 1 31, 2 ^ (8 * x) * (l[x]!).val)
        + 2 ^ 248 * (l[31]!).val := by
    intro l
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    norm_num
  simp only [Array.getElem!_Nat_eq, Array.set_val_eq, List.set_set, hsplit,
    UScalar.ofNatCore_val_eq]
  have hmid : ∑ x ∈ Finset.Ico 1 31,
      2 ^ (8 * x) * ((((bytes : List U8).set 0 i1).set 31 i5)[x]!).val =
      ∑ x ∈ Finset.Ico 1 31, 2 ^ (8 * x) * (((bytes : List U8))[x]!).val := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_Ico.mp hx
    rw [get_set_ne _ _ _ _ (by omega) (by simp [hlen]; omega),
      get_set_ne _ _ _ _ (by omega) (by omega)]
  rw [get_set_ne _ _ _ _ (by omega) (by simp [hlen]), get_set_self _ _ _ (by omega),
    get_set_self _ _ _ (by simp [hlen]), hmid, h0, h31]
  set M := ∑ x ∈ Finset.Ico 1 31, 2 ^ (8 * x) * (((bytes : List U8))[x]!).val with hM
  have hMdvd : 256 ∣ M := by
    apply Finset.dvd_sum
    intro x hx
    have hx' := Finset.mem_Ico.mp hx
    exact Dvd.dvd.mul_right
      ((show (256 : ℕ) = 2 ^ 8 by norm_num) ▸ pow_dvd_pow 2 (by omega)) _
  have hMle : M ≤ 2 ^ 248 - 256 := by
    have : M ≤ ∑ x ∈ Finset.Ico 1 31, 2 ^ (8 * x) * 255 := by
      apply Finset.sum_le_sum
      intro x hx
      gcongr
      scalar_tac
    calc M ≤ ∑ x ∈ Finset.Ico 1 31, 2 ^ (8 * x) * 255 := this
    _ = 2 ^ 248 - 256 := by decide
  have hb0 : ((bytes : List U8)[0]!).val < 256 := by scalar_tac
  have hb31 : ((bytes : List U8)[31]!).val < 256 := by scalar_tac
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Spec theorem for `curve25519_dalek::scalar::clamp_integer`** (via `U8x32_as_Nat_foldr`)
• The function always succeeds (no panic) for any 32-byte input
• h divides U8x32_as_Nat_foldr result
• U8x32_as_Nat_foldr result < 2^255
• 2^254 ≤ U8x32_as_Nat_foldr result
• Functional characterization (RFC 7748 `decodeScalar25519`):
  `U8x32_as_Nat_foldr result = 2^254 + 8 * ((U8x32_as_Nat_foldr bytes / 8) % 2^251)`
-/
theorem clamp_integer_spec' (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Array U8 32#usize) =>
      h ∣ U8x32_as_Nat_foldr result ∧
      U8x32_as_Nat_foldr result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat_foldr result ∧
      U8x32_as_Nat_foldr result =
        2 ^ 254 + 8 * (U8x32_as_Nat_foldr bytes / 8 % 2 ^ 251) ⦄ := by
  simp only [← U8x32_as_Nat_eq_foldr']
  apply clamp_integer_spec

end curve25519_dalek.scalar
