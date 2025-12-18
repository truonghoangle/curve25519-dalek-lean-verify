/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Add

/-! # Spec Theorem for `Scalar52::from_bytes_wide`

Specification and proof for `Scalar52::from_bytes_wide`.

This function constructs an unpacked scalar from a wide byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes a 64-byte array b as input and returns an unpacked scalar u that
      represents the 512-bit integer value reduced modulo L, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u8x64_to_nat(b) % L
-/

/- **Spec for `backend.serial.u64.scalar.Scalar52.from_bytes_wide_loop`**:
- Starting from index `i` with accumulator `words`
- Packs 8 consecutive bytes from position `i*8` through `i*8+7` into words[i] in little-endian order
- Each iteration processes one 64-bit word by combining 8 bytes
- Parts of words before index i are preserved
- The result satisfies: words represents the byte array interpreted as U64 words in little-endian format -/

@[progress]
theorem from_bytes_wide_loop_spec (bytes : Array U8 64#usize) (words : Array U64 8#usize) (i : Usize)
    (hi : i.val ≤ 8)
    (hwords : ∀ j < 8, i.val ≤ j → words[j]!.val = 0) :
    ∃ words', from_bytes_wide_loop bytes words i = ok words' ∧
    (∀ j < i.val, words'[j]!.val = words[j]!.val) ∧
    (∀ j < 8, i.val ≤ j →
      words'[j]!.val = ∑ k ∈ Finset.range 8, 2^(8 * k) * bytes[j * 8 + k]!.val) := by
    sorry

/- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/


set_option maxHeartbeats 100000000 in
-- simp_all heavy


@[progress]
theorem from_bytes_wide_spec (b : Array U8 64#usize) :
    ∃ u, from_bytes_wide b = ok u ∧
    Scalar52_as_Nat u = U8x64_as_Nat b % L := by
    unfold from_bytes_wide IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
    progress*
    · simp_all [Array.repeat]
      decide
    · simp [*]
      decide
    · simp [*]
      have : mask.val = 2 ^ 52-1 := by simp [*]; scalar_tac
      intro i hi
      cases i
      · simp[i2_post_1]
        rw[this, land_pow_two_sub_one_eq_mod]
        grind
      · rename_i i
        cases i
        · simp[i7_post_1]
          rw[this, land_pow_two_sub_one_eq_mod]
          grind
        · rename_i i
          cases i
          · simp[i12_post_1]
            rw[this, land_pow_two_sub_one_eq_mod]
            grind
          · rename_i i
            cases i
            · simp[i17_post_1]
              rw[this, land_pow_two_sub_one_eq_mod]
              grind
            · rename_i i
              cases i
              · simp[i22_post_1]
                rw[this, land_pow_two_sub_one_eq_mod]
                have := Nat.mod_lt (i21.val) (by simp : 0 < 2 ^ 52)
                apply lt_trans this
                simp
              · grind

    · unfold constants.R
      decide
    · simp [*]
      have : mask.val = 2 ^ 52-1 := by simp [*]; scalar_tac
      intro i hi
      cases i
      · simp[i24_post_1]
        rw[this, land_pow_two_sub_one_eq_mod]
        grind
      · rename_i i
        cases i
        · simp[i29_post_1]
          rw[this, land_pow_two_sub_one_eq_mod]
          grind
        · rename_i i
          cases i
          · simp[i34_post_1]
            rw[this, land_pow_two_sub_one_eq_mod]
            grind
          · rename_i i
            cases i
            · simp[i39_post_1]
              rw[this, land_pow_two_sub_one_eq_mod]
              grind
            · rename_i i
              cases i
              · simp[i41_post_1, i36_post]
                rw[Nat.shiftRight_eq_div_pow ]
                apply Nat.div_lt_of_lt_mul
                simp_all [Finset.sum_range_succ]
                sorry
              · grind
    · unfold constants.RR
      decide
    · sorry
      



























end curve25519_dalek.backend.serial.u64.scalar.Scalar52
