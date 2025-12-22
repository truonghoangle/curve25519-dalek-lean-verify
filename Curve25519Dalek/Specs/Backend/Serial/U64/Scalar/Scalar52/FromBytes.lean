/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes

/-! # Spec Theorem for `Scalar52::from_bytes`

Specification and proof for `Scalar52::from_bytes`.

This function constructs an unpacked scalar from a byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

open curve25519_dalek.backend.serial.u64.field.FieldElement51


/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_loop`**:
- No panic (always returns successfully)
- The loop converts bytes to words, preserving the numeric value
- Processes bytes in 8-byte chunks to create 64-bit words
-/

lemma LOW_52_BIT_MASK_spec : 1 <<< 52 % U64.size - 1 = 2^ 52 -1 := by
  scalar_tac

lemma LOW_48_BIT_MASK_spec : 1 <<< 48 % U64.size - 1 = 2^ 48 -1 := by
  scalar_tac


theorem lsb_or_leftShift_eq_lsb {n : ℕ} (a b : ℕ) (hn : n < 12) :
  ((a >>> 52 ||| b <<< 12 % U64.size) % 2 ^ 52) >>> n % 2 = ((a >>> 52) % 2^ 52) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 52 % 2 ^ 52) >>> n) ((b <<< 12 % U64.size % 2 ^ 52) >>> n) 1
  rw[(by simp : 2 ^ 1 =2)] at this
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 :  b * 2 ^ 12 % 4503599627370496 / 2 ^ n % 2 = 0 := by
    interval_cases n
    all_goals grind
  rw[h1]
  grind



theorem lsb_or_leftShift_eq_lsbI {n : ℕ} (a b : U64) (hn : 12 ≤ n) :
  ((a.val >>> 52 ||| b.val <<< 12 % U64.size) % 2 ^ 52) >>> n  = ((b.val <<< 12) %  2 ^ 52) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have a_lt: a.val < 2 ^ 64 := by scalar_tac
  have : (a.val / 2 ^ 52) % 4503599627370496 =(a.val / 2 ^ 52) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans a_lt
    simp
  have  :  (a.val / 2 ^ 52) % 4503599627370496 / 2 ^ n = a.val / 2 ^ (52+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a.val / 2 ^ 52) % 4503599627370496 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le a_lt
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind




theorem lsb_or_leftShift_eq_lsb_40_24 {n : ℕ} (a b : ℕ) (hn : n < 17) :
  ((a >>> 40 ||| b <<< 24 % U64.size) % 2 ^ 52) >>> n % 2^8 = ((a >>> 40) % 2^ 52) >>> n % 2^8 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 40 % 2 ^ 52) >>> n) ((b <<< 24 % U64.size % 2 ^ 52) >>> n) 8
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 :  b * 2 ^ 24 % 4503599627370496 / 2 ^ n % 2 ^8 = 0 := by
    interval_cases n
    all_goals grind
  rw[(by simp : 256= 2 ^8), h1]
  grind




theorem lsb_or_leftShift_eq_lsb_28_36 {n : ℕ} (a b : ℕ) (hn : n < 29) :
  ((a >>> 28 ||| b <<< 36 % U64.size) % 2 ^ 52) >>> n % 2^8 = ((a >>> 28) % 2^ 52) >>> n % 2^8 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 28 % 2 ^ 52) >>> n) ((b <<< 36 % U64.size % 2 ^ 52) >>> n) 8
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 :  b * 2 ^ 36 % 4503599627370496 / 2 ^ n % 2 ^8 = 0 := by
    interval_cases n
    all_goals grind
  rw[(by simp : 256= 2 ^8), h1]
  grind



theorem lsb_or_leftShift_eq_lsb_28_36_2 {n : ℕ} (a b : ℕ) (hn : n < 29) :
  ((a >>> 28 ||| b <<< 36 % U64.size) % 2 ^ 52) >>> n % 2 = ((a >>> 28) % 2^ 52) >>> n % 2 := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  have := @Nat.or_mod_two_pow ((a >>> 28 % 2 ^ 52) >>> n) ((b <<< 36 % U64.size % 2 ^ 52) >>> n) 1
  rw[this]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 :  b * 2 ^ 36 % 4503599627370496 / 2 ^ n % 2  = 0 := by
    interval_cases n
    all_goals grind
  rw[ h1]
  grind





theorem lsb_or_leftShift_eq_lsbI_40_24 {n : ℕ} (a b : U64) (hn : 24 ≤ n) :
  ((a.val >>> 40 ||| b.val <<< 24 % U64.size) % 2 ^ 52) >>> n  = ((b.val <<< 24) %  2 ^ 52) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have a_lt: a.val < 2 ^ 64 := by scalar_tac
  have : (a.val / 2 ^ 40) % 4503599627370496 =(a.val / 2 ^ 40) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans a_lt
    simp
  have  :  (a.val / 2 ^ 40) % 4503599627370496 / 2 ^ n = a.val / 2 ^ (40+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a.val / 2 ^ 40) % 4503599627370496 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le a_lt
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind





theorem lsb_or_leftShift_eq_lsbI_28_36 {n : ℕ} (a b : U64) (hn : 36 ≤ n) :
  ((a.val >>> 28 ||| b.val <<< 36 % U64.size) % 2 ^ 52) >>> n  = ((b.val <<< 36) %  2 ^ 52) >>> n  := by
  rw[Nat.or_mod_two_pow, Nat.shiftRight_or_distrib]
  simp [U64.size, U64.numBits]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have a_lt: a.val < 2 ^ 64 := by scalar_tac
  have : (a.val / 2 ^ 28) % 4503599627370496 =(a.val / 2 ^ 28) := by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_trans a_lt
    simp
  have  :  (a.val / 2 ^ 28) % 4503599627370496 / 2 ^ n = a.val / 2 ^ (28+ n) := by
    rw[this]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have h1 :  (a.val / 2 ^ 28) % 4503599627370496 / 2 ^ n = 0 := by
    rw[this]
    simp
    apply lt_of_lt_of_le a_lt
    apply Nat.pow_le_pow_right <;> omega
  rw[h1]
  grind


theorem powTwo_block_split_52 (z : ℕ) :
  z % 2 ^ 8 --0
  + 2 ^ 8 * ((z % 2 ^ 52)  >>> 8 % 2 ^ 8) --8
  + 2 ^ 16 * ((z % 2 ^ 52)  >>> 16 % 2 ^ 8) --16
  + 2 ^ 24 * ((z % 2 ^ 52)   >>> 24 % 2 ^ 8) --24
  + 2 ^ 32 * ((z % 2 ^ 52)   >>> 32 % 2 ^ 8) --32
  + 2 ^ 40 * ((z % 2 ^ 52)   >>> 40 % 2 ^ 8) --40
  + 2 ^ 48 * (
        ((z % 2 ^ 52)   >>> 48 >>> 0) % 2
        + 2* (((z % 2 ^ 52)   >>> 48) >>> 1 % 2)
        + 2 ^2 * (((z % 2 ^ 52)   >>> 48) >>> 2 % 2)
        + 2 ^3 * (((z % 2 ^ 52)   >>> 48) >>> 3 % 2)
        )
  = z % 2^ 52 := by
  have := powTwo_six_block_split z (by simp : 6 * 8 < 52)
  rw [this]
  have mod52: ((z % 2 ^ 52)   >>> 48) % 2^52 = (z % 2 ^ 52)   >>> 48 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := powTwo_four_block_split ((z % 2 ^ 52)   >>> 48) (by simp : 4 * 1 < 52)
  rw [mod52] at this
  simp at this
  simp [this]
  have mod8: ((z % 4503599627370496)   >>> 48) % 16 = (z % 4503599627370496)   >>> 48 := by
    apply Nat.mod_eq_of_lt
    rw[ Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    simp
    apply Nat.mod_lt z (by simp)
  rw [mod8, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod  (z % 2 ^ 52) (2 ^ 48)
  simp [add_comm] at this
  simp [this]



theorem u8x8_to_nat_extract_byte_1 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 8 % 2 ^ 8 = z1.val := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_2 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 16 % 2 ^ 8 = z2.val := by
   rw[hi]
   scalar_tac

theorem u8x8_to_nat_extract_byte_3 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 24 % 2 ^ 8 = z3.val := by
   rw[hi]
   scalar_tac

theorem u8x8_to_nat_extract_byte_4 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 32 % 2 ^ 8 = z4 := by
   rw[hi]
   scalar_tac

theorem u8x8_to_nat_extract_byte_5 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 40 % 2 ^ 8 = z5.val := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_5I {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 i >>> 40 % 2 ^ 8 = z5.val := by
   rw[hi]
   scalar_tac



theorem u8x8_to_nat_extract_byte_6 {i n : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hn : n < 4)
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i % 2^ 52) >>> 48 >>> n % 2  = z6.val >>>n %2 := by
  rw[hi]
  interval_cases n
  any_goals scalar_tac







theorem u8x8_to_nat_extract_byte_6_0 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 i >>> 48  % 2 ^8  = z6.val  % 2 ^8 := by
  rw[hi]
  any_goals scalar_tac

theorem u8x8_to_nat_extract_byte_6_1 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 i >>> 56  % 2 ^8  = z7.val  % 2 ^8 := by
  rw[hi]
  any_goals scalar_tac



theorem u8x8_to_nat_extract_byte_6I {i n : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hn : n < 4)
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 52) % 2 ^ 52) >>> n   % 2 = (z6.val >>> (n + 4)) % 2  := by
   rw[hi]
   interval_cases n
   any_goals scalar_tac






theorem u8x8_to_nat_extract_byte_6I_28 {i n : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hn : n < 4)
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 28) % 2 ^ 52) >>> n   % 2 = ((z3.val % 2 ^ 52) >>> (n + 4)) % 2  := by
   rw[hi]
   interval_cases n
   any_goals scalar_tac


theorem u8x8_to_nat_extract_byte_6I_28_4 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 28) % 2 ^ 52) >>> 4   % 2 ^ 8 = (z4.val ) % 2 ^8  := by
    rw[hi]
    scalar_tac




theorem u8x8_to_nat_extract_byte_6I_28_12 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 28) % 2 ^ 52) >>> 12   % 2 ^ 8 = (z5.val ) % 2 ^8  := by
   rw[hi]
   scalar_tac



theorem u8x8_to_nat_extract_byte_6I_28_20 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 28) % 2 ^ 52) >>> 20   % 2 ^ 8 = (z6.val ) % 2 ^8  := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_6I_28_28 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 28) % 2 ^ 52) >>> 28   % 2 ^ 8 = (z7.val ) % 2 ^8  := by
   rw[hi]
   scalar_tac





theorem u8x8_to_nat_extract_byte_7 {i n : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hn : n < 8)
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 52) % 2 ^ 52) >>> (n+4)   % 2 = (z7.val >>> n) % 2  := by
   rw[hi]
   interval_cases n
   any_goals scalar_tac



theorem u8x8_to_nat_extract_byte_12_0 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 12 % 2 ^ 52) >>> 12 % 2 ^ 8 = z0.val := by
   rw[hi]
   scalar_tac

theorem u8x8_to_nat_extract_byte_36_0 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 36 % 2 ^ 52) >>> 36 % 2 ^ 8 = z0.val := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_44_0 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 36 % 2 ^ 52) >>> 44 % 2 ^ 8 = z1.val := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_12_1 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 12 % 2 ^ 52) >>> 20 % 2 ^ 8 = z1.val := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_12_2 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 12 % 2 ^ 52) >>> 28 % 2 ^ 8 = z2.val := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_12_3 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 12 % 2 ^ 52) >>> 36 % 2 ^ 8 = z3.val := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_12_4 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 12 % 2 ^ 52) >>> 44 % 2 ^ 8 = z4.val := by
   rw[hi]
   scalar_tac





theorem u8x8_to_nat_extract_byte_24_0 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 24 % 2 ^ 52) >>> 24 % 2 ^ 8 = z0.val := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_24_1 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 24 % 2 ^ 52) >>> 32 % 2 ^ 8 = z1.val := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_24_2 {z0 z1 z2 z3 z4 z5 z6 z7 : U8} {i : ℕ}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 (i * 2 ^ 24 % 2 ^ 52) >>> 40 % 2 ^ 8 = z2.val := by
   rw[hi]
   scalar_tac





theorem u8x8_to_nat_extract_byte_6_24 {i n : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hn : n < 4)
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i * 2 ^ 24) % 2^ 52) >>> 48 >>> n % 2  = (z3.val % 2 ^ 52) >>> n %2 := by
  rw[hi]
  interval_cases n
  any_goals scalar_tac



theorem u8x8_to_nat_extract_byte_16_0 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52)    % 2 ^ 8 = (z2.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac

theorem u8x8_to_nat_extract_byte_16_8 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52) >>> 8   % 2 ^ 8 = (z3.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac


theorem u8x8_to_nat_extract_byte_16_16 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52) >>> 16   % 2 ^ 8 = (z4.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac



theorem u8x8_to_nat_extract_byte_16_24 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52) >>> 24   % 2 ^ 8 = (z5.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac





theorem u8x8_to_nat_extract_byte_16_32 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52) >>> 32   % 2 ^ 8 = (z6.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac




theorem u8x8_to_nat_extract_byte_16_40 {i : ℕ} {z0 z1 z2 z3 z4 z5 z6 z7 : U8}
  (hi : i = z0.val --0
  + 2 ^ 8 * (z1.val) --8
  + 2 ^ 16 * (z2.val) --16
  + 2 ^ 24 * (z3.val) --24
  + 2 ^ 32 * (z4.val) --32
  + 2 ^ 40 * (z5.val) --40
  + 2 ^ 48 * (z6.val)
  + 2 ^ 56 * (z7.val)) :
 ((i >>> 16) % 2 ^ 52) >>> 40   % 2 ^ 8 = (z7.val) % 2 ^ 8  := by
   rw[hi]
   scalar_tac



theorem powTwo_block_split_52_remain4 (z : ℕ) :
  z % 2^4
    + 2^4  * ((z % 2^52) >>> 4  % 2^8)
    + 2^12 * ((z % 2^52) >>> 12 % 2^8)
    + 2^20 * ((z % 2^52) >>> 20 % 2^8)
    + 2^28 * ((z % 2^52) >>> 28 % 2^8)
    + 2^36 * ((z % 2^52) >>> 36 % 2^8)
    + 2^44 * ((z % 2^52) >>> 44 % 2^8)
    = z % 2^52 := by
  have := powTwo_split_block_5 z (by simp : 5 * 8 + 4 < 52)
  rw [this]
  have mod51 :
      ((z % 2^52) >>> 44) % 2^52 = (z % 2^52) >>> 44 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    apply lt_trans (Nat.mod_lt z (by simp))
    simp
  have := Nat.div_add_mod (z % 2^52) (2^44)
  scalar_tac




@[progress]
theorem from_bytes_loop_spec (bytes : Array U8 32#usize) (words : Array U64 4#usize) (i : Usize)
    (hi : i.val < 5) :
    ∃ words',
    from_bytes_loop bytes words i = ok words' ∧
    (∀ j < i, words'[j]!.val = words[j]!.val) ∧
    (∀ j, i.val ≤ j → j < 4 →
      words'[j]!.val =
        (bytes[j * 8]!.val : Nat) +
        (bytes[j * 8 + 1]!.val : Nat) * 2^8 +
        (bytes[j * 8 + 2]!.val : Nat) * 2^16 +
        (bytes[j * 8 + 3]!.val : Nat) * 2^24 +
        (bytes[j * 8 + 4]!.val : Nat) * 2^32 +
        (bytes[j * 8 + 5]!.val : Nat) * 2^40 +
        (bytes[j * 8 + 6]!.val : Nat) * 2^48 +
        (bytes[j * 8 + 7]!.val : Nat) * 2^56) := by
    unfold from_bytes_loop
    sorry






/-
natural language description:

    • Takes a 32-byte array b as input and returns an unpacked scalar u that
      represents the same 256-bit integer value, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u32x8_to_nat(b)
-/





/- **Spec and proof concerning `scalar.Scalar52.from_bytes`**:
- No panic (always returns successfully)
- The result represents the same number as the input byte array
-/

set_option maxHeartbeats 10000000000 in
-- simp_all heavy

@[progress]
theorem from_bytes_spec (b : Array U8 32#usize) :
    ∃ u,
    from_bytes b = ok u ∧
    Scalar52_as_Nat u = U8x32_as_Nat b ∧
    ∀ i < 5, u[i]!.val < 2 ^ 52
    := by
    unfold from_bytes IndexMutcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index_mut
    simp_all
    progress*
    constructor
    ·   simp [Scalar52_as_Nat, Finset.sum_range_succ,
        i3_post_1, i8_post_1, i13_post_1, i18_post_1, i20_post_1]
        rw[mask_post_1, i_post_1, LOW_52_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            land_pow_two_sub_one_eq_mod,
            top_mask_post_1, i1_post_1, LOW_48_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod]

        have eq0: i2.val % 2 ^ 8 = (b.val[0]).val := by
          simp_all
          scalar_tac
        have i2_eq: i2.val = b.val[0] + 2 ^ 8 * b.val[1] +
          2 ^ 16 * b.val[2] + 2 ^ 24 * b.val[3] +
          2 ^ 32 * b.val[4] + 2 ^ 40 * b.val[5] +
          2 ^ 48 * b.val[6] +2 ^ 56 * b.val[7] := by
          simp_all
          grind
        have eq1:= u8x8_to_nat_extract_byte_1 i2_eq
        have eq2:= u8x8_to_nat_extract_byte_2 i2_eq
        have eq3:= u8x8_to_nat_extract_byte_3  i2_eq
        have eq4:= u8x8_to_nat_extract_byte_4  i2_eq
        have eq5:= u8x8_to_nat_extract_byte_5  i2_eq
        have eq60:= u8x8_to_nat_extract_byte_6 (by simp : 0 < 4)  i2_eq
        have eq61:= u8x8_to_nat_extract_byte_6 (by simp : 1 < 4) i2_eq
        have eq62:= u8x8_to_nat_extract_byte_6 (by simp : 2 < 4) i2_eq
        have eq63:= u8x8_to_nat_extract_byte_6 (by simp : 3 < 4) i2_eq
        have eqi1:= powTwo_block_split_52 i2.val
        rw[eq0, eq1, eq2, eq3, eq4, eq5, eq60, eq61, eq62, eq63] at eqi1
        rw[← eqi1]
        clear eq0 eq1 eq2 eq3 eq4 eq5 eq60 eq61 eq62 eq63 eqi1

        have eq64: i7.val  % 2 = b.val[6].val >>> 4 % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 0 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I (by simp : 0 < 4) i2_eq
          simp at this
          rw[this]



        have eq65: (i7.val % 2 ^ 52)  >>> 1 % 2 = b.val[6].val >>> 5 % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 1< 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_6I (by simp : 1 < 4) i2_eq

        have eq66: (i7.val % 2 ^ 52) >>> 2 % 2 = b.val[6].val >>> 6 % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 2 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_6I (by simp : 2 < 4) i2_eq
        have eq67: (i7.val % 2 ^ 52) >>> 3 % 2 = b.val[6].val >>> 7 % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 3 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_6I (by simp : 3 < 4) i2_eq
        have eq70: (i7.val % 2 ^ 52) >>> 4 % 2 = b.val[7].val  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 4 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 0 < 8) i2_eq
        have eq71: (i7.val % 2 ^ 52) >>> 5 % 2 = b.val[7].val >>> 1  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 5 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 1 < 8) i2_eq
        have eq72: (i7.val % 2 ^ 52) >>> 6 % 2 = b.val[7].val >>> 2  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 6 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 2 < 8) i2_eq
        have eq73: (i7.val % 2 ^ 52) >>> 7 % 2 = b.val[7].val >>> 3  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 7 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 3 < 8) i2_eq
        have eq74: (i7.val % 2 ^ 52) >>> 8 % 2 = b.val[7].val >>> 4  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 8 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 4 < 8) i2_eq
        have eq75: (i7.val % 2 ^ 52) >>> 9 % 2 = b.val[7].val >>> 5  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 9 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 5 < 8) i2_eq
        have eq76: (i7.val % 2 ^ 52) >>> 10 % 2 = b.val[7].val >>> 6  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 10 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 6 < 8) i2_eq
        have eq77: (i7.val % 2 ^ 52) >>> 11 % 2 = b.val[7].val >>> 7  % 2 := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsb (i2.val) (i5.val) (by simp : 11 < 12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_7 (by simp : 7 < 8) i2_eq

        have i5_eq: i5.val = b.val[8] + 2 ^ 8 * b.val[9] +
          2 ^ 16 * b.val[10] + 2 ^ 24 * b.val[11] +
          2 ^ 32 * b.val[12] + 2 ^ 40 * b.val[13] +
          2 ^ 48 * b.val[14] +2 ^ 56 * b.val[15] := by
          simp_all
          grind


        have eq8: ((i7.val % 2 ^ 52) >>> 12) % 2 ^8  = b.val[8].val  := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsbI i2 i5 (by simp : 12 ≤  12)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_12_0 i5_eq
          simp at this
          rw[this]

        have eq9: ((i7.val % 2 ^ 52) >>> 20) % 2 ^8  = b.val[9].val  := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsbI i2 i5 (by simp : 12 ≤  20)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_12_1 i5_eq
          simp at this
          rw[this]

        have eq10: ((i7.val % 2 ^ 52) >>> 28) % 2 ^8  = b.val[10].val  := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsbI i2 i5 (by simp : 12 ≤  28)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_12_2 i5_eq
          simp at this
          rw[this]

        have eq11: ((i7.val % 2 ^ 52) >>> 36) % 2 ^8  = b.val[11].val  := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsbI i2 i5 (by simp : 12 ≤  36)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_12_3 i5_eq
          simp at this
          rw[this]

        have eq12: ((i7.val % 2 ^ 52) >>> 44) % 2 ^8  = b.val[12].val  := by
          simp[i7_post_1, i4_post_1, i6_post_1]
          have := lsb_or_leftShift_eq_lsbI i2 i5 (by simp : 12 ≤  44)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_12_4 i5_eq
          simp at this
          rw[this]

        have eqi1:= powTwo_block_split_52_remain4 i7.val
        have eq_7:= @powTwo_four_block_split 1 52 (i7.val) (by simp)
        rw[(by simp : 4 * 1 = 4), (by simp : 2 ^ 1 = 2)] at eq_7
        have :((i7.val % 2 ^ 52) >>> 4) % 2 ^ 52 = (i7.val % 2 ^ 52) >>> 4 := by
          apply Nat.mod_eq_of_lt
          rw[Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          apply lt_trans _ (by simp: 2 ^ 52 < 2 ^ 4 * 2 ^ 52)
          apply Nat.mod_lt
          simp
        have eq_8:= @powTwo_8_block_split 1 52 ((i7.val % 2 ^ 52) >>> 4) (by simp)
        rw[this, ← Nat.shiftRight_add,
        ← Nat.shiftRight_add, ← Nat.shiftRight_add, ← Nat.shiftRight_add, ← Nat.shiftRight_add,
        ← Nat.shiftRight_add, ← Nat.shiftRight_add,
         (by simp : 8 * 1 = 8), (by simp : 2 ^ 1 = 2),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp :∀ a:ℕ , a * 1 = a),
         (by simp : 4 + 1 = 5), (by simp : 4 + 2 * 1 = 6),
         (by simp : 4 + 3 * 1 = 7), (by simp : 4 + 4 * 1 = 8),
         (by simp : 4 + 5 * 1 = 9), (by simp : 4 + 6 * 1 = 10),
         (by simp : 4 + 7 * 1 = 11)
        ] at eq_8
        rw[ eq70,
        eq71, eq72, eq73, eq74, eq75, eq76, eq77] at eq_8



        have : b.val[7] % 2 ^ 52 = b.val[7] := by
          apply Nat.mod_eq_of_lt
          scalar_tac

        have eq_80:= @powTwo_8_block_split 1 52 (b.val[7]) (by simp)
        rw[this, (by simp : 2 ^ 1 = 2), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a),
        eq_8] at eq_80



        rw[eq12, eq11, eq10, eq9, eq8, ← eq_7, eq64, eq65, eq66, eq67, eq_80] at eqi1
        rw[← eqi1]
        clear eq12 eq11 eq10 eq9 eq8  eq_7 eq64 eq65
        clear eq66 eq67 eq_80 eqi1 this eq_8 i5_eq
        clear eq70 eq71 eq72 eq73 eq74 eq75 eq76 eq77 i2_eq this

        have : 4503599627370496 = 2 ^ 48 * 2^ 4 := by simp

        rw[this]

        have eq_6:  2 ^ 48 *
              ((b.val[6]).val >>> 0 % 2 + 2 * ((b.val[6]).val>>> 1 % 2) + 2 ^ 2 * ((b.val[6]).val >>> 2 % 2) +
                2 ^ 3 * ((b.val[6]).val >>> 3 % 2)) +
          2 ^ 48 * 2^ 4 *
            ((b.val[6]).val >>> 4 % 2 + 2 * ((b.val[6]).val >>> 5 % 2) + 2 ^ (2 * 1) * ((b.val[6]).val >>> 6 % 2) +
                          2 ^ (3 * 1) * ((b.val[6]).val >>> 7 % 2))
            = 2 ^ 48 *
              ((b.val[6]).val >>> 0 % 2 + 2 * ((b.val[6]).val >>> 1 % 2) + 2 ^ 2 * ((b.val[6]).val >>> 2 % 2) +
                2 ^ 3 * ((b.val[6]).val >>> 3 % 2) + 2 ^ 4 *
                ((b.val[6]).val >>> 4 % 2) + 2 ^ 5 * ((b.val[6]).val >>> 5 % 2)
                + 2 ^ (6) * ((b.val[6]).val >>> 6 % 2) +
                          2 ^ (7) * ((b.val[6]).val >>> 7 % 2)) := by
               rw[mul_assoc, ← mul_add (2 ^ 48), mul_add (2 ^ 4) ]
               simp[add_assoc]
               rw[mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc]
               simp [add_assoc]

        have : b.val[6] % 2 ^ 52 = b.val[6] := by
          apply Nat.mod_eq_of_lt
          scalar_tac

        have eq_60:= @powTwo_8_block_split 1 52 (b.val[6]) (by simp)
        rw[ this, (by simp : 2 ^ 1 = 2), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a)
        ] at eq_60
        clear this
        have : b.val[6].val >>>0  = b.val[6] := by
          scalar_tac
        rw[this, eq_60] at eq_6
        clear this
        have : 2 ^ 48 * 2 ^ 4 *
            ((b.val)[6].val >>> 4 % 2 + 2 * ((b.val)[6].val >>> 5 % 2) + 2 ^ (2 * 1) * ((b.val)[6].val >>> 6 % 2) +
                          2 ^ (3 * 1) * ((b.val)[6].val >>> 7 % 2) +
                        2 ^ 4 * ((b.val)[7].val % 2 ^ 8) +
                      2 ^ 12 * (b.val)[8].val +
                    2 ^ 20 * (b.val)[9].val +
                  2 ^ 28 * (b.val)[10].val +
                2 ^ 36 * (b.val)[11].val +
              2 ^ 44 * (b.val)[12].val) =
            2 ^ 48 * 2 ^ 4 *
            ((b.val)[6].val >>> 4 % 2 + 2 * ((b.val)[6].val >>> 5 % 2) + 2 ^ (2 * 1) * ((b.val)[6].val >>> 6 % 2) +
                          2 ^ (3 * 1) * ((b.val)[6].val >>> 7 % 2)) +
                     2 ^ 48 * 2 ^ 4 *  ( 2 ^ 4 * ((b.val)[7].val % 2 ^ 8) +
                      2 ^ 12 * (b.val)[8].val +
                    2 ^ 20 * (b.val)[9].val +
                  2 ^ 28 * (b.val)[10].val +
                2 ^ 36 * (b.val)[11].val +
              2 ^ 44 * (b.val)[12].val)  := by
              rw[← mul_add (2 ^ 48 * 2 ^ 4)]
              grind
        rw[this]
        clear this

        have :  b.val[0].val + 2 ^ 8 * b.val[1].val + 2 ^ 16 * b.val[2].val + 2 ^ 24 * b.val[3].val + 2 ^ 32 * b.val[4].val + 2 ^ 40 * b.val[5].val +
            2 ^ 48 *
              (b.val[6].val >>> 0 % 2 + 2 * (b.val[6].val >>> 1 % 2) + 2 ^ 2 * (b.val[6].val >>> 2 % 2) +
                2 ^ 3 * (b.val[6].val >>> 3 % 2)) +
          (2 ^ 48 * 2 ^ 4 *
              (b.val[6].val >>> 4 % 2 + 2 * (b.val[6].val >>> 5 % 2) + 2 ^ (2 * 1) * (b.val[6].val >>> 6 % 2) +
                2 ^ (3 * 1) * (b.val[6].val >>> 7 % 2)) +
            2 ^ 48 * 2 ^ 4 *
              (2 ^ 4 * (b.val[7].val % 2 ^ 8) + 2 ^ 12 * b.val[8].val + 2 ^ 20 * b.val[9].val + 2 ^ 28 * b.val[10].val +
                  2 ^ 36 * b.val[11].val +
                2 ^ 44 * b.val[12].val)) =
             b.val[0].val + 2 ^ 8 * b.val[1].val + 2 ^ 16 * b.val[2].val + 2 ^ 24 * b.val[3].val + 2 ^ 32 * b.val[4].val + 2 ^ 40 * b.val[5].val +
            (2 ^ 48 *
              (b.val[6].val >>> 0 % 2 + 2 * (b.val[6].val >>> 1 % 2) + 2 ^ 2 * (b.val[6].val >>> 2 % 2) +
                2 ^ 3 * (b.val[6].val >>> 3 % 2)) +
          2 ^ 48 * 2 ^ 4 *
              (b.val[6].val >>> 4 % 2 + 2 * (b.val[6].val >>> 5 % 2) + 2 ^ (2 * 1) * (b.val[6].val >>> 6 % 2) +
                2 ^ (3 * 1) * (b.val[6].val >>> 7 % 2))) +
            2 ^ 48 * 2 ^ 4 *
              (2 ^ 4 * (b.val[7].val % 2 ^ 8) + 2 ^ 12 * b.val[8].val + 2 ^ 20 * b.val[9].val + 2 ^ 28 * b.val[10].val +
                  2 ^ 36 * b.val[11].val +
                2 ^ 44 * b.val[12].val) := by grind
        rw[this]
        clear this
        have : b.val[6].val >>>0  = b.val[6] := by
          scalar_tac

        rw[this, eq_6]
        clear this eq_6 eq_60
        have : b.val[6] % 2 ^ 8 = b.val[6] := by
          apply Nat.mod_eq_of_lt
          scalar_tac
        rw[this]
        clear this
        have : b.val[7] % 2 ^ 8 = b.val[7] := by
          apply Nat.mod_eq_of_lt
          scalar_tac
        rw[this]
        clear this
        rw[mul_add, mul_add, mul_add, mul_add, mul_add,
         ← mul_assoc,  ← mul_assoc,  ← mul_assoc ,
         ← mul_assoc,  ← mul_assoc,  ← mul_assoc]

        have i5_eq: i5.val = b.val[8] + 2 ^ 8 * b.val[9] +
          2 ^ 16 * b.val[10] + 2 ^ 24 * b.val[11] +
          2 ^ 32 * b.val[12] + 2 ^ 40 * b.val[13] +
          2 ^ 48 * b.val[14] +2 ^ 56 * b.val[15] := by
          simp_all
          grind

        have eq13: i12.val  % 2^8 = b.val[13].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsb_40_24 (i5.val) (i10.val) (by simp : 0 < 17)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          apply u8x8_to_nat_extract_byte_5I  i5_eq


        have eq14: (i12.val % 2 ^ 52) >>> 8 % 2^8 = b.val[14].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsb_40_24 (i5.val) (i10.val) (by simp : 8 < 17)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :i5.val >>> 40 % 4503599627370496 =i5.val >>> 40 := by
            apply Nat.mod_eq_of_lt
            scalar_tac
          rw[this,← Nat.shiftRight_add, (by simp : 40 + 8 = 48)]
          have :=u8x8_to_nat_extract_byte_6_0  i5_eq
          simp at this
          rw[this]
        have eq15: (i12.val % 2 ^ 52) >>> 16 % 2^8 = b.val[15].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsb_40_24 (i5.val) (i10.val) (by simp : 16 < 17)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :i5.val >>> 40 % 4503599627370496 =i5.val >>> 40 := by
            apply Nat.mod_eq_of_lt
            scalar_tac
          rw[this,← Nat.shiftRight_add, (by simp : 40 + 16 = 56)]
          have :=u8x8_to_nat_extract_byte_6_1  i5_eq
          simp at this
          rw[this]

        have i10_eq: i10.val = b.val[16] + 2 ^ 8 * b.val[17] +
          2 ^ 16 * b.val[18] + 2 ^ 24 * b.val[19] +
          2 ^ 32 * b.val[20] + 2 ^ 40 * b.val[21] +
          2 ^ 48 * b.val[22] +2 ^ 56 * b.val[23] := by
          simp_all
          grind

        have eq16: (i12.val % 2 ^ 52) >>> 24 % 2^8 = b.val[16].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  24)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_24_0 i10_eq
          simp at this
          rw[this]

        have eq17: (i12.val % 2 ^ 52) >>> 32 % 2^8 = b.val[17].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  32)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_24_1 i10_eq
          simp at this
          rw[this]

        have eq18: (i12.val % 2 ^ 52) >>> 40 % 2^8 = b.val[18].val  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  40)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_24_2 i10_eq
          simp at this
          rw[this]

        have eq190: (i12.val % 2 ^ 52) >>> 48 >>> 0 % 2 = (b.val[19].val % 2^ 52) % 2  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  48)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_6_24 (by simp : 0 < 4) i10_eq
          simp at this
          rw[this]

        have eq191: (i12.val % 2 ^ 52) >>> 48 >>> 1 % 2 = (b.val[19].val % 2^ 52) >>> 1 % 2  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  48)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_6_24 (by simp : 1 < 4) i10_eq
          simp at this
          rw[this]

        have eq192: (i12.val % 2 ^ 52) >>> 48 >>> 2 % 2 = (b.val[19].val % 2^ 52) >>> 2 % 2  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  48)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_6_24 (by simp : 2 < 4) i10_eq
          simp at this
          rw[this]
        have eq193: (i12.val % 2 ^ 52) >>> 48 >>> 3 % 2 = (b.val[19].val % 2^ 52) >>> 3 % 2  := by
          simp[i12_post_1, i9_post_1, i11_post_1]
          have := lsb_or_leftShift_eq_lsbI_40_24 (i5) (i10) (by simp : 24 ≤  48)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have := u8x8_to_nat_extract_byte_6_24 (by simp : 3 < 4) i10_eq
          simp at this
          rw[this]




        have eqi1:= powTwo_block_split_52 i12.val
        rw[eq13, eq14, eq15, eq16, eq17, eq18, eq190, eq191, eq192, eq193] at eqi1
        rw[← eqi1]
        clear eq13 eq14 eq15 eq16 eq17 eq18 eq190 eq191 eq192 eq193


        have eq194: i17.val  % 2  = (b.val[19].val % 2^ 52) >>> 4 % 2  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36_2 (i10.val) (i15.val) (by simp : 0 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28 (by simp : 0 < 4) i10_eq
          simp at this
          rw[this]


        have eq195: (i17.val % 2 ^ 52) >>> 1 % 2  = (b.val[19].val % 2^ 52) >>> 5 % 2  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36_2 (i10.val) (i15.val) (by simp : 1 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28 (by simp : 1 < 4) i10_eq
          simp at this
          rw[this]

        have eq196: (i17.val % 2 ^ 52) >>> 2 % 2  = (b.val[19].val % 2^ 52) >>> 6 % 2  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36_2 (i10.val) (i15.val) (by simp : 2 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28 (by simp : 2 < 4) i10_eq
          simp at this
          rw[this]

        have eq197: (i17.val % 2 ^ 52) >>> 3 % 2  = (b.val[19].val % 2^ 52) >>> 7 % 2  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36_2 (i10.val) (i15.val) (by simp : 3 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28 (by simp : 3 < 4) i10_eq
          simp at this
          rw[this]


        have eq20: (i17.val % 2 ^ 52) >>> 4 % 2 ^ 8  = b.val[20].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36 (i10.val) (i15.val) (by simp : 4 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28_4  i10_eq
          simp at this
          rw[this]

        have eq21: (i17.val % 2 ^ 52) >>> 12 % 2 ^ 8  = b.val[21].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36 (i10.val) (i15.val) (by simp : 12 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28_12  i10_eq
          simp at this
          rw[this]

        have eq22: (i17.val % 2 ^ 52) >>> 20 % 2 ^ 8  = b.val[22].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36 (i10.val) (i15.val) (by simp : 20 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28_20  i10_eq
          simp at this
          rw[this]


        have eq23: (i17.val % 2 ^ 52) >>> 28 % 2 ^ 8  = b.val[23].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsb_28_36 (i10.val) (i15.val) (by simp : 28 < 29)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_6I_28_28  i10_eq
          simp at this
          rw[this]



        have eqi1:= powTwo_block_split_52_remain4 i17.val
        have eq_17:= @powTwo_four_block_split 1 52 (i17.val) (by simp)
        rw[(by simp : 4 * 1 = 4), (by simp : 2 ^ 1 = 2)] at eq_17

        rw[eq23, eq22, eq21, eq20, ← eq_17, eq197, eq196, eq195, eq194 ] at eqi1
        rw[← eqi1]
        clear eq23 eq22 eq21 eq20 eq_17 eq197 eq196 eq195 eq194

        have i15_eq: i15.val = (b.val[24] + 2 ^ 8 * b.val[25] +
          2 ^ 16 * b.val[26] + 2 ^ 24 * b.val[27] +
          2 ^ 32 * b.val[28] + 2 ^ 40 * b.val[29] +
          2 ^ 48 * b.val[30] +2 ^ 56 * b.val[31])  := by
          simp_all
          grind

        have eq23: (i17.val % 2 ^ 52) >>> 36 % 2 ^ 8  = b.val[24].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsbI_28_36 (i10) (i15) (by simp : 36 ≤  36)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_36_0  i15_eq
          simp at this
          rw[this]

        have eq231: (i17.val % 2 ^ 52) >>> 44 % 2 ^ 8  = b.val[25].val  := by
          simp[i17_post_1, i14_post_1, i16_post_1]
          have := lsb_or_leftShift_eq_lsbI_28_36 (i10) (i15) (by simp : 36 ≤  44)
          simp[Nat.shiftLeft_eq] at this
          simp[Nat.shiftLeft_eq]
          rw[this]
          have :=u8x8_to_nat_extract_byte_44_0  i15_eq
          simp at this
          rw[this]

        have eq24:= u8x8_to_nat_extract_byte_16_0 i15_eq
        rw[← i19_post_1] at eq24
        have eq25:= u8x8_to_nat_extract_byte_16_8 i15_eq
        rw[← i19_post_1] at eq25
        have eq26:= u8x8_to_nat_extract_byte_16_16 i15_eq
        rw[← i19_post_1] at eq26
        have eq27:= u8x8_to_nat_extract_byte_16_24 i15_eq
        rw[← i19_post_1] at eq27
        have eq28:= u8x8_to_nat_extract_byte_16_32 i15_eq
        rw[← i19_post_1] at eq28
        have eq29:= u8x8_to_nat_extract_byte_16_40 i15_eq
        rw[← i19_post_1] at eq29
        have : i19.val % 2 ^ 52 % 2 ^ 8 = i19 % 2 ^ 8 := by grind
        rw[this] at eq24

        have eqi1:= powTwo_six_block_split i19.val (by simp : 6 * 8 < 52)
        rw[eq24, eq25, eq26, eq27, eq28, eq29, (by simp : 6 * 8 = 48)] at eqi1
        rw[← eqi1]
        have eq_80:= @powTwo_8_block_split 1 52 (b.val[19]) (by simp)
        rw[ (by simp : 2 ^ 1 = 2), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a), (by simp :∀ a:ℕ , a * 1 = a),
        (by simp :∀ a:ℕ , a * 1 = a),(by simp :∀ a:ℕ , a * 1 = a)
        ] at eq_80

        rw[eq23, eq231]



        simp[U8x32_as_Nat, Finset.sum_range_succ]
        simp[add_assoc, mul_add, ← mul_assoc]
        simp[← add_assoc]
        have : b.val[19] % 2 ^ 8 = b.val[19] := by
          apply Nat.mod_eq_of_lt
          scalar_tac
        rw[this] at eq_80
        nth_rw 9 [← eq_80]
        simp[mul_add, ← mul_assoc, add_assoc]
    · intro i hi
      interval_cases i
      · simp[i3_post_1]
        rw[mask_post_1, i_post_1, LOW_52_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            ]
        simp
        apply Nat.mod_lt
        simp
      · simp[i8_post_1]
        rw[mask_post_1, i_post_1, LOW_52_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            ]
        simp
        apply Nat.mod_lt
        simp
      · simp[i13_post_1]
        rw[mask_post_1, i_post_1, LOW_52_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            ]
        simp
        apply Nat.mod_lt
        simp
      · simp[i18_post_1]
        rw[mask_post_1, i_post_1, LOW_52_BIT_MASK_spec,
            land_pow_two_sub_one_eq_mod,
            ]
        simp
        apply Nat.mod_lt
        simp
      · simp[i20_post_1]
        rw[top_mask_post_1, i1_post_1, LOW_48_BIT_MASK_spec,
        land_pow_two_sub_one_eq_mod,
            ]
        apply lt_trans _ (by simp : 2 ^ 48 < 4503599627370496)
        apply Nat.mod_lt
        simp

























































































      --simp_all[U8x32_as_Nat, Finset.sum_range_succ]
















end curve25519_dalek.backend.serial.u64.scalar.Scalar52
