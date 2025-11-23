/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics


/-! # to_bytes

Specification and proof for `FieldElement51::to_bytes`.

Much of the proof and aux lemmas contributed by Son Ho.

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo 2^255-19 and encodes the result as bytes.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

set_option linter.style.setOption false
set_option linter.style.cdot false
set_option maxHeartbeats 1000000000000

open Aeneas.Std Result

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  simp only [UScalar.cast, UScalarTy.U64_numBits_eq, UScalarTy.U8_numBits_eq,
    Aeneas.Bvify.U64.UScalar_bv, BitVec.truncate_eq_setWidth]
  simp only [UScalar.val]
  simp only [UScalarTy.U8_numBits_eq, BitVec.toNat_setWidth, UScalar.bv_toNat,
    UScalarTy.U64_numBits_eq, Aeneas.Bvify.U64.UScalar_bv]

-- This is specific to the problem below
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  bvify 64 at *
  bv_decide


-- TODO: move to standard library
attribute [simp_scalar_simps] BitVec.toNat_shiftLeft


-- We also need something like this
theorem recompose_decomposed_limb_split (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val
  := by
  bvify 64 at *
  /- Small trick when bvify doesn't work: we can prove the property we
     want about bit-vectors, then convert it back to natural numbers with
     `natify` and `simp_scalar`. In particular, `simp_scalar` is good at simplifying
     things like `x % 2 ^ 32` when `x < 2^32`, etc. -/
  have : BitVec.ofNat 64 (limb.val <<< 4) = limb.bv <<< 4 := by
    natify
    simp_scalar
  simp [this]
  bv_decide





-- This is specific to the problem below

@[progress]
theorem decompose_or_limbs (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) +
  ((limb1.val <<< 4) % 2 ^ 8) := by
  bvify 64 at *
  -- The idea is to do something similar to the proof above
  have : BitVec.ofNat 64 (((↑limb0 >>> 48 ||| ↑limb1 <<< 4 % U64.size) % 256)) = ((limb0.bv >>> 48 ||| limb1.bv <<< 4 % U64.size) % 256) := by
    natify
    simp_scalar
    progress
    sorry
  sorry




theorem Array.val_getElem!_eq'U8 (bs : Array U8 5#usize) (i : Nat) (h : i < bs.length) :
    (bs.val)[i]! = bs[i] := by
  simpa [Subtype.val] using getElem!_pos bs.val i _


@[ext] lemma U8.ext {a b : U8} (h : a.bv = b.bv) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[simp] lemma zero_bv : U8.bv 0#u8 = 0 := rfl







lemma dvd_iff_exists_eq_mul_right {n a : ℤ} :
    n ∣ a ↔ ∃ k, a = k * n := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩      -- hk : a = n * k
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk

theorem land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  . simp
    scalar_tac
  . simp

lemma mod19_eq_51: 19 ≡ 2^(51* 5) [MOD p]:= by
   simp[Nat.modEq_iff_dvd, p]


theorem nat_lt_two_iff_eq_zero_or_one (b : Nat) : b < 2 ↔ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    cases b with
    | zero => left; rfl
    | succ b' =>
      cases b' with
      | zero => right; rfl
      | succ b'' =>
        -- succ (succ b'') ≥ 2, contradicts b < 2
        have ge2 : 2 ≤ Nat.succ (Nat.succ b'') := by
          apply Nat.succ_le_succ
          apply Nat.succ_le_succ
          apply Nat.zero_le
        exact absurd h (not_lt_of_ge ge2)
  · intro h
    cases h with
    | inl h0 => rw[h0]; simp
    | inr h1 => rw[h1]; simp

theorem div_pow51_eq_zero_iff_lt (a : Nat) : a / 2 ^ 51 = 0 ↔ a < 2 ^ 51 := by
  have h : 2 ^ 51 ≠ 0 := by decide
  rw [Nat.div_eq_zero_iff]
  simp


theorem mul_le_mul_left' {x y z : Nat} (_ : 0 < z) : x ≤  y → z * x ≤  z * y := by
  intro hcase
  apply Nat.mul_le_mul_left z
  exact hcase

theorem mul_lt_mul_left_of_pos {a b c : Nat} (hc : 0 < c) (h : a < b) : c * a < c * b := by
  exact (Nat.mul_lt_mul_left hc).mpr h


theorem mod_51_256 : 2^(51) ≡ 0 [MOD 256] := by
  simp[Nat.modEq_iff_dvd]

theorem mod_102_256 : 2^(51 * 2) ≡ 0 [MOD 256] := by
  simp[Nat.modEq_iff_dvd]

theorem mod_153_256 : 2^(51 * 3) ≡ 0 [MOD 256] := by
  simp[Nat.modEq_iff_dvd]

theorem mod_204_256 : 2^(51 * 4) ≡ 0 [MOD 256] := by
  simp[Nat.modEq_iff_dvd]

theorem mod_255_256 : 2^(51 * 5) ≡ 0 [MOD 256] := by
  simp[Nat.modEq_iff_dvd]








/-! ## Spec for `to_bytes` -/


/-- Byte-by-byte specification for `to_bytes` -/
theorem to_bytes_spec' (limbs : Array U64 5#usize) :
    ∃ result, to_bytes limbs = ok result ∧
    ∀ (i : Fin 32), result.val[i.val].val = match i.val with
      | 0  => limbs.val[0].val >>> 0 % 2^8
      | 1  => limbs.val[0].val >>> 8 % 2^8
      | 2  => limbs.val[0].val >>> 16 % 2^8
      | 3  => limbs.val[0].val >>> 24 % 2^8
      | 4  => limbs.val[0].val >>> 32 % 2^8
      | 5  => limbs.val[0].val >>> 40 % 2^8
      | 6  => (limbs.val[0].val >>> 48 ||| limbs.val[1].val <<< 4) % 2^8
      | 7  => limbs.val[1].val >>> 4 % 2^8
      | 8  => limbs.val[1].val >>> 12 % 2^8
      | 9  => limbs.val[1].val >>> 20 % 2^8
      | 10 => limbs.val[1].val >>> 28 % 2^8
      | 11 => limbs.val[1].val >>> 36 % 2^8
      | 12 => limbs.val[1].val >>> 44 % 2^8
      | 13 => limbs.val[2].val >>> 0 % 2^8
      | 14 => limbs.val[2].val >>> 8 % 2^8
      | 15 => limbs.val[2].val >>> 16 % 2^8
      | 16 => limbs.val[2].val >>> 24 % 2^8
      | 17 => limbs.val[2].val >>> 32 % 2^8
      | 18 => limbs.val[2].val >>> 40 % 2^8
      | 19 => (limbs.val[2].val >>> 48 ||| limbs.val[3].val <<< 4) % 2^8
      | 20 => limbs.val[3].val >>> 4 % 2^8
      | 21 => limbs.val[3].val >>> 12 % 2^8
      | 22 => limbs.val[3].val >>> 20 % 2^8
      | 23 => limbs.val[3].val >>> 28 % 2^8
      | 24 => limbs.val[3].val >>> 36 % 2^8
      | 25 => limbs.val[3].val >>> 44 % 2^8
      | 26 => limbs.val[4].val >>> 0 % 2^8
      | 27 => limbs.val[4].val >>> 8 % 2^8
      | 28 => limbs.val[4].val >>> 16 % 2^8
      | 29 => limbs.val[4].val >>> 24 % 2^8
      | 30 => limbs.val[4].val >>> 32 % 2^8
      | 31 => limbs.val[4].val >>> 40 % 2^8
      | _  => 0
    := by
  unfold to_bytes
  progress
  progress
  rename_i z h_bounds_z y  x hx
  have h_bounds_z0:= h_bounds_z 0 (by simp)
  have h_bounds_z1:= h_bounds_z 1 (by simp)
  have h_bounds_z2:= h_bounds_z 2 (by simp)
  have h_bounds_z3:= h_bounds_z 3 (by simp)
  have h_bounds_z4:= h_bounds_z 4 (by simp)
  set con:= 2251799813840877 with hcon
  progress as ⟨a, ha⟩
  progress as ⟨b, hb, hb_bv⟩
  progress as ⟨z1, hz1⟩
  progress as ⟨a1, ha1⟩
  progress as ⟨b1, hb1, hb1_bv⟩
  progress as ⟨z2, hz2⟩
  progress as ⟨a2, ha2⟩
  progress as ⟨b2, hb2, hb2_bv⟩
  progress as ⟨z3, hz3⟩
  progress as ⟨a3, ha3⟩
  progress as ⟨b3, hb3, hb3_bv⟩
  progress as ⟨z4, hz4⟩
  progress as ⟨a4, ha4⟩
  progress as ⟨b4, hb4, hb4_bv⟩
  progress as ⟨c4, hc4⟩
  progress as ⟨d4, hd4⟩
  have hlen_z0 : 0#usize < z.length := by scalar_tac
  have hlen_z1 : 1#usize < z.length := by scalar_tac
  have hlen_z2 : 2#usize < z.length := by scalar_tac
  have hlen_z3 : 3#usize < z.length := by scalar_tac
  have hlen_z4 : 4#usize < z.length := by scalar_tac
  obtain ⟨zd, hzd_ok, hzd_val⟩ := Array.update_spec z 0#usize d4 hlen_z0
  simp only [hzd_ok, bind_tc_ok]
  progress as ⟨i12, hi12, hi12_bv⟩
  progress as ⟨a5, ha5, ha5_le⟩
  progress as ⟨zd0, hzd0⟩
  progress as ⟨azd0, hazd0, azd0_bv⟩
  progress as ⟨zd1, hzd1⟩
  have a_le:=Nat.shiftRight_le a.val 51
  have a1_le:=Nat.shiftRight_le a1.val 51
  have a2_le:=Nat.shiftRight_le a2.val 51
  have a3_le:=Nat.shiftRight_le a3.val 51
  have a4_le:=Nat.shiftRight_le a4.val 51

  have : zd1.val + azd0.val ≤ U64.max := by
    simp[hzd1, hzd_val]
    have : azd0.val ≤ 2 ^ 64 - 1 - con := by
     rw[hazd0, Nat.shiftRight_eq_div_pow]
     apply Nat.div_le_of_le_mul
     simp[hzd0, hzd_val, hd4, hx, hc4]
     have :b4.val ≤ (2 ^ 51 * (2 ^ 64 -1 - con) - con)/ 19 := by
       rw[hb4, Nat.shiftRight_eq_div_pow]
       apply Nat.div_le_of_le_mul
       rw[ha4, hz4]
       have : b3.val ≤ (2 ^ 51 * (2 ^ 64 - 1 - con) - con)/ 19- con := by
        rw[hb3, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[ha3, hz3]
        have : b2.val ≤ 2 ^ 51 * ((2 ^ 51 * (2 ^ 64 -1 - con) - con) / 19 - con)-  con := by
         rw[hb2, Nat.shiftRight_eq_div_pow]
         apply Nat.div_le_of_le_mul
         rw[ha2]
         have : b1.val ≤ 2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 64 -1 - con) - con) / 19 - con) - con)- con := by
           rw[hb1, Nat.shiftRight_eq_div_pow]
           apply Nat.div_le_of_le_mul
           rw[ha1]
           have :b.val ≤  2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 64 -1 - con) - con) / 19 - con) - con) - con) - con := by
             rw[hb, Nat.shiftRight_eq_div_pow]
             apply Nat.div_le_of_le_mul
             rw[ha, hx]
             scalar_tac
           have :=Nat.add_le_add h_bounds_z1 this
           scalar_tac
         have :=Nat.add_le_add h_bounds_z2 this
         scalar_tac
        have :=Nat.add_le_add h_bounds_z3 this
        scalar_tac
       have :=Nat.add_le_add h_bounds_z4 this
       scalar_tac
     have le_19: 19≤ 19 :=by simp
     have := Nat.mul_le_mul le_19 this
     have :=Nat.add_le_add h_bounds_z0 this
     simp at this
     apply le_trans this
     simp[hcon]
    have :=Nat.add_le_add h_bounds_z1 this
    simp at this
    apply le_trans this
    simp[hcon, U64.max, U64.numBits ]
  progress as ⟨azd1, hazd1⟩
  have hlen_zd1 : 1#usize < zd.length := by scalar_tac
  obtain ⟨zdu, hzdu_ok, hzdu_val⟩ := Array.update_spec zd 1#usize azd1 hlen_zd1
  simp only [hzdu_ok, bind_tc_ok]
  progress as ⟨zdu0, hzdu0⟩
  progress as ⟨i18, hi18, hi18_bv⟩
  have hlen_zd0 : 0#usize < zd.length := by scalar_tac
  obtain ⟨zdu20, hzdu20_ok, hzdu20_valz⟩ := Array.update_spec zd 0#usize i18 hlen_zd0
  have hlen_zdu0 : 0#usize < zdu.length := by scalar_tac
  obtain ⟨zdu180, hzdu180_ok, hzdu180_val⟩ := Array.update_spec zdu 0#usize i18 hlen_zdu0
  simp only [hzdu180_ok, bind_tc_ok]
  progress as ⟨zdu1, hzdu1⟩
  progress as ⟨zdu2, hzdu2, hzdu2_bv⟩
  progress as ⟨z80, hz80⟩
  have sum1: z80.val + zdu2.val ≤ U64.max := by
    simp[hz80, hzdu180_val, hzdu_val, hzd_val]
    have : zdu2.val ≤ 2 ^ 64 - 1 -con := by
      rw[hzdu2, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[hzdu1, hzdu180_val, hzdu_val, hazd1, hzd1, hzd_val]
      have :azd0 ≤ 2 ^ 51 *(2 ^ 64 - 1 -con) - con := by
        rw[hazd0, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        simp[hzd0, hzd_val, hd4, hx, hc4]
        have : b4.val ≤ (2 ^ 51 * (2 ^ 51 *(2 ^ 64 - 1 -con) - con)-con)/19 := by
          rw[hb4, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          rw[ha4, hz4]
          have : b3.val ≤ (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19))-con := by
            rw[hb3, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[ha3, hz3]
            have : b2.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con  := by
              rw[hb2, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[ha2]
              have : b1.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con) -con := by
                rw[hb1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[ha1]
                have :b.val ≤  2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con) - con) -con := by
                  rw[hb, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[ha, hx]
                  scalar_tac
                have :=Nat.add_le_add h_bounds_z1 this
                scalar_tac
              have :=Nat.add_le_add h_bounds_z2 this
              scalar_tac
            have :=Nat.add_le_add h_bounds_z3 this
            scalar_tac
          have :=Nat.add_le_add h_bounds_z4 this
          scalar_tac
        have le_19: 19≤ 19 :=by simp
        have := Nat.mul_le_mul le_19 this
        have :=Nat.add_le_add h_bounds_z0 this
        simp at this
        apply le_trans this
        simp[hcon]
      have :=Nat.add_le_add h_bounds_z1 this
      scalar_tac
    have :=Nat.add_le_add h_bounds_z2 this
    simp at this
    apply le_trans this
    simp[hcon, U64.max, U64.numBits ]
  progress as ⟨zd80, hzd80⟩
  have hlen_zdu180 : 2#usize < zdu180.length := by scalar_tac
  obtain ⟨a11, ha11_ok, ha11_val⟩ := Array.update_spec zdu180 2#usize zd80 hlen_zdu180
  simp only [ha11_ok, bind_tc_ok]








  progress as ⟨a12, ha12⟩
  progress as ⟨a13, ha13, ha13_bv⟩
  have hlen_a11 : 1#usize < a11.length := by scalar_tac
  obtain ⟨a21, ha21_ok, ha21_val⟩ := Array.update_spec a11 1#usize a13 hlen_a11
  simp only [ha21_ok, bind_tc_ok]
  progress as ⟨a22, ha22⟩
  progress as ⟨a23, ha23, ha23_bv⟩
  progress as ⟨a24, ha24⟩
  have sum2: a24.val + a23.val ≤ U64.max := by
    simp[ha24, ha21_val, ha11_val, hzdu180_val, hzdu_val, hzd_val]
    have : a23.val ≤  2 ^ 64 -1 -con := by
     rw[ha23, Nat.shiftRight_eq_div_pow]
     apply Nat.div_le_of_le_mul
     simp[ha22, ha21_val,ha11_val, hzd80, hz80, hzdu180_val, hzdu_val, hzd_val]
     have : zdu2.val ≤  2 ^ 51 * (2 ^ 64 -1 -con)-con := by
       rw[hzdu2, Nat.shiftRight_eq_div_pow]
       apply Nat.div_le_of_le_mul
       simp[hzdu1, hzdu180_val, hzdu_val, hazd1, hzd1, hzd_val]
       have :azd0.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 64 -1 -con)-con) -con := by
         rw[hazd0, Nat.shiftRight_eq_div_pow]
         apply Nat.div_le_of_le_mul
         simp[hzd0, hzd_val, hd4, hx, hc4]
         have : b4.val ≤ (2 ^ 51 * (2 ^ 51 *(2 ^ 64 - 1 -con) - con)-con)/19 := by
          rw[hb4, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          rw[ha4, hz4]
          have : b3.val ≤ (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19))-con := by
            rw[hb3, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[ha3, hz3]
            have : b2.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con  := by
              rw[hb2, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[ha2]
              have : b1.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con) -con := by
                rw[hb1, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[ha1]
                have :b.val ≤  2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con) - con) - con) / 19) - con) - con) - con) - con) -con := by
                  rw[hb, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[ha, hx]

                  scalar_tac
                have :=Nat.add_le_add h_bounds_z1 this
                scalar_tac
              have :=Nat.add_le_add h_bounds_z2 this
              scalar_tac
            have :=Nat.add_le_add h_bounds_z3 this
            scalar_tac
          have :=Nat.add_le_add h_bounds_z4 this
          scalar_tac
         have le_19: 19≤ 19 :=by simp
         have := Nat.mul_le_mul le_19 this
         have :=Nat.add_le_add h_bounds_z0 this
         simp at this
         apply le_trans this
         simp[hcon]
       have :=Nat.add_le_add h_bounds_z1 this
       scalar_tac
     have :=Nat.add_le_add h_bounds_z2 this
     scalar_tac
    have :=Nat.add_le_add h_bounds_z3 this
    simp at this
    apply le_trans this
    simp[hcon, U64.max, U64.numBits ]
  progress as ⟨a31, ha31⟩
  have hlen_a21 : 3#usize < a21.length := by scalar_tac
  obtain ⟨a32, ha32_ok, ha32_val⟩ := Array.update_spec a21 3#usize a31 hlen_a21
  simp only [ha32_ok, bind_tc_ok]
  progress as ⟨a33, ha33⟩
  progress as ⟨a34, ha34, ha34_bv⟩
  have hlen_a32 : 2#usize < a32.length := by scalar_tac
  obtain ⟨a41, ha41_ok, ha41_val⟩ := Array.update_spec a32 2#usize a34 hlen_a32
  simp only [ha41_ok, bind_tc_ok]
  progress as ⟨a42, ha42⟩
  progress as ⟨a44, ha44, ha44_bv⟩
  progress as ⟨a45, ha45⟩
  have sum3: a44.val + a45.val ≤ U64.max := by
    simp[ha44, ha45, ha41_val, ha32_val, ha21_val, ha11_val, hzdu180_val, hzdu_val, hzd_val]
    have : a42.val >>> 51 ≤ 2^64 -1- con := by
      rw[Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      simp[ha42, ha41_val, ha32_val, ha31, ha24, ha21_val, ha11_val, hzdu180_val, hzdu_val, hzd_val]
      have : a23.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con := by
        rw[ha23, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        simp[ha22, ha21_val, ha11_val, hzd80, hz80, hzdu180_val, hzdu_val, hzd_val]
        have : zdu2.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con := by
          rw[hzdu2, Nat.shiftRight_eq_div_pow]
          apply Nat.div_le_of_le_mul
          simp[hzdu1, hzdu180_val, hzdu_val, hazd1, hzd1, hzd_val]
          have : azd0.val ≤ 2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) -con := by
            rw[hazd0, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            simp[hzd0, hzd_val, hd4, hx, hc4]
            have : b4.val ≤ ((2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) -con)-con)/19 := by
              rw[hb4, Nat.shiftRight_eq_div_pow]
              apply Nat.div_le_of_le_mul
              rw[ha4, hz4]
              have : b3.val ≤ (2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) - con - con) / 19)) - con := by
                rw[hb3, Nat.shiftRight_eq_div_pow]
                apply Nat.div_le_of_le_mul
                rw[ha3, hz3]
                have : b2.val ≤ 2 ^ 51 * ((2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) - con - con) / 19)) - con) - con  := by
                  rw[hb2, Nat.shiftRight_eq_div_pow]
                  apply Nat.div_le_of_le_mul
                  rw[ha2]
                  have : b1.val ≤ 2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) - con - con) / 19)) - con) - con) -con := by
                    rw[hb1, Nat.shiftRight_eq_div_pow]
                    apply Nat.div_le_of_le_mul
                    rw[ha1]
                    have :b.val ≤  2 ^ 51 * (2 ^ 51 * (2 ^ 51 * ((2 ^ 51 * ((2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 51 * (2 ^ 64 - 1 - con)) - con) - con) - con - con) / 19)) - con) - con) -con) -con := by
                      rw[hb, Nat.shiftRight_eq_div_pow]
                      apply Nat.div_le_of_le_mul
                      rw[ha, hx]
                      scalar_tac
                    have :=Nat.add_le_add h_bounds_z1 this
                    scalar_tac
                  have :=Nat.add_le_add h_bounds_z2 this
                  scalar_tac
                have :=Nat.add_le_add h_bounds_z3 this
                scalar_tac
              have :=Nat.add_le_add h_bounds_z4 this
              scalar_tac
            have le_19: 19≤ 19 :=by simp
            have := Nat.mul_le_mul le_19 this
            have :=Nat.add_le_add h_bounds_z0 this
            simp at this
            apply le_trans this
            simp[hcon]
          have :=Nat.add_le_add h_bounds_z1 this
          scalar_tac
        have :=Nat.add_le_add h_bounds_z2 this
        scalar_tac
      have :=Nat.add_le_add h_bounds_z3 this
      scalar_tac
    have :=Nat.add_le_add this h_bounds_z4
    simp at this
    apply le_trans this
    simp[hcon, U64.max, U64.numBits ]
  progress as ⟨a51, ha51⟩
  have hlen_a41 : 4#usize < a41.length := by scalar_tac
  obtain ⟨a52, ha52_ok, ha52_val⟩ := Array.update_spec a41 4#usize a51 hlen_a41
  simp only [ha52_ok, bind_tc_ok]
  progress as ⟨a53, ha53⟩
  progress as ⟨a54, ha54, ha54_bv⟩
  progress as ⟨a55, ha55⟩
  progress as ⟨a56, ha56⟩
  progress as ⟨a57, ha57, ha57_bv⟩
  progress as ⟨a58, ha58⟩
  progress as ⟨a59, ha59⟩
  progress as ⟨a60, ha60⟩
  set zero:= Array.repeat 32#usize 0#u8 with hzero
  progress as ⟨a61, ha61⟩
  progress as ⟨a62, ha62, ha62_bv⟩
  progress as ⟨a63, ha63⟩
  progress as ⟨a64, ha64⟩
  progress as ⟨a65, ha65, ha65_bv⟩
  progress as ⟨a66, ha66⟩
  progress as ⟨a67, ha67⟩
  progress as ⟨a68, ha68, ha68_bv⟩
  progress as ⟨a69, ha69⟩
  progress as ⟨a70, ha70⟩
  progress as ⟨a71, ha71, ha71_bv⟩
  progress as ⟨a72, ha72⟩
  progress as ⟨a73, ha73⟩
  progress as ⟨a74, ha74, ha74_bv⟩
  progress as ⟨a75, ha77⟩
  progress as ⟨a76, ha76⟩
  progress as ⟨a77, ha77, ha77_bv⟩
  progress as ⟨a78, ha78⟩
  progress as ⟨a79, ha79, ha79_bv⟩
  progress as ⟨a80, ha80, ha80_bv⟩
  progress as ⟨a81, ha81⟩
  progress as ⟨a82, ha82⟩
  progress as ⟨a83, ha83, ha83_bv⟩
  progress as ⟨a84, ha84⟩
  progress as ⟨a85, ha85⟩
  progress as ⟨a86, ha86, ha86_bv⟩
  have i12_eq: i12.val= 2^51:= by
    simp[hi12, Nat.shiftLeft_eq, U64.size, U64.numBits]






  have b_lt: b.val < 2 := by
    rw[hb, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw[ha, hx]
    have le_19: 19≤ 19 :=by simp
    have h:= Nat.add_le_add  h_bounds_z0 le_19
    have :con + 19 < 2 ^ 51 *2 := by
      simp[hcon]
    have :=lt_of_le_of_lt h this
    simp at this
    simp[this]

  have b1_lt : b1.val < 2 := by
    rw[hb1, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw[ha1]
    have h:= Nat.add_le_add  h_bounds_z1 (le_of_lt b_lt)
    have :con + 2 < 2 ^ 51 *2 := by
      simp[hcon]
    have :=lt_of_le_of_lt h this
    simp at this
    simp[hz1,this]

  have b2_lt : b2.val < 2 := by
    rw[hb2, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw[ha2]
    have h:= Nat.add_le_add  h_bounds_z2 (le_of_lt b1_lt)
    have :con + 2 < 2 ^ 51 *2 := by
      simp[hcon]
    have :=lt_of_le_of_lt h this
    simp at this
    simp[hz2,this]
  have b3_lt : b3.val < 2 := by
    rw[hb3, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw[ha3, hz3]
    have h:= Nat.add_le_add  h_bounds_z3 (le_of_lt b2_lt)
    have :con + 2 < 2 ^ 51 *2 := by
      simp[hcon]
    have :=lt_of_le_of_lt h this
    simp at this
    simp[this]
  have b4_lt : b4.val < 2 := by
    rw[hb4, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    rw[ha4, hz4]
    have h:= Nat.add_le_add  h_bounds_z4 (le_of_lt b3_lt)
    have :con + 2 < 2 ^ 51 *2 := by
      simp[hcon]
    have :=lt_of_le_of_lt h this
    simp at this
    simp[this]


  have Z_le_2p: Field51_as_Nat z < 2 * p := by
    have := lt_or_ge (Field51_as_Nat z)  (2*p)
    rw[or_comm] at this
    rcases  this with hcase2 | hcase2
    . unfold Field51_as_Nat at hcase2
      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase2
      have : 0 < 2 ^ (51 * 4) := by norm_num
      have mz4:= mul_le_mul_left'  this h_bounds_z4
      have : 0 < 2 ^ (51 * 3) := by norm_num
      have mz3:= mul_le_mul_left'  this h_bounds_z3
      have : 0 < 2 ^ (51 * 2) := by norm_num
      have mz2:= mul_le_mul_left'  this h_bounds_z2
      have : 0 < 2 ^ (51 * 1) := by norm_num
      have mz1:= mul_le_mul_left'  this h_bounds_z1
      have := Nat.add_le_add  mz3 mz4
      have := Nat.add_le_add  mz2 this
      have := Nat.add_le_add  mz1 this
      have := Nat.add_le_add  h_bounds_z0 this
      simp at this
      rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at this
      have := le_trans hcase2 this
      simp[p, hcon] at this
    . exact hcase2


  set remain:= (Field51_as_Nat z) % p with hremain
  have quote: b4.val = Field51_as_Nat z / p := by
    have := lt_or_ge (Field51_as_Nat z)  (2*p)
    rw[or_comm] at this
    rcases  this with hcase2 | hcase2
    . unfold Field51_as_Nat at hcase2
      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase2
      have : 0 < 2 ^ (51 * 4) := by norm_num
      have mz4:= mul_le_mul_left'  this h_bounds_z4
      have : 0 < 2 ^ (51 * 3) := by norm_num
      have mz3:= mul_le_mul_left'  this h_bounds_z3
      have : 0 < 2 ^ (51 * 2) := by norm_num
      have mz2:= mul_le_mul_left'  this h_bounds_z2
      have : 0 < 2 ^ (51 * 1) := by norm_num
      have mz1:= mul_le_mul_left'  this h_bounds_z1
      have := Nat.add_le_add  mz3 mz4
      have := Nat.add_le_add  mz2 this
      have := Nat.add_le_add  mz1 this
      have := Nat.add_le_add  h_bounds_z0 this
      simp at this
      rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at this
      have := le_trans hcase2 this
      simp[p, hcon] at this
    · rcases  lt_or_ge (Field51_as_Nat z)  (p) with hcase | hcase
      . rw[Nat.div_eq_of_lt hcase]
        rw[hb4, Nat.shiftRight_eq_div_pow]
        apply Nat.div_eq_of_lt
        rw[ha4]
        rw[nat_lt_two_iff_eq_zero_or_one] at b3_lt
        have :=(lt_or_ge z4.val  (2 ^ 51))
        rw[or_comm] at this
        rcases  this with hcase_a4 | hcase_a4
        . unfold Field51_as_Nat at hcase
          rw[Finset.sum_range_succ, Finset.sum_range_succ,
              Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hcase
          have : 0 < 2 ^ (51 * 4) := by norm_num
          have :=mul_le_mul_left'  this hcase_a4
          have :=Nat.add_le_add_left  this  (2 ^ (51 * 0) * z.val[0]! + 2 ^ (51 * 1) * z.val[1]! + 2 ^ (51 * 2) * z.val[2]! + 2 ^ (51 * 3) * z.val[3]!)
          have :=lt_of_le_of_lt (Nat.le_add_left _ _) this
          simp[hz4] at this
          simp at hcase
          have :=lt_trans this hcase
          simp[p] at this
        . simp at hcase_a4
          rcases b3_lt with hb3_zero | hb3_one
          · rw[hb3_zero]
            simp
            exact hcase_a4
          · rw[hb3_one]
            rcases  lt_or_ge z4.val  (2 ^ 51-1) with hcase_a4_lt | hcase_a4_lt
            . simp at hcase_a4_lt
              exact Nat.succ_lt_succ hcase_a4_lt
            . have hz4_le : z4.val ≤ 2 ^ 51 - 1 := by
                apply Nat.lt_succ_iff.1
                exact hcase_a4

              have h_eq : 2 ^ 51 - 1 = z4.val := Nat.le_antisymm hcase_a4_lt hz4_le
              have :=(lt_or_ge z3.val  (2 ^ 51))
              rw[or_comm] at this
              rcases  this with hcase_a3 | hcase_a3
              . have : 0 < 2 ^ (51 * 3) := by norm_num
                have := mul_le_mul_left'  this hcase_a3
                have := Nat.add_le_add_right this (2 ^ (51 * 4) *z4.val)
                have a_this:= Nat.add_le_add_left this (2 ^ (51 * 0) * z.val[0]! + 2 ^ (51 * 1) * z.val[1]! + 2 ^ (51 * 2) * z.val[2]!)
                rw[← add_assoc, ← add_assoc] at a_this
                have := Nat.zero_le (2 ^ (51 * 0) * z.val[0]! + 2 ^ (51 * 1) * z.val[1]! + 2 ^ (51 * 2) * z.val[2]!)
                have := Nat.add_le_add_right this (2 ^ (51 * 3) * 2 ^ 51 + 2 ^ (51 * 4) * z4.val)
                rw[← add_assoc, ← add_assoc] at this
                have := le_trans this a_this
                have :0 + 2 ^ (51 * 3) * 2 ^ 51 + 2 ^ (51 * 4) * z4.val ≤ Field51_as_Nat z := by
                  unfold Field51_as_Nat
                  simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,  hz4]
                  simp[hz3] at this
                  exact this
                have := lt_of_le_of_lt this hcase
                simp[p, ← h_eq] at this
              . rcases  lt_or_ge z3.val  (2 ^ 51-1) with hcase_a3_lt | hcase_a3_lt
                . rw[hb3, ha3] at hb3_one
                  have : z3.val +b2.val < 2 ^ 51  := by
                    rw[nat_lt_two_iff_eq_zero_or_one b2.val] at b2_lt
                    rcases b2_lt with hb2_zero | hb2_one
                    · simp[hb2_zero ]
                      apply Nat.lt_trans hcase_a3_lt
                      simp
                    · simp[hb2_one ]
                      apply Nat.lt_of_le_of_lt hcase_a3_lt
                      simp
                  have := Nat.shiftRight_eq_zero (z3.val + b2.val) 51 this
                  simp[this] at hb3_one
                . have hz3_le : z3.val ≤ 2 ^ 51 - 1 := by
                    apply Nat.lt_succ_iff.1
                    exact hcase_a3
                  have h_eq3 : 2 ^ 51 - 1 = z3.val := Nat.le_antisymm hcase_a3_lt hz3_le
                  have :=(lt_or_ge z2.val  (2 ^ 51))
                  rw[or_comm] at this
                  rcases  this with hcase_a2 | hcase_a2
                  . have : 0 < 2 ^ (51 * 2) := by norm_num
                    have := mul_le_mul_left'  this hcase_a2
                    have := Nat.add_le_add_right this (2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                    have a_this:= Nat.add_le_add_left this (2 ^ (51 * 0) * z.val[0]! + 2 ^ (51 * 1) * z.val[1]! )
                    rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at a_this
                    have := Nat.zero_le (2 ^ (51 * 0) * z.val[0]! + 2 ^ (51 * 1) * z.val[1]!)
                    have := Nat.add_le_add_right this (2 ^ (51 * 2) * 2 ^ 51 + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                    rw[← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at this
                    have := le_trans this a_this
                    have :0 + 2 ^ (51 * 2) * 2 ^ 51 + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val ≤ Field51_as_Nat z := by
                      unfold Field51_as_Nat
                      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hz3, hz4]
                      simp[hz3, hz4, hz2] at this
                      exact this
                    have := lt_of_le_of_lt this hcase
                    simp[p, ← h_eq, ← h_eq3] at this
                  . rcases  lt_or_ge z2.val  (2 ^ 51-1) with hcase_a2_lt | hcase_a2_lt
                    . have : z2.val +b1.val < 2 ^ 51  := by
                        rw[nat_lt_two_iff_eq_zero_or_one b1.val] at b1_lt
                        rcases b1_lt with hb1_zero | hb1_one
                        · simp[hb1_zero ]
                          apply Nat.lt_trans hcase_a2_lt
                          simp
                        · simp[hb1_one ]
                          apply Nat.lt_of_le_of_lt hcase_a2_lt
                          simp
                      have := Nat.shiftRight_eq_zero (z2.val + b1.val) 51 this
                      simp[hb3, ha3, ← h_eq3] at hb3_one
                      rw[nat_lt_two_iff_eq_zero_or_one b2.val] at b2_lt
                      rcases b2_lt with hb2_zero | hb2_one
                      . simp[hb2_zero ] at hb3_one
                      . simp[hb2, ha2, this] at hb2_one
                    . have hz2_le : z2.val ≤ 2 ^ 51 - 1 := by
                        apply Nat.lt_succ_iff.1
                        exact hcase_a2
                      have h_eq2 : 2 ^ 51 - 1 = z2.val := Nat.le_antisymm hcase_a2_lt hz2_le
                      have :=(lt_or_ge z1.val  (2 ^ 51))
                      rw[or_comm] at this
                      rcases  this with hcase_a1 | hcase_a1
                      . have : 0 < 2 ^ (51 * 1) := by norm_num
                        have := mul_le_mul_left'  this hcase_a1
                        have := Nat.add_le_add_right this (2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                        have a_this:= Nat.add_le_add_left this (2 ^ (51 * 0) * z.val[0]!)
                        rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at a_this
                        have := Nat.zero_le (2 ^ (51 * 0) * z.val[0]!)
                        have := Nat.add_le_add_right this (2 ^ (51 * 1) * 2 ^ 51 + 2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                        rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at this
                        have := le_trans this a_this
                        have :0 +2 ^ (51 * 1) * 2 ^ 51 + 2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val ≤ Field51_as_Nat z := by
                          unfold Field51_as_Nat
                          simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,   hz4, hz3, hz2]
                          simp[hz3, hz4, hz2, hz1] at this
                          exact this
                        have := lt_of_le_of_lt this hcase
                        simp[p, ← h_eq, ← h_eq3, ← h_eq2] at this
                      . rcases  lt_or_ge z1.val  (2 ^ 51-1) with hcase_a1_lt | hcase_a1_lt
                        . have : z1.val +b.val < 2 ^ 51  := by
                            rw[nat_lt_two_iff_eq_zero_or_one b.val] at b_lt
                            rcases b_lt with hb_zero | hb_one
                            · simp[hb_zero ]
                              apply Nat.lt_trans hcase_a1_lt
                              simp
                            · simp[hb_one ]
                              apply Nat.lt_of_le_of_lt hcase_a1_lt
                              simp
                          have := Nat.shiftRight_eq_zero (z1.val + b.val) 51 this
                          simp[hb3, ha3, ← h_eq3] at hb3_one
                          rw[nat_lt_two_iff_eq_zero_or_one b2.val] at b2_lt
                          rcases b2_lt with hb2_zero | hb2_one
                          . simp[hb2_zero ] at hb3_one
                          . simp[hb2, ha2, this, ← h_eq2] at hb2_one
                            rw[nat_lt_two_iff_eq_zero_or_one b1.val] at b1_lt
                            rcases b1_lt with hb1_zero | hb1_one
                            · simp[hb1_zero ] at hb2_one
                            · simp[hb1, ha1, this] at hb1_one
                        . have hz1_le : z1.val ≤ 2 ^ 51 - 1 := by
                            apply Nat.lt_succ_iff.1
                            exact hcase_a1
                          have h_eq1 : 2 ^ 51 - 1 = z1.val := Nat.le_antisymm hcase_a1_lt hz1_le
                          have :=(lt_or_ge a.val  (2 ^ 51))
                          rw[or_comm] at this
                          rcases  this with hcase_a | hcase_a
                          . have : 0 < 2 ^ (51 * 0) := by norm_num
                            have := mul_le_mul_left'  this hcase_a
                            have := Nat.add_le_add_right this (2 ^ (51 * 1) * z1.val + 2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                            have a_this:= Nat.add_le_add_left this (0)
                            rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at a_this
                            have := Nat.zero_le (0)
                            have := Nat.add_le_add_right this (2 ^ (51 * 0) * 2 ^ 51 + 2 ^ (51 * 1) * z1.val + 2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val)
                            rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at this
                            have := le_trans this a_this
                            have :0 +2 ^ (51 * 0) * (2^ 51 -19) + 2 ^ (51 * 1) * z1.val + 2 ^ (51 * 2) * z2.val + 2 ^ (51 * 3) * z3.val + 2 ^ (51 * 4) * z4.val ≤ Field51_as_Nat z := by
                              unfold Field51_as_Nat
                              simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,   hz4, hz3, hz2, hz1]
                              simp[hz3, hz4, hz2, hz1] at this
                              simp[ha, hx] at hcase_a
                              apply le_trans _ hcase_a
                              simp
                            have := lt_of_le_of_lt this hcase
                            simp[p, ← h_eq, ← h_eq3, ← h_eq2, ← h_eq1] at this
                          . have := Nat.shiftRight_eq_zero a.val 51 hcase_a
                            rw[this] at hb
                            rw[hb] at ha1
                            rw[ha1] at hb1
                            rw[hb1] at ha2
                            rw[ha2] at hb2
                            rw[hb2] at ha3
                            rw[ha3] at hb3
                            simp[hb3,← h_eq1,← h_eq2,← h_eq3] at hb3_one
      . rw[nat_lt_two_iff_eq_zero_or_one b4.val] at b4_lt
        rw[or_comm] at b4_lt
        rcases b4_lt with hb4_one | hb4_zero
        · rw[hb4_one]
          have h_div_le_one : Field51_as_Nat z / p ≤ 1 := by
            have : Field51_as_Nat z / p < 2 := by
              apply Nat.div_lt_of_lt_mul
              rw[mul_comm]
              exact hcase2
            exact Nat.le_of_lt_succ this
          have h_one_le_div : 1 ≤ Field51_as_Nat z / p := by
            have :0 < p := by simp[p]
            have p_1:= Nat.div_self this
            have : p / p ≤ Field51_as_Nat z / p :=
               Nat.div_le_div_right hcase
            simp[p_1] at this
            exact this
          have h_eq : Field51_as_Nat z / p = 1 := Nat.le_antisymm h_div_le_one h_one_le_div
          rw[h_eq]
        . rw[hb4, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff ] at hb4_zero
          simp at hb4_zero
          rw[ha4] at hb4_zero
          rw[nat_lt_two_iff_eq_zero_or_one b3.val] at b3_lt
          rw[or_comm] at b3_lt
          rcases b3_lt with hb3_one | hb3_zero
          . rw[hb3_one] at hb4_zero
            have :=(lt_or_ge z4.val  (2 ^ 51-1))
            rw[or_comm] at this
            rcases  this with hcase_a4 | hcase_a4
            . have := Nat.add_le_add_right hcase_a4 1
              have := lt_of_le_of_lt this hb4_zero
              simp at this
            . rw[hb3] at hb3_one
              have :=lt_or_ge a3.val  (2 ^ 51)
              rcases  this with hcase_a3 | hcase_a3
              . have := Nat.shiftRight_eq_zero a3.val 51 hcase_a3
                simp[this] at hb3_one
              . rw[ha3] at hcase_a3
                have hcase_a4_le:= Nat.le_pred_of_lt hcase_a4
                have : 0 < 2 ^ (51 * 4) := by norm_num
                have mz4:= mul_le_mul_left'  this  hcase_a4_le
                have : 0 < 2 ^ (51 * 3) := by norm_num
                have mz3:= mul_le_mul_left'  this h_bounds_z3
                have : 0 < 2 ^ (51 * 2) := by norm_num
                have mz2:= mul_le_mul_left'  this h_bounds_z2
                have : 0 < 2 ^ (51 * 1) := by norm_num
                have mz1:= mul_le_mul_left'  this h_bounds_z1
                have := Nat.add_le_add  mz3 mz4
                have := Nat.add_le_add  mz2 this
                have := Nat.add_le_add  mz1 this
                have := Nat.add_le_add  h_bounds_z0 this
                simp[hz4] at this
                rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc,  ← add_assoc] at this
                unfold Field51_as_Nat at hcase
                simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase
                have := le_trans hcase this
                simp[p, hcon] at this
          . simp[hb3_zero] at hb4_zero
            rw[hb3] at hb3_zero
            have :=lt_or_ge a3.val  (2 ^ 51)
            rw[or_comm] at this
            rcases  this with hcase_a3 | hcase_a3
            . simp[Nat.shiftRight_eq_div_pow] at hb3_zero
              have := Nat.lt_of_le_of_lt hcase_a3 hb3_zero
              simp at this
            . rw[ha3] at hcase_a3
              rw[nat_lt_two_iff_eq_zero_or_one b2.val] at b2_lt
              rw[or_comm] at b2_lt
              rcases b2_lt with hb2_one | hb2_zero
              . simp[hb2_one] at hcase_a3
                have :=(lt_or_ge z3.val  (2 ^ 51-1))
                rw[or_comm] at this
                rcases  this with hcase_a3_4 | hcase_a3_4
                . have := Nat.add_le_add_right hcase_a3_4 1
                  have := lt_of_le_of_lt this hcase_a3
                  simp at this
                . have hcase_a4_le:= Nat.le_pred_of_lt hb4_zero
                  have : 0 < 2 ^ (51 * 4) := by norm_num
                  have mz4:= mul_le_mul_left'  this  hcase_a4_le
                  have hcase_a3_le:= Nat.le_pred_of_lt hcase_a3_4
                  have : 0 < 2 ^ (51 * 3) := by norm_num
                  have mz3:= mul_le_mul_left'  this  hcase_a3_le
                  have : 0 < 2 ^ (51 * 2) := by norm_num
                  have mz2:= mul_le_mul_left'  this h_bounds_z2
                  have : 0 < 2 ^ (51 * 1) := by norm_num
                  have mz1:= mul_le_mul_left'  this h_bounds_z1
                  have := Nat.add_le_add  mz3 mz4
                  have := Nat.add_le_add  mz2 this
                  have := Nat.add_le_add  mz1 this
                  have := Nat.add_le_add  h_bounds_z0 this
                  simp[hz3, hz4] at this
                  rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at this
                  unfold Field51_as_Nat at hcase
                  simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase
                  have := le_trans hcase this
                  simp[p, hcon] at this
              . simp[hb2_zero] at hcase_a3
                rw[hb2] at hb2_zero
                have :=lt_or_ge a2.val  (2 ^ 51)
                rw[or_comm] at this
                rcases  this with hcase_a2 | hcase_a2
                . simp[Nat.shiftRight_eq_div_pow] at hb2_zero
                  have := Nat.lt_of_le_of_lt hcase_a2 hb2_zero
                  simp at this
                . rw[ha2] at hcase_a2
                  rw[nat_lt_two_iff_eq_zero_or_one b1.val] at b1_lt
                  rw[or_comm] at b1_lt
                  rcases b1_lt with hb1_one | hb1_zero
                  . simp[hb1_one] at hcase_a2
                    have :=(lt_or_ge z2.val  (2 ^ 51-1))
                    rw[or_comm] at this
                    rcases  this with hcase_a2_4 | hcase_a2_4
                    . have := Nat.add_le_add_right hcase_a2_4 1
                      have := lt_of_le_of_lt this hcase_a2
                      simp at this
                    . have hcase_a4_le:= Nat.le_pred_of_lt hb4_zero
                      have : 0 < 2 ^ (51 * 4) := by norm_num
                      have mz4:= mul_le_mul_left'  this  hcase_a4_le
                      have hcase_a3_le:= Nat.le_pred_of_lt hcase_a3
                      have : 0 < 2 ^ (51 * 3) := by norm_num
                      have mz3:= mul_le_mul_left'  this  hcase_a3_le
                      have hcase_a2_le:= Nat.le_pred_of_lt hcase_a2_4
                      have : 0 < 2 ^ (51 * 2) := by norm_num
                      have mz2:= mul_le_mul_left'  this  hcase_a2_le
                      have : 0 < 2 ^ (51 * 1) := by norm_num
                      have mz1:= mul_le_mul_left'  this h_bounds_z1
                      have := Nat.add_le_add  mz3 mz4
                      have := Nat.add_le_add  mz2 this
                      have := Nat.add_le_add  mz1 this
                      have := Nat.add_le_add  h_bounds_z0 this
                      simp[hz2, hz3, hz4] at this
                      rw[← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at this
                      unfold Field51_as_Nat at hcase
                      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase
                      have := le_trans hcase this
                      simp[p, hcon] at this
                  . simp[hb1_zero] at hcase_a2
                    rw[hb1] at hb1_zero
                    have :=lt_or_ge a1.val  (2 ^ 51)
                    rw[or_comm] at this
                    rcases  this with hcase_a1 | hcase_a1
                    . simp[Nat.shiftRight_eq_div_pow] at hb1_zero
                      have := Nat.lt_of_le_of_lt hcase_a1 hb1_zero
                      simp at this
                    . rw[ha1] at hcase_a1
                      rw[nat_lt_two_iff_eq_zero_or_one b.val] at b_lt
                      rw[or_comm] at b_lt
                      rcases b_lt with hb_one | hb_zero
                      . simp[hb_one] at hcase_a1
                        have :=(lt_or_ge z1.val  (2 ^ 51-1))
                        rw[or_comm] at this
                        rcases  this with hcase_a1_4 | hcase_a1_4
                        . have := Nat.add_le_add_right hcase_a1_4 1
                          have := lt_of_le_of_lt this hcase_a1
                          simp at this
                        . have hcase_a4_le:= Nat.le_pred_of_lt hb4_zero
                          have : 0 < 2 ^ (51 * 4) := by norm_num
                          have mz4:= mul_le_mul_left'  this  hcase_a4_le
                          have hcase_a3_le:= Nat.le_pred_of_lt hcase_a3
                          have : 0 < 2 ^ (51 * 3) := by norm_num
                          have mz3:= mul_le_mul_left'  this  hcase_a3_le
                          have hcase_a2_le:= Nat.le_pred_of_lt hcase_a2
                          have : 0 < 2 ^ (51 * 2) := by norm_num
                          have mz2:= mul_le_mul_left'  this  hcase_a2_le
                          have hcase_a1_le:= Nat.le_pred_of_lt hcase_a1_4
                          have : 0 < 2 ^ (51 * 1) := by norm_num
                          have mz1:= mul_le_mul_left'  this  hcase_a1_le
                          have := Nat.add_le_add  mz3 mz4
                          have := Nat.add_le_add  mz2 this
                          have := Nat.add_le_add  mz1 this
                          have := Nat.add_le_add  h_bounds_z0 this
                          simp[hz1, hz2, hz3, hz4] at this
                          rw[← add_assoc, ← add_assoc, ← add_assoc] at this
                          unfold Field51_as_Nat at hcase
                          simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase
                          have := le_trans hcase this
                          simp[p, hcon] at this
                      . simp[hb_zero] at hcase_a1
                        rw[hb] at hb_zero
                        have :=lt_or_ge a.val  (2 ^ 51)
                        rw[or_comm] at this
                        rcases  this with hcase_a | hcase_a
                        . simp[Nat.shiftRight_eq_div_pow] at hb_zero
                          have := Nat.lt_of_le_of_lt hcase_a hb_zero
                          simp at this
                        . rw[ha] at hcase_a
                          have hcase_a4_le:= Nat.le_pred_of_lt hb4_zero
                          have : 0 < 2 ^ (51 * 4) := by norm_num
                          have mz4:= mul_le_mul_left'  this  hcase_a4_le
                          have hcase_a3_le:= Nat.le_pred_of_lt hcase_a3
                          have : 0 < 2 ^ (51 * 3) := by norm_num
                          have mz3:= mul_le_mul_left'  this  hcase_a3_le
                          have hcase_a2_le:= Nat.le_pred_of_lt hcase_a2
                          have : 0 < 2 ^ (51 * 2) := by norm_num
                          have mz2:= mul_le_mul_left'  this  hcase_a2_le
                          have hcase_a1_le:= Nat.le_pred_of_lt hcase_a1
                          have : 0 < 2 ^ (51 * 1) := by norm_num
                          have mz1:= mul_le_mul_left'  this  hcase_a1_le
                          have hcase_a_le:= Nat.le_pred_of_lt hcase_a
                          have : 0 < 2 ^ (51 * 0) := by norm_num
                          have mz0:= mul_le_mul_left'  this  hcase_a_le
                          simp[] at mz0
                          have := Nat.add_le_add  mz3 mz4
                          have := Nat.add_le_add  mz2 this
                          have := Nat.add_le_add  mz1 this
                          have := Nat.add_le_add  mz0 this
                          simp[hx, hz1, hz2, hz3, hz4] at this
                          rw[← add_assoc, ← add_assoc, ← add_assoc] at this
                          unfold Field51_as_Nat at hcase
                          simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ] at hcase
                          have := le_trans hcase this
                          simp[p] at this


  have hat: Field51_as_Nat z = p * (Field51_as_Nat z / p) + remain := by
    simp[hremain, Nat.div_add_mod]
  rw[← quote] at hat







  have aux_0: ((a11).val[0]).val % 256 = (limbs[0]).val % 256 := by

    simp[ha11_val, hzdu180_val, hi18, ha5]
    rw[i12_eq, land_pow_two_sub_one_eq_mod]
    simp[hzdu0, hzdu_val,  hzd_val]
    rw[← Nat.ModEq]
    simp[hd4, hc4]
    have x_mod_z_256: x.val ≡ Field51_as_Nat z [MOD 256] := by
      unfold Field51_as_Nat
      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp[hx ]
      have := Nat.ModEq.mul_right z1.val mod_51_256
      have := Nat.ModEq.add this (Nat.ModEq.mul_right z2.val mod_102_256)
      have := Nat.ModEq.add this (Nat.ModEq.mul_right z3.val mod_153_256)
      have := Nat.ModEq.add this (Nat.ModEq.mul_right z4.val mod_204_256)
      have := Nat.ModEq.add_left x.val this
      simp[hx, hz1, hz2, hz3, hz4] at this
      rw[← add_assoc, ← add_assoc, ← add_assoc] at this
      apply Nat.ModEq.symm
      simp[this]
    have limbs0_mod_256: (limbs.val)[0] ≡ Field51_as_Nat limbs [MOD 256] := by
      unfold Field51_as_Nat
      simp[Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have := Nat.ModEq.mul_right ((limbs.val)[1]) mod_51_256
      have := Nat.ModEq.add this (Nat.ModEq.mul_right ((limbs.val)[2]) mod_102_256)
      have := Nat.ModEq.add this (Nat.ModEq.mul_right ((limbs.val)[3]) mod_153_256)
      have := Nat.ModEq.add this (Nat.ModEq.mul_right ((limbs.val)[4]) mod_204_256)
      have := Nat.ModEq.add_left ((limbs.val)[0]) this
      simp at this
      rw[← add_assoc, ← add_assoc, ← add_assoc] at this
      apply Nat.ModEq.symm
      simp[this]
    have : Field51_as_Nat z + 19 * b4.val ≡ remain [MOD 256] := by
      rw[hat,p,  add_assoc, add_comm, add_assoc, ← Nat.add_mul]
      have : 19 + (2 ^ 255 - 19) = 2 ^ (51 * 5) := by norm_num
      rw[this]
      have := Nat.ModEq.mul_right b4.val mod_255_256
      have := Nat.ModEq.add_left remain this
      simp at this
      simp
      exact this
    rw[hat] at y
    have y_remain: Field51_as_Nat limbs ≡  remain [MOD p] := by
      simp [Nat.ModEq] at y
      simp[Nat.ModEq]
      exact y


























    rcases  lt_or_ge (Field51_as_Nat z)  (p) with hcase | hcase
    . have := Nat.div_eq_of_lt hcase
      simp[quote, this,hx]
















  iterate 82 progress
  rename_i t30 t29 t28 t27 t26 t25 t24 t23 t22 t21 t20 t19 t18 t17 t16 t15 t14 t13 t12 t11 t10 t9 t8 t7 t6 t5 t4 t3 t2 t1 t0 z30 z29 z28 z27 z26 z25 z24 z23 z22 z21 z20 z19 z18 z17 z16 z15 z14 z13 z12 z11 z10 z9 z8 z7 z6 z5 z4 z3 z2 z1 z0 v30 v29 v28 v27 v26 v25 v24 v23 v22 v21 v20 v19 v18 v17 v16 v15 v14 v13 v12 v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 y30 y29 y28 y27 y26 y25 y24 y23 y22 y21 y20 y19 y18 y17 y16 y15 y14 y13 y12 y11 y10 y9 y8 y7 y6 y5 y4 y3 y2 y1 y0 u30 u29 u28 u27 u26 u25 u24 u23 u22 u21 u20 u19 u18 u17 u16 u15 u14 u13 u12 u11 u10 u9 u8 u7 u6 u5 u4 u3 u2 u1 x31 hx31 hx31_bv  re1 re2 xx2 hxx2_bv xx1 hxx1_bv xx hxx hxx_bv
  rename_i e32 e31 e30 e29 e28 e27 e26 e25 e24 e23 e22 e21 e20 e19 e18 e17 e16 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0
  by_cases hxx0:xx=0#u8
  progress
  intro i
  cases i
  rename_i i hi
  simp
  cases i

  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76]
  simp[ha73, ha70, ha67, ha64, ha61, ha60, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  exact aux_0

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76]
  simp[ha73, ha70, ha67, ha64, ha63, ha62, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]


  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76]
  simp[ha73, ha70, ha67, ha64, ha63, ha66, ha65, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76]
  simp[ha73, ha70, ha67, ha64, ha63, ha66, ha69, ha68, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76]
  simp[ha73, ha70, ha67, ha64, ha63, ha66, ha69, ha72, ha71, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76, e28, ha74, ha59, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76, e28, ha81, ha80, ha77, ha59, ha58, ha55, ha79, ha78]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76, e28, ha81, ha84, ha83, ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e24, ha85, ha82, ha76, e28, ha81, ha84, e26, ha86, ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e19, e22, ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e19, e12, e15, ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19]
  simp[e3, e10, e17, e19, e12, e5, e8, ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19, t21, t24, t27, t29, e1]
  simp[ha78, ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  simp[ha34, ha33, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry


  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19, t21, t14, t17, t29]
  simp[ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  simp[ha34, ha33, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry

  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19, t21, t14, t7, t10, t29]
  simp[ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  simp[ha34, ha33, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry


  rename_i i
  cases i
  simp
  simp[hxx2_bv,u1, u8, u15, u22, u29, y5, y20, y27, v3, v10, v17, v24, z8]
  simp[z15, z22, z29, t5, t12, t19, t21, t14, t7, t0, t3, t29]
  simp[ha58, ha55]
  simp[ha52_val, ha41_val, ha32_val, ha21_val]
  simp[ha34, ha33, ha32_val, ha21_val]
  rw[← Nat.ModEq]
  sorry













  apply U8.ext
  rw[zero_bv]
  simp [hxx_bv,hxx1_bv]
  bv_decide





























































  have : i27.val + i26.val ≤ U64.max := by
   sorry
  progress as ⟨ i27, hi27⟩





































/-- **Spec for `backend.serial.u64.field.FieldElement51.to_bytes`**:

This function converts a field element to its canonical 32-byte little-endian representation.
The implementation performs reduction modulo p = 2^255-19 to ensure the result is in
canonical form.

The algorithm:
1. Reduces the field element using `reduce` to ensure all limbs are within bounds
2. Performs a final conditional reduction to ensure the result is < p
3. Packs the 5 limbs (each 51 bits) into 32 bytes in little-endian format

Specification:
- The function succeeds (no panic)
- The natural number interpretation of the byte array is congruent to the field element value modulo p
- The byte array represents the unique canonical form (0 ≤ value < p)
-/
@[progress]
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    ∃ result, to_bytes self = ok result ∧
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p := by
  unfold to_bytes
  progress*
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · expand fe_post_1 with 5; scalar_tac
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

end curve25519_dalek.backend.serial.u64.field.FieldElement51
