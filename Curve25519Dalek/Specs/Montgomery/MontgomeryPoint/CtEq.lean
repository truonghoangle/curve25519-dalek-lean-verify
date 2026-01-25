/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
/-! # Spec Theorem for `MontgomeryPoint::ct_eq`

Specification and proof for
`curve25519_dalek::montgomery::{subtle::ConstantTimeEq for curve25519_dalek::montgomery::MontgomeryPoint}::ct_eq`.

This function compares two MontgomeryPoint values in constant time by
interpreting their 32-byte encodings as FieldElement51 values and then
delegating to FieldElement51 constant-time equality.

**Source**: curve25519-dalek/src/montgomery.rs, lines 79:4-84:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.field.FieldElement51
namespace curve25519_dalek.montgomery.ConstantTimeEqMontgomeryPoint

/-
natural language description:

• Interprets each MontgomeryPoint byte array as a FieldElement51 using
  `FieldElement51.from_bytes`.

• Calls the FieldElement51 constant-time equality routine on the two
  decoded field elements.

natural language specs:

• The function always succeeds (no panic)
• The result is exactly the output of `field.ConstantTimeEqFieldElement51.ct_eq`
  on the decoded field elements
-/

/-- **Spec and proof concerning `montgomery.ConstantTimeEqMontgomeryPoint.ct_eq`**:
- No panic (always returns successfully)
- Delegates to `field.ConstantTimeEqFieldElement51.ct_eq` on the decoded u-coordinates
- The returned Choice is the constant-time equality result of those field elements
-/



@[progress]
theorem ct_eq_spec (self other : MontgomeryPoint) :
    ∃ c,
    ct_eq self other = ok c ∧
    ∃ self_fe other_fe,
      from_bytes self = ok self_fe ∧
      from_bytes other = ok other_fe ∧
      field.ConstantTimeEqFieldElement51.ct_eq self_fe other_fe = ok c := by
  unfold ct_eq
  progress*
  use self_fe
  use other_fe
  simp
  unfold field.ConstantTimeEqFieldElement51.ct_eq
  progress as ⟨ a, ha,ha_lt⟩
  progress as ⟨ sa, hsa⟩
  progress as ⟨ b, hb,hb_lt⟩
  progress as ⟨ sb, hsb⟩
  progress as ⟨ c, ch⟩
  by_cases h: c = Choice.one
  · simp_all
    have: a=b :=by
      have : a.to_slice = b.to_slice := by grind
      simp only [Array.to_slice, Slice.eq_iff] at *
      exact Subtype.eq this
    simp_all
    have eq:=ha.symm.trans hb
    apply symm
    rw[res_post ]
    obtain ⟨ru, hu, hru_mod, hu_lt⟩ := to_bytes_spec self_fe
    obtain ⟨rv, hv, hrv_mod, hv_lt⟩ := to_bytes_spec other_fe
    have eq:=(hru_mod.trans eq).trans hrv_mod.symm
    simp[Nat.ModEq] at eq
    have :=Nat.mod_eq_of_lt hu_lt
    rw[this] at eq
    have :=Nat.mod_eq_of_lt hv_lt
    rw[this] at eq
    have  := U8x32_as_Nat_injective
    simp[Function.Injective] at this
    have := @this _ _ eq
    simp_all
  · simp_all
    by_cases h1: res = Choice.one
    · simp_all
      have eq:= eq_to_bytes_eq_Field51_as_Nat res_post
      rw[← Nat.ModEq] at eq
      have eq:= (ha.trans eq).trans hb.symm
      simp[Nat.ModEq] at eq
      have :=Nat.mod_eq_of_lt ha_lt
      rw[this] at eq
      have :=Nat.mod_eq_of_lt hb_lt
      rw[this] at eq
      have  := U8x32_as_Nat_injective
      simp[Function.Injective] at this
      have := @this _ _ eq
      simp_all
    ·
      have :res = Choice.zero := by
          cases res with
          | mk v hvalid =>
            cases hvalid with
            | inl hv0 =>
                -- v = 0
                simp [Choice.zero, hv0]
            | inr hv1 =>
                -- v = 1, contradiction with h1
                exfalso
                apply h1
                simp [Choice.one, hv1]

      have :c = Choice.zero := by
          cases c with
          | mk v hvalid =>
            cases hvalid with
            | inl hv0 =>
                -- v = 0
                simp [Choice.zero, hv0]
            | inr hv1 =>
                -- v = 1, contradiction with h1
                exfalso
                apply h
                simp [Choice.one, hv1]
      simp_all

end curve25519_dalek.montgomery.ConstantTimeEqMontgomeryPoint
