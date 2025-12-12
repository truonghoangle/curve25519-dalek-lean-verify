/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq

/-! # Eq

Specification and proof for `FieldElement51::eq`.

This function implements equality testing for field elements by wrapping constant-time equality.
It converts the result from a `Choice` to a `Bool`.

Source: curve25519-dalek/src/field.rs, lines 87:4-89:5
-/

open Aeneas.Std Result
open curve25519_dalek.field.ConstantTimeEqcurve25519_dalekbackendserialu64fieldFieldElement51

namespace curve25519_dalek.field.PartialEqcurve25519_dalekbackendserialu64fieldFieldElement51curve25519_dalekbackendserialu64fieldFieldElement51

/-! ## Spec for `eq` -/

/-- Helper lemma: Choice.one has val = 1 -/
lemma Choice.val_eq_one_iff (c : subtle.Choice) :
  c.val = 1#u8 ↔ c = Choice.one := by
  cases c with
  | mk val valid =>
    simp [Choice.one]

/-- **Spec for `backend.serial.u64.field.FieldElement51.eq`**:
- No panic (always returns successfully)
- Returns `true` iff the two field elements are equal (same canonical representation)
- Internally uses constant-time comparison via `ct_eq` and converts `Choice` to `Bool`
- Equality is determined by comparing canonical byte representations -/
@[progress]
theorem eq_spec (a b : backend.serial.u64.field.FieldElement51) :
    ∃ result, eq a b = ok result ∧
    (result = true ↔ a.to_bytes = b.to_bytes) := by
  unfold eq
  progress*
  unfold subtle.FromBoolsubtleChoice.from
  simp only [ ok.injEq, exists_eq_left']
  simp only [decide_eq_true_eq]
  rw [Choice.val_eq_one_iff]
  simp_all

end curve25519_dalek.field.PartialEqcurve25519_dalekbackendserialu64fieldFieldElement51curve25519_dalekbackendserialu64fieldFieldElement51
