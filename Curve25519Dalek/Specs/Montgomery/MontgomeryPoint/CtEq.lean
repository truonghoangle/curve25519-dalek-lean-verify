/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

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
      backend.serial.u64.field.FieldElement51.from_bytes self = ok self_fe ∧
      backend.serial.u64.field.FieldElement51.from_bytes other = ok other_fe ∧
      field.ConstantTimeEqFieldElement51.ct_eq self_fe other_fe = ok c := by

    sorry

end curve25519_dalek.montgomery.ConstantTimeEqMontgomeryPoint
