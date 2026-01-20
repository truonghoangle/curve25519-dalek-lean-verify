/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `MontgomeryPoint::eq`

Specification and proof for
`curve25519_dalek::montgomery::{core::cmp::PartialEq<curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::eq`.

This function compares two MontgomeryPoint values by checking constant-time
field element equality of their u-coordinates, then converting the resulting
Choice into a Bool.

**Source**: curve25519-dalek/src/montgomery.rs, lines 94:4-96:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.PartialEqMontgomeryPointMontgomeryPoint

/-
natural language description:

• Compares two MontgomeryPoint values by constant-time equality of their
  u-coordinates (decoded as FieldElement51).

• The result Choice is converted into Bool via FromBoolChoice.

natural language specs:

• The function always succeeds (no panic)
• The result is true iff the underlying field elements represent the same
  value modulo p
-/

/-- **Spec and proof concerning `montgomery.PartialEqMontgomeryPointMontgomeryPoint.eq`**:
- No panic (always returns successfully)
- Returns true iff the u-coordinates are equal modulo p
- Implemented via constant-time equality followed by Choice-to-Bool conversion
-/
@[progress]
theorem eq_spec (self other : MontgomeryPoint) :
    ∃ b,
    eq self other = ok b ∧
    (b = true ↔
      ∃ c,
      montgomery.ConstantTimeEqMontgomeryPoint.ct_eq self other = ok c ∧
      c = Choice.one) := by

    sorry

end curve25519_dalek.montgomery.PartialEqMontgomeryPointMontgomeryPoint
