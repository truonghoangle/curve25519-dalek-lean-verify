/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `ProjectivePoint::conditional_select`

Specification and proof for
`curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_select`.

This function selects between two Montgomery projective points in constant time,
by conditionally selecting each coordinate (U and W) using
`FieldElement51::conditional_select`.

**Source**: curve25519-dalek/src/montgomery.rs, lines 311:4-320:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.ConditionallySelectableProjectivePoint

/-
natural language description:

• Takes two projective points a = (U, W) and b = (U', W') and a constant-time
  Choice flag, then conditionally selects each coordinate using
  `FieldElement51::conditional_select`.

• The resulting projective point has U chosen from a.U or b.U depending on the
  Choice, and similarly for W.

natural language specs:

• The function always succeeds (no panic)
• The result is computed by conditionally selecting U and W independently
  according to `choice`
-/

/-- **Spec and proof concerning `montgomery.ConditionallySelectableProjectivePoint.conditional_select`**:
- No panic (always returns successfully)
- Selects each coordinate using `FieldElement51::conditional_select`
- The resulting projective point is `{ U := u, W := w }` with the selected
  coordinates
-/
@[progress]
theorem conditional_select_spec
    (a b : montgomery.ProjectivePoint)
    (choice : subtle.Choice) :
    ∃ res,
    conditional_select a b choice = ok res ∧
    ∃ u w,
      backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select
        a.U b.U choice = ok u ∧
      backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select
        a.W b.W choice = ok w ∧
      res = { U := u, W := w } := by

    sorry

end curve25519_dalek.montgomery.ConditionallySelectableProjectivePoint
