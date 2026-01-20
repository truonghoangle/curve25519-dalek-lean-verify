/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `ProjectivePoint::identity`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::traits::Identity for curve25519_dalek::montgomery::ProjectivePoint}::identity`.

This function returns the identity element of the Montgomery curve in
projective (U : W) coordinates.

**Source**: curve25519-dalek/src/montgomery.rs, lines 296:4-301:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.IdentityProjectivePoint

/-
natural language description:

• Returns the identity element of the Montgomery curve in projective
  coordinates (U, W).

natural language specs:

• The function always succeeds (no panic)
• The resulting ProjectivePoint is the identity with U = 1 and W = 0
-/

/-- **Spec and proof concerning `montgomery.IdentityProjectivePoint.identity`**:
- No panic (always returns successfully)
- The resulting ProjectivePoint is the identity with U = 1 and W = 0
-/
@[progress]
theorem identity_spec :
    ∃ p,
    identity = ok p ∧
    p.U = backend.serial.u64.field.FieldElement51.ONE ∧
      p.W = backend.serial.u64.field.FieldElement51.ZERO := by
  unfold identity
  simp

end curve25519_dalek.montgomery.IdentityProjectivePoint
