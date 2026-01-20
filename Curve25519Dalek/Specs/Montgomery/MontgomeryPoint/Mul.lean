/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `MontgomeryPoint::mul`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::montgomery::MontgomeryPoint), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::scalar::Scalar)}::mul`.

This function implements scalar multiplication of a MontgomeryPoint by delegating to the
corresponding MontgomeryPoint * Scalar implementation (the Montgomery ladder in the backend).

**Source**: curve25519-dalek/src/montgomery.rs, lines 462:4-464:5

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint

/-
natural language description:

• Computes the scalar multiplication [s]P on the Montgomery curve, where s is a Scalar
  and P is a MontgomeryPoint (u-coordinate only).

• The implementation simply calls the MontgomeryPoint * Scalar routine, which uses the
  Montgomery ladder on the u-coordinate.

natural language specs:

• The function always succeeds (no panic)
• The result is exactly the output of `MontgomeryPoint * Scalar` with arguments swapped
-/

/-- **Spec and proof concerning `montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully)
- Delegates to `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`
- The returned MontgomeryPoint equals the Montgomery ladder result for the given scalar and point
-/
@[progress]
theorem mul_spec (self : scalar.Scalar) (point : MontgomeryPoint) :
    ∃ result,
    mul self point = ok result ∧
    montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul point self =
      ok result := by

    sorry

end curve25519_dalek.montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint
