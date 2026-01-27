/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Field.FieldElement51.Invert

import Mathlib.Data.Nat.ModEq
/-! # Spec Theorem for `ProjectivePoint::as_affine`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::ProjectivePoint}::as_affine`.

This function dehomogenizes a projective point to affine coordinates by computing
u = U / W, where the division is performed via multiplication by the inverse of W.

**Source**: curve25519-dalek/src/montgomery.rs, lines 330:4-333:5

--/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.montgomery.ProjectivePoint

/-
Natural language description:

    • Computes the inverse of the projective W coordinate using `FieldElement51.invert`.

    • Multiplies the projective U coordinate by the inverse of W to obtain the affine
      u-coordinate.

    • Converts the resulting field element to a 32-byte representation.

Natural language specs:

    • The function always succeeds (no panic) given bounded inputs
    • Returns the affine u-coordinate u = U / W when W ≠ 0 (mod p)
    • Returns 0 when W = 0 (mod p) (by the behavior of FieldElement51.invert)
    • The conversion preserves the mathematical relationship between projective and
      affine representations
-/
/-- **Spec and proof concerning `montgomery.ProjectivePoint.as_affine`**:
- No panic (always returns successfully given bounded inputs)
- Correctly dehomogenizes the projective point (U : W) to affine coordinates
- The returned `MontgomeryPoint` represents the u-coordinate in affine form
- Mathematical properties of the result after `ok`:
  * When W ≢ 0 (mod p): The result encodes the field element u = U/W,
    meaning the byte representation satisfies
    U8x32_as_Nat(result) ≡ (Field51_as_Nat(U) · Field51_as_Nat(W)^(p-2)) (mod p),
    which recovers the affine u-coordinate from the projective representation (U : W)
  * When W ≡ 0 (mod p): The result encodes 0, corresponding to the point at infinity
    in the projective representation
  * The conversion to bytes ensures the result fits canonically in a 32-byte
    MontgomeryPoint encoding with value reduced modulo 2^255
-/

@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : ∀ i < 5, (self.U[i]!).val < 2 ^ 54)
    (hW : ∀ i < 5, (self.W[i]!).val < 2 ^ 54) :
    ∃ result,
    as_affine self = ok result ∧
    let U_nat := Field51_as_Nat self.U % p
    let W_nat := Field51_as_Nat self.W % p
    (W_nat ≠ 0 →
      (U8x32_as_Nat result % 2 ^ 255) ≡ (U_nat * W_nat ^ (p - 2)) [MOD p]) ∧
    (W_nat = 0 →
      (U8x32_as_Nat result % 2 ^ 255) ≡ 0 [MOD p]) := by
  unfold as_affine
  sorry

end curve25519_dalek.montgomery.ProjectivePoint
