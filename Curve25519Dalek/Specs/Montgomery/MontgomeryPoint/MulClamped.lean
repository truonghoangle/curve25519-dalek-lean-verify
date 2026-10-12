/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Auxiliary
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Mul
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_clamped`

This function clamps a 32-byte input to a scalar and performs Montgomery
scalar multiplication of the given point by the clamped scalar.

• Clamps the 32-byte input to a valid scalar using `scalar.clamp_integer`.
• Multiplies the MontgomeryPoint by the clamped scalar via
  `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_clamped`**
• The function always succeeds (no panic)
• The result satisfies `MontgomeryPoint.mkPoint result = m • (MontgomeryPoint.mkPoint P)`
  where `m = 2^254 + 8 * ((U8x32_as_Nat bytes / 8) % 2^251)` is the *deterministic*
  clamped value of the input bytes (RFC 7748 `decodeScalar25519`); `m` is divisible
  by the cofactor `h = 8` and lies in `[2^254, 2^255)`
-/
@[step]
theorem mul_clamped_spec (P : MontgomeryPoint) (bytes : Array U8 32#usize)
    (hP_bound : U8x32_as_Nat P < 2 ^ 255) :
    mul_clamped P bytes ⦃ (result : MontgomeryPoint) =>
      MontgomeryPoint.mkPoint result =
        (2 ^ 254 + 8 * (U8x32_as_Nat bytes / 8 % 2 ^ 251)) •
          (MontgomeryPoint.mkPoint P) ⦄ := by
  unfold mul_clamped
  step*
  have := Nat.mod_eq_of_lt a_post2
  rw [this] at result_post
  rw [← a_post4]
  exact result_post

end curve25519_dalek.montgomery.MontgomeryPoint
