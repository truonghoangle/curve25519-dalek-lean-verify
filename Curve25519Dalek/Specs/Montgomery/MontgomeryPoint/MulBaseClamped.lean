/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.MulBase
import Curve25519Dalek.Specs.Scalar.ClampInteger

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_base_clamped`

This function performs scalar multiplication by the Montgomery basepoint after
clamping the input bytes to a valid scalar.

• Clamps the 32-byte input to a valid scalar using `scalar::clamp_integer`.
• Computes the Montgomery basepoint multiplication with the clamped scalar by
  delegating to `MontgomeryPoint::mul_base`.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64 Montgomery
namespace curve25519_dalek.montgomery.MontgomeryPoint

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::mul_base_clamped`**
• The function always succeeds (no panic)
• With `n = 2^254 + 8 * ((U8x32_as_Nat bytes / 8) % 2^251)` the *deterministic*
  clamped value of the input bytes (RFC 7748 `decodeScalar25519`, divisible by the
  cofactor `h = 8` and lying in `[2^254, 2^255)`):
  `mkPoint result = T_point` if `(n • Edwards.basepoint).y = 1`, and
  `mkPoint result = abs_montgomery (n • fromEdwards basepoint)` otherwise
-/
@[step]
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (result : MontgomeryPoint) =>
      let n := 2 ^ 254 + 8 * (U8x32_as_Nat bytes / 8 % 2 ^ 251)
      (if (n • Edwards.basepoint).y = 1 then
          MontgomeryPoint.mkPoint result = T_point
        else MontgomeryPoint.mkPoint result =
          abs_montgomery (n • fromEdwards _root_.Edwards.basepoint)) ⦄ := by
  unfold mul_base_clamped
  step with scalar.clamp_integer_spec
  step with mul_base_spec ({ bytes := a } : scalar.Scalar) a_post2
  simp_all [← U8x32_as_Nat_eq_foldr' a]

end curve25519_dalek.montgomery.MontgomeryPoint
