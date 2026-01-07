/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Assistant
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `CompressedEdwardsY::decompress::step_2`

Specification and proof for the second step of `CompressedEdwardsY::decompress`.

This function performs the final decompression step which:
1. Extracts the sign bit from the compressed representation
2. Conditionally negates the x-coordinate according to the sign bit
3. Computes T = X * Y
4. Returns the complete EdwardsPoint in extended coordinates (X, Y, Z, T)

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul
namespace curve25519_dalek.edwards.CompressedEdwardsY

/-
Natural language description:

    - Takes a CompressedEdwardsY and field elements X, Y, Z from step_1
    - Extracts the sign bit from the high bit of byte 31 of the compressed representation
    - Since sqrt_ratio_i returns the nonnegative square root, conditionally negates X
      according to the sign bit to match the encoded sign
    - Computes T = X * Y (the product of x and y coordinates)
    - Returns an EdwardsPoint with coordinates (X, Y, Z, T)

Natural language specs:

    - The function always succeeds (no panic)
    - The sign bit is extracted from the high bit (bit 7) of byte 31
    - X is conditionally negated: if the sign bit is set, X becomes -X
    - T is computed as the product X * Y (mod p)
    - The returned point has Z unchanged from the input
    - The returned point satisfies T = X * Y (mod p)
-/

/-- **Spec for `edwards.decompress.step_2`**:
- No panic (always returns successfully)
- Returns an EdwardsPoint with coordinates (X', Y, Z, T) where:
  - The sign bit is extracted from bit 7 of byte 31 of the compressed representation
  - X' is conditionally negated based on the sign bit:
    - If sign bit is 0, X' = X
    - If sign bit is 1, X' = -X (mod p)
  - Y and Z are unchanged from the inputs
  - T = X' * Y (mod p)
-/
@[progress]
theorem step_2_spec
    (repr : edwards.CompressedEdwardsY)
    (X : backend.serial.u64.field.FieldElement51)
    (Y : backend.serial.u64.field.FieldElement51)
    (Z : backend.serial.u64.field.FieldElement51) :
    ∃ result, edwards.decompress.step_2 repr X Y Z = ok result ∧

      let ep := result

      -- Y and Z are unchanged
      ep.Y = Y ∧
      ep.Z = Z ∧

      -- The sign bit is extracted from the compressed representation
      (∃ bytes sign_bit,
        edwards.CompressedEdwardsY.as_bytes repr = ok bytes ∧
        sign_bit = (bytes[31]!.val.testBit 7) ∧

        -- X is conditionally negated based on the sign bit
        (if sign_bit then
          (∃ neg_X,
            backend.serial.u64.field.FieldElement51.neg X = ok neg_X ∧
            ep.X = neg_X)
        else
          ep.X = X) ∧

        -- T = X' * Y
        (∃ T_computed,
          mul ep.X Y = ok T_computed ∧
          ep.T = T_computed)) := by
  sorry

end curve25519_dalek.edwards.CompressedEdwardsY
