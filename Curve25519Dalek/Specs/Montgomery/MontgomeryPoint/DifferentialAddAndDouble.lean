/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `montgomery::differential_add_and_double`

Specification and proof for
`curve25519_dalek::montgomery::differential_add_and_double`.

This function performs the core Montgomery ladder step, taking two projective
points P and Q along with the affine u-coordinate of P - Q, and returns the
projective points corresponding to 2P and P + Q.

**Source**: curve25519-dalek/src/montgomery.rs, lines 351:0-389:1

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery

/-
natural language description:

• Computes the differential addition and doubling step used in the Montgomery
  ladder. Given projective points P and Q representing (x_P : z_P) and
  (x_Q : z_Q), together with the affine u-coordinate of (P - Q), it produces
  projective points for 2P and P + Q.

• The function follows the standard Montgomery formulas using additions,
  subtractions, squarings, and multiplications in the FieldElement51 field.

natural language specs:

• The function always succeeds (no panic)
• Returns (P2, P3) where P2 corresponds to 2P and P3 corresponds to P + Q
  with intermediate values computed exactly as in the Rust implementation
-/

/-- **Spec and proof concerning `montgomery.differential_add_and_double`**:
- No panic (always returns successfully)
- The returned pair (P2, P3) is computed using the standard Montgomery ladder
  formulas for doubling and differential addition
- The output coordinates are exactly those computed by the sequence of
  field operations in the implementation
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    ∃ P2 P3,
    differential_add_and_double P Q affine_PmQ = ok (P2, P3) ∧
    ∃ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17,
      backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
        P.U P.W = ok t0 ∧
      backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
        P.U P.W = ok t1 ∧
      backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
        Q.U Q.W = ok t2 ∧
      backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
        Q.U Q.W = ok t3 ∧
      backend.serial.u64.field.FieldElement51.square t0 = ok t4 ∧
      backend.serial.u64.field.FieldElement51.square t1 = ok t5 ∧
      backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
        t4 t5 = ok t6 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        t0 t3 = ok t7 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        t1 t2 = ok t8 ∧
      backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
        t7 t8 = ok t9 ∧
      backend.serial.u64.field.SubShared0FieldElement51SharedAFieldElement51FieldElement51.sub
        t7 t8 = ok t10 ∧
      backend.serial.u64.field.FieldElement51.square t9 = ok t11 ∧
      backend.serial.u64.field.FieldElement51.square t10 = ok t12 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        backend.serial.u64.constants.APLUS2_OVER_FOUR t6 = ok t13 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        t4 t5 = ok t14 ∧
      backend.serial.u64.field.AddShared0FieldElement51SharedAFieldElement51FieldElement51.add
        t13 t5 = ok t15 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        t6 t15 = ok t16 ∧
      backend.serial.u64.field.MulShared0FieldElement51SharedAFieldElement51FieldElement51.mul
        affine_PmQ t12 = ok t17 ∧
      P2 = { U := t14, W := t16 } ∧
      P3 = { U := t11, W := t17 } := by

    sorry

end curve25519_dalek.montgomery
