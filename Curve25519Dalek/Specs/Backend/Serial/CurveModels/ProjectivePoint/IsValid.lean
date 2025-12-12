/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Eq
/-! # Spec Theorem for `ProjectivePoint::is_valid`

Specification and proof for `ProjectivePoint::is_valid`.

This function validates whether a ProjectivePoint satisfies the Curve25519 elliptic curve
equation in projective coordinates. Given a point P = (X:Y:Z), it checks if the point
lies on the curve by verifying the homogenized Edwards curve equation.

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/- [curve25519_dalek::backend::serial::curve_models::{curve25519_dalek::backend::serial::curve_models::ProjectivePoint}::is_valid]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 276:4-289:5 -/
noncomputable def is_valid
  (self : ProjectivePoint) : Result Bool := do
  let XX ← backend.serial.u64.field.FieldElement51.square self.X
  let YY ← backend.serial.u64.field.FieldElement51.square self.Y
  let ZZ ← backend.serial.u64.field.FieldElement51.square self.Z
  let ZZZZ ← backend.serial.u64.field.FieldElement51.square ZZ
  let fe ←
    backend.serial.u64.field.FieldElement51.Sub.sub
      YY XX
  let lhs ←
    backend.serial.u64.field.FieldElement51.Mul.mul
      fe ZZ
  let fe1 ←
    backend.serial.u64.field.FieldElement51.Mul.mul
      XX YY
  let fe2 ←
    backend.serial.u64.field.FieldElement51.Mul.mul
      backend.serial.u64.constants.EDWARDS_D fe1
  let rhs ←
    backend.serial.u64.field.FieldElement51.Add.add
      ZZZZ fe2
  field.PartialEqcurve25519_dalekbackendserialu64fieldFieldElement51curve25519_dalekbackendserialu64fieldFieldElement51.eq
    lhs rhs

/-
natural language description:

• Takes a ProjectivePoint with coordinates (X, Y, Z) and returns a boolean indicating
whether the point satisfies the Edwards curve equation in projective form. Arithmetics are
performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input point (X, Y, Z), the output is true if and only if:
  (-X² + Y²)·Z² ≡ Z⁴ + d·X²·Y² (mod p)
  which is the homogenized form of the Edwards curve equation: -x² + y² = 1 + d·x²·y²
-/

/- **Spec and proof concerning `backend.serial.curve_models.ProjectivePoint.is_valid`**:
- No panic (always returns successfully)
- Given input ProjectivePoint with coordinates (X, Y, Z), the function returns true if and only if
the point satisfies the projective Edwards curve equation modulo p:
  (-X² + Y²)·Z² ≡ Z⁴ + d·X²·Y² (mod p)
where p = 2^255 - 19 and d is the Edwards curve constant.
This validates that the point lies on the Curve25519 elliptic curve.
-/

set_option maxHeartbeats 1000000 in
-- simp_all is heavy

@[progress]
theorem is_valid_spec (q : ProjectivePoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val ≤ 2 ^ 52)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val ≤ 2 ^ 52)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val ≤ 2 ^ 52) :
    ∃ b, is_valid q = ok b ∧
    let X := Field51_as_Nat q.X
    let Y := Field51_as_Nat q.Y
    let Z := Field51_as_Nat q.Z
    let d := Field51_as_Nat backend.serial.u64.constants.EDWARDS_D
    (b = true ↔ (Y^2 * Z^2) % p = (Z^4 + d * X^2 * Y^2 + X^2 * Z^2) % p) := by
  unfold is_valid
  progress as ⟨XX, h_XX, XX_bounds⟩
  · intro i hi
    have := h_qX_bounds i hi
    scalar_tac
  progress as ⟨YY, h_YY, YY_bounds⟩
  · intro i hi
    have := h_qY_bounds i hi
    scalar_tac
  progress as ⟨ZZ, h_ZZ, ZZ_bounds⟩
  · intro i hi
    have := h_qZ_bounds i hi
    scalar_tac
  progress as ⟨ZZZZ, h_ZZZZ, ZZZZ_bounds⟩
  · intro i hi
    have := ZZ_bounds i hi
    scalar_tac
  progress as ⟨fe, h_fe, fe_bounds⟩
  · intro i hi
    have := YY_bounds i hi
    scalar_tac
  · intro i hi
    have := XX_bounds i hi
    scalar_tac
  progress as ⟨lhs, lhs_fe, lhs_bounds⟩
  · intro i hi
    have := h_fe i hi
    scalar_tac
  · intro i hi
    have := ZZ_bounds i hi
    scalar_tac
  progress as ⟨fe1, h_fe1, fe1_bounds⟩
  · intro i hi
    have := XX_bounds i hi
    scalar_tac
  · intro i hi
    have := YY_bounds i hi
    scalar_tac
  progress as ⟨fe2, h_fe2, fe2_bounds⟩
  · unfold u64.constants.EDWARDS_D
    decide
  · intro i hi
    have := fe1_bounds i hi
    scalar_tac
  progress as ⟨rhs, h_rhs, rhs_bounds⟩
  · intro i hi
    have := ZZZZ_bounds i hi
    scalar_tac
  · intro i hi
    have := fe2_bounds i hi
    scalar_tac
  progress as ⟨ c, hc⟩
  constructor
  · intro h_true
    simp[h_true] at hc
    rw[← Nat.ModEq]
    sorry
  · sorry  

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
