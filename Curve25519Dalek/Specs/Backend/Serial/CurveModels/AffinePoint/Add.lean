/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add

/-! # Spec Theorem for `EdwardsPoint + AffineNielsPoint` (Affine addition)

Specification and proof for the addition of an Edwards point in extended
coordinates with a point in affine Niels coordinates, returning the result
in completed coordinates (ℙ¹ × ℙ¹).

This mirrors the Rust implementation at
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` lines 458–473:

impl<'a> Add<&'a AffineNielsPoint> for &EdwardsPoint { type Output = CompletedPoint; fn add(..) }

Formulas (with P = (X:Y:Z:T) and N = (y_plus_x, y_minus_x, xy2d)):
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PP        = Y_plus_X  · N.y_plus_x
- MM        = Y_minus_X · N.y_minus_x
- Txy2d     = T · N.xy2d
- Z2        = Z + Z
- X'        = PP − MM
- Y'        = PP + MM
- Z'        = Z2 + Txy2d
- T'        = Z2 − Txy2d
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models

/-- Local mirror of AffineNielsPoint for specification purposes (not extracted).
Represents (y+x, y−x, 2dxy). -/
structure AffineNielsPoint where
  y_plus_x  : backend.serial.u64.field.FieldElement51
  y_minus_x : backend.serial.u64.field.FieldElement51
  xy2d      : backend.serial.u64.field.FieldElement51

end curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/- Lean extraction of the affine-Niels addition (spec-level function). -/
/-- Add an EdwardsPoint to an AffineNielsPoint, returning a CompletedPoint. -/
def add_affine
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.AffineNielsPoint) :
  Result backend.serial.curve_models.CompletedPoint := do
  let Y_plus_X ← FieldElement51.Add.add self.Y self.X
  let Y_minus_X ← FieldElement51.Sub.sub self.Y self.X
  let PP ← FieldElement51.Mul.mul Y_plus_X other.y_plus_x
  let MM ← FieldElement51.Mul.mul Y_minus_X other.y_minus_x
  let Txy2d ← FieldElement51.Mul.mul self.T other.xy2d
  let Z2 ← FieldElement51.Add.add self.Z self.Z
  let fe ← FieldElement51.Sub.sub PP MM
  let fe1 ← FieldElement51.Add.add PP MM
  let fe2 ← FieldElement51.Add.add Z2 Txy2d
  let fe3 ← FieldElement51.Sub.sub Z2 Txy2d
  ok { X := fe, Y := fe1, Z := fe2, T := fe3 }

/-! ## Specification

Arithmetic is modulo p = 2^255 − 19 on the limb-reconstructed naturals.
- Y_plus_X ≡ Y + X
- Y_minus_X ≡ Y − X
- Z2 ≡ 2·Z
- Txy2d ≡ T · xy2d
- X' ≡ PP − MM
- Y' ≡ PP + MM
- Z' ≡ 2·Z + T·xy2d
- T' ≡ 2·Z − T·xy2d
-/

set_option maxHeartbeats 1000000 in
-- simp_all heavy
@[progress]
theorem add_affine_spec
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.AffineNielsPoint)
  (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
  (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
  (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
  (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
  (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
  (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
  (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
∃ c,
add_affine self other = ok c ∧
let X := Field51_as_Nat self.X
let Y := Field51_as_Nat self.Y
let Z := Field51_as_Nat self.Z
let T := Field51_as_Nat self.T
let ypx := Field51_as_Nat other.y_plus_x
let ymx := Field51_as_Nat other.y_minus_x
let xy2d := Field51_as_Nat other.xy2d
let X' := Field51_as_Nat c.X
let Y' := Field51_as_Nat c.Y
let Z' := Field51_as_Nat c.Z
let T' := Field51_as_Nat c.T
(X' + Y * ymx) % p = (((Y + X) * ypx) + X * ymx) % p ∧
(Y' + X * ymx) % p = (((Y + X) * ypx) + Y * ymx) % p ∧
Z' % p = ((2 * Z) + (T * xy2d)) % p ∧
(T' + T * xy2d) % p = (2 * Z) % p := by
  unfold add_affine
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  · intro i hi; exact lt_trans (h_selfY_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_selfX_bounds i hi) (by simp)
  progress as ⟨PP, h_PP, PP_bounds⟩
  · intro i hi; exact lt_trans (h_otherYpX_bounds i hi) (by simp)
  progress as ⟨MM, h_MM, MM_bounds⟩
  · intro i hi; exact lt_trans (Y_minus_X_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_otherYmX_bounds i hi) (by simp)
  progress as ⟨Txy2d, h_Txy2d, Txy2d_bounds⟩
  · intro i hi; exact lt_trans (h_selfT_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_otherXY2d_bounds i hi) (by simp)
  progress as ⟨Z2, h_Z2, Z2_bounds⟩
  progress as ⟨fe, h_fe, fe_bounds⟩
  · intro i hi; exact lt_trans (PP_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (MM_bounds i hi) (by simp)
  progress as ⟨fe1, h_fe1, fe1_bounds⟩
  · intro i hi; exact lt_trans (PP_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (MM_bounds i hi) (by simp)
  have hzz: ∀ i < 5, Z2[i]!.val < 2 ^ 54 := by simp_all
  obtain ⟨fe2, h_fe2_ok, h_fe2, fe2_bounds⟩ := CompletedPoint.add_spec' hzz  Txy2d_bounds
  simp only [h_fe2_ok, bind_tc_ok]
  progress as ⟨fe3, h_fe3, fe3_bounds⟩
  · intro i hi; exact lt_trans (Z2_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (Txy2d_bounds i hi) (by simp)
  constructor
  · rw[← Nat.ModEq]; rw[← Nat.ModEq] at fe_bounds
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.y_minus_x) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PP)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_bounds)
    apply Nat.ModEq.add_left
    exact h_MM
  constructor
  · rw[← Nat.ModEq]
    have : Field51_as_Nat fe1 = Field51_as_Nat PP + Field51_as_Nat MM := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have := Nat.ModEq.add h_PP h_MM
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.y_minus_x) this
    apply Nat.ModEq.trans this
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this, add_assoc]
    apply Nat.ModEq.add_left
    rw[← add_mul]
    apply Nat.ModEq.mul_right
    rw[← Nat.ModEq] at h_Y_minus_X; exact h_Y_minus_X
  constructor
  · rw[← Nat.ModEq]
    have : Field51_as_Nat fe2 = Field51_as_Nat Z2 + Field51_as_Nat Txy2d := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have : Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    simp[this, (by scalar_tac : ∀ a, a + a = 2 * a)]
    apply Nat.ModEq.add_left; exact h_Txy2d
  · rw[← Nat.ModEq]; rw[← Nat.ModEq] at fe3_bounds
    have := Nat.ModEq.add_left (Field51_as_Nat fe3) h_Txy2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe3_bounds
    apply Nat.ModEq.trans this
    have : Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this, (by scalar_tac : ∀ a, a + a = 2 * a)]

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
