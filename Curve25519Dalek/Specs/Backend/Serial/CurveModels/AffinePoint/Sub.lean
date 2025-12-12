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

/-! # Spec Theorem for `EdwardsPoint - AffineNielsPoint` (Affine subtraction)

Specification and proof for the subtraction of a point in affine Niels coordinates
from an Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹).

This mirrors the Rust implementation at
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` lines 476–493:

impl<'a> Sub<&'a AffineNielsPoint> for &EdwardsPoint { type Output = CompletedPoint; fn sub(..) }

Formulas (with P = (X:Y:Z:T) and N = (y_plus_x, y_minus_x, xy2d)):
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PM        = Y_plus_X  · N.y_minus_x
- MP        = Y_minus_X · N.y_plus_x
- Txy2d     = T · N.xy2d
- Z2        = Z + Z
- X'        = PM − MP
- Y'        = PM + MP
- Z'        = Z2 − Txy2d
- T'        = Z2 + Txy2d
-/

open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models

/-- Local mirror of AffineNielsPoint for specification purposes (not extracted).
Represents (y+x, y−x, 2dxy). -/
structure AffineNielsPoint where
  y_plus_x : backend.serial.u64.field.FieldElement51
  y_minus_x : backend.serial.u64.field.FieldElement51
  xy2d : backend.serial.u64.field.FieldElement51

end curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/- Lean extraction of the affine-Niels subtraction (spec-level function). -/
/-- Subtract an AffineNielsPoint from an EdwardsPoint, returning a CompletedPoint. -/
def sub_affine
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.AffineNielsPoint) :
  Result backend.serial.curve_models.CompletedPoint := do
  let Y_plus_X ← FieldElement51.Add.add self.Y self.X
  let Y_minus_X ← FieldElement51.Sub.sub self.Y self.X
  let PM ← FieldElement51.Mul.mul Y_plus_X other.y_minus_x
  let MP ← FieldElement51.Mul.mul Y_minus_X other.y_plus_x
  let Txy2d ← FieldElement51.Mul.mul self.T other.xy2d
  let Z2 ← FieldElement51.Add.add self.Z self.Z
  let fe ← FieldElement51.Sub.sub PM MP
  let fe1 ← FieldElement51.Add.add PM MP
  let fe2 ← FieldElement51.Sub.sub Z2 Txy2d
  let fe3 ← FieldElement51.Add.add Z2 Txy2d
  ok { X := fe, Y := fe1, Z := fe2, T := fe3 }

/-! ## Specification

Arithmetic is modulo p = 2^255 − 19 on the limb-reconstructed naturals.
- Y_plus_X ≡ Y + X
- Y_minus_X ≡ Y − X
- Z2 ≡ 2·Z
- Txy2d ≡ T · xy2d
- X' ≡ PM − MP
- Y' ≡ PM + MP
- Z' ≡ 2·Z − T·xy2d
- T' ≡ 2·Z + T·xy2d
-/

set_option maxHeartbeats 1000000 in
@[progress]
theorem sub_affine_spec
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
sub_affine self other = ok c ∧
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
(X' + Y * ypx) % p = (((Y + X) * ymx) + X * ypx) % p ∧
(Y' + X * ypx) % p = (((Y + X) * ymx) + Y * ypx) % p ∧
(Z' + T * xy2d) % p = (2 * Z) % p ∧
T' % p = ((2 * Z) + (T * xy2d)) % p := by
  unfold sub_affine
  progress as ⟨Y_plus_X , h_Y_plus_X, Y_plus_X_bounds ⟩
  progress as ⟨Y_minus_X,   Y_minus_X_bounds, h_Y_minus_X⟩
  · intro i hi; exact lt_trans (h_selfY_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_selfX_bounds i hi) (by simp)
  progress as ⟨PM, h_PM, PM_bounds⟩
  · intro i hi; exact lt_trans (h_otherYmX_bounds i hi) (by simp)
  progress as ⟨MP, h_MP, MP_bounds⟩
  · intro i hi; exact lt_trans (Y_minus_X_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_otherYpX_bounds i hi) (by simp)
  progress as ⟨Txy2d, h_Txy2d, Txy2d_bounds⟩
  · intro i hi; exact lt_trans (h_selfT_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (h_otherXY2d_bounds i hi) (by simp)
  progress as ⟨Z2, h_Z2, Z2_bounds⟩
  progress as ⟨fe, h_fe, fe_bounds⟩
  · intro i hi; exact lt_trans (PM_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (MP_bounds i hi) (by simp)
  progress as ⟨fe1, h_fe1, fe1_bounds⟩
  · intro i hi; exact lt_trans (PM_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (MP_bounds i hi) (by simp)
  progress as ⟨fe2, h_fe2, fe2_bounds⟩
  · intro i hi; exact lt_trans (Z2_bounds i hi) (by simp)
  · intro i hi; exact lt_trans (Txy2d_bounds i hi) (by simp)
  have hzz: ∀ i < 5, Z2[i]!.val < 2 ^ 54 := by simp_all
  obtain ⟨fe3, h_fe3_ok, h_fe3, fe3_bounds⟩ := CompletedPoint.add_spec' hzz  Txy2d_bounds
  simp only [h_fe3_ok, bind_tc_ok]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · rw[← Nat.ModEq]; rw[← Nat.ModEq] at fe_bounds
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have := Nat.ModEq.mul_right (Field51_as_Nat other.y_plus_x) h_Y_minus_X
    have := Nat.ModEq.symm (Nat.ModEq.add_left (Field51_as_Nat fe) this)
    rw[add_mul, ← add_assoc] at this
    apply Nat.ModEq.trans this
    apply Nat.ModEq.add_right
    apply Nat.ModEq.symm
    apply Nat.ModEq.trans (Nat.ModEq.symm h_PM)
    apply Nat.ModEq.trans (Nat.ModEq.symm fe_bounds)
    apply Nat.ModEq.add_left
    exact h_MP
  · rw[← Nat.ModEq]
    have : Field51_as_Nat fe1 = Field51_as_Nat PM + Field51_as_Nat MP := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have := Nat.ModEq.add h_PM h_MP
    have := Nat.ModEq.add_right (Field51_as_Nat self.X * Field51_as_Nat other.y_plus_x) this
    apply Nat.ModEq.trans this
    have : Field51_as_Nat self.Y + Field51_as_Nat self.X = Field51_as_Nat Y_plus_X := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this, add_assoc]
    apply Nat.ModEq.add_left
    rw[← add_mul]
    apply Nat.ModEq.mul_right
    rw[← Nat.ModEq] at h_Y_minus_X; exact h_Y_minus_X
  · rw[← Nat.ModEq]
    rw[← Nat.ModEq] at fe2_bounds
    have := Nat.ModEq.add_left (Field51_as_Nat fe2) h_Txy2d
    have := Nat.ModEq.trans (Nat.ModEq.symm this) fe2_bounds
    apply Nat.ModEq.trans this
    have : Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this, (by scalar_tac : ∀ a, a + a = 2 * a)]
  · rw[← Nat.ModEq]
    have : Field51_as_Nat fe3 = Field51_as_Nat Z2 + Field51_as_Nat Txy2d := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    rw[this]
    have : Field51_as_Nat Z2 = Field51_as_Nat self.Z + Field51_as_Nat self.Z := by
      simp[Field51_as_Nat, Finset.sum_range_succ]; simp_all; scalar_tac
    simp[this, (by scalar_tac : ∀ a, a + a = 2 * a)]
    apply Nat.ModEq.add_left; exact h_Txy2d

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
