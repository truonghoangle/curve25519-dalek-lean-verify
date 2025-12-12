/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # Spec Theorem for `AffineNielsPoint::identity`

Specification and proof for the identity point constructor on AffineNielsPoint
used by the serial backend. This file provides specifications matching the Rust code in
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` lines 256-264.

The identity function creates the neutral element for the Edwards curve in affine
Niels coordinates, represented as (y+x, y-x, 2dxy) = (1, 1, 0), which corresponds
to the affine point (0, 1).

Mathematically, this is the identity element of the elliptic curve group, satisfying
P + identity = P for any point P on the curve. For the affine point (x, y) = (0, 1):
- y_plus_x = y + x = 1 + 0 = 1
- y_minus_x = y - x = 1 - 0 = 1
- xy2d = 2dxy = 2d·0·1 = 0
-/

set_option linter.unusedVariables false
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.curve_models

/-- Local mirror of AffineNielsPoint for specification purposes (not extracted).
Represents (y+x, y−x, 2dxy). -/
structure AffineNielsPoint where
  y_plus_x : backend.serial.u64.field.FieldElement51
  y_minus_x : backend.serial.u64.field.FieldElement51
  xy2d : backend.serial.u64.field.FieldElement51

end curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.backend.serial.curve_models.AffineNielsPoint

/- [curve25519_dalek::backend::serial::curve_models::{curve25519_dalek::traits::Identity for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::identity]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 256:4-264:5 -/
/-- Lean extraction of `AffineNielsPoint::identity`.
Returns the identity point (1, 1, 0) in affine Niels coordinates. -/
def identity : Result backend.serial.curve_models.AffineNielsPoint := do
  ok { y_plus_x := FieldElement51.ONE
     , y_minus_x := FieldElement51.ONE
     , xy2d := FieldElement51.ZERO }

/-- Spec for `AffineNielsPoint::identity`:
- No panic (always returns successfully)
- Returns an AffineNielsPoint with y_plus_x = 1, y_minus_x = 1, xy2d = 0 (mod p)
- Represents the affine point (0, 1) in Niels coordinates (y+x, y-x, 2dxy)
- This is the identity element on the Edwards curve
- For the identity point (x, y) = (0, 1): y+x = 1, y-x = 1, 2dxy = 0
-/
@[progress]
theorem identity_spec :
∃ pt,
  identity = ok pt ∧
  Field51_as_Nat pt.y_plus_x % p = 1 ∧
  Field51_as_Nat pt.y_minus_x % p = 1 ∧
  Field51_as_Nat pt.xy2d % p = 0 := by
  unfold identity
  refine ⟨{ y_plus_x := FieldElement51.ONE, y_minus_x := FieldElement51.ONE, xy2d := FieldElement51.ZERO }, ?_⟩
  constructor
  · rfl
  constructor
  · rw [FieldElement51.ONE_spec]; rfl
  constructor
  · rw [FieldElement51.ONE_spec]; rfl
  · rw [FieldElement51.ZERO_spec]; rfl

end curve25519_dalek.backend.serial.curve_models.AffineNielsPoint
