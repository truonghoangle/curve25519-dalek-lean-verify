/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # Spec Theorem for `ProjectivePoint::identity`

Specification and proof for the identity point constructor on ProjectivePoint
used by the serial backend. This file provides specifications matching the Rust code in
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` lines 229-237.

The identity function creates the neutral element for the Edwards curve in projective
coordinates (ℙ²), represented as (X:Y:Z) = (0:1:1), which corresponds to the affine
point (0, 1).

Mathematically, this is the identity element of the elliptic curve group, satisfying
P + identity = P for any point P on the curve.
-/

set_option linter.unusedVariables false
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/- [curve25519_dalek::backend::serial::curve_models::{curve25519_dalek::traits::Identity for curve25519_dalek::backend::serial::curve_models::ProjectivePoint}::identity]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 229:4-237:5 -/
/-- Lean extraction of `ProjectivePoint::identity`.
Returns the identity point (0:1:1) in projective coordinates. -/
def identity : Result backend.serial.curve_models.ProjectivePoint := do
  ok { X := FieldElement51.ZERO
     , Y := FieldElement51.ONE
     , Z := FieldElement51.ONE }

/-- Spec for `ProjectivePoint::identity`:
- No panic (always returns successfully)
- Returns a ProjectivePoint with X = 0, Y = 1, Z = 1 (mod p)
- Represents the affine point (0, 1), which is the identity element on the Edwards curve
- The resulting point satisfies the Edwards curve equation:
  -x² + y² = 1 + d·x²·y² where x = 0/1 = 0, y = 1/1 = 1
-/
@[progress]
theorem identity_spec :
∃ pt,
  identity = ok pt ∧
  Field51_as_Nat pt.X % p = 0 ∧
  Field51_as_Nat pt.Y % p = 1 ∧
  Field51_as_Nat pt.Z % p = 1 := by
  unfold identity
  refine ⟨{ X := FieldElement51.ZERO, Y := FieldElement51.ONE, Z := FieldElement51.ONE }, ?_⟩
  constructor
  · rfl
  constructor
  · rw [FieldElement51.ZERO_spec]; rfl
  constructor
  · rw [FieldElement51.ONE_spec]; rfl
  · rw [FieldElement51.ONE_spec]; rfl

end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
