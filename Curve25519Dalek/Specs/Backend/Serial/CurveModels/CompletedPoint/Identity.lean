/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # Spec Theorem for `CompletedPoint::identity`

Specification and proof for the identity point constructor on CompletedPoint
used by the serial backend. This file provides specifications for constructing the
identity element in completed coordinates (ℙ¹ × ℙ¹).

The identity function creates the neutral element for the Edwards curve in completed
coordinates, represented as ((X:Z), (Y:T)) = ((0:1), (1:1)), which corresponds to the
affine point (0, 1).

Mathematically, this is the identity element of the elliptic curve group, satisfying
P + identity = P for any point P on the curve. In completed coordinates, this is
represented with X = 0, Y = 1, Z = 1, T = 1.

**Source**: Adapted from curve25519-dalek/src/backend/serial/curve_models/mod.rs
            ProjectivePoint::identity implementation (lines 239-248)
-/

set_option linter.unusedVariables false
open Aeneas.Std Result
open curve25519_dalek.backend.serial.u64.field

namespace curve25519_dalek.backend.serial.curve_models.CompletedPoint

/-- Lean extraction of `CompletedPoint::identity`.
Returns the identity point ((0:1), (1:1)) in completed coordinates. -/
def identity : Result backend.serial.curve_models.CompletedPoint := do
  ok { X := FieldElement51.ZERO
     , Y := FieldElement51.ONE
     , Z := FieldElement51.ONE
     , T := FieldElement51.ONE }

/-- Spec for `CompletedPoint::identity`:
- No panic (always returns successfully)
- Returns a CompletedPoint with X = 0, Y = 1, Z = 1, T = 1 (mod p)
- Represents the affine point (0, 1) in completed coordinates ((X:Z), (Y:T))
- This is the identity element on the Edwards curve
- The point ((0:1), (1:1)) maps to (0, 1) under the Segre embedding
-/
@[progress]
theorem identity_spec :
∃ pt,
  identity = ok pt ∧
  Field51_as_Nat pt.X % p = 0 ∧
  Field51_as_Nat pt.Y % p = 1 ∧
  Field51_as_Nat pt.Z % p = 1 ∧
  Field51_as_Nat pt.T % p = 1 := by
  unfold identity
  refine ⟨{ X := FieldElement51.ZERO, Y := FieldElement51.ONE, Z := FieldElement51.ONE, T := FieldElement51.ONE }, ?_⟩
  constructor
  · rfl
  constructor
  · rw [FieldElement51.ZERO_spec]; rfl
  constructor
  · rw [FieldElement51.ONE_spec]; rfl
  constructor
  · rw [FieldElement51.ONE_spec]; rfl
  · rw [FieldElement51.ONE_spec]; rfl

end curve25519_dalek.backend.serial.curve_models.CompletedPoint
