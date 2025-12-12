/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # Spec Theorem for `Neg` on internal curve models

Specification and proof for negation on internal curve models used by the
serial backend. This file provides specifications matching the Rust code in
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` around the
"Negation" section (lines ~500-511), adapted to the extracted Lean functions.

In particular, we cover:

• ProjectiveNielsPoint::neg: swaps Y_plus_X and Y_minus_X, keeps Z, and
  negates T2d.

Mathematically, this corresponds to taking the additive inverse of the cached
product coordinate without changing the cached sums/differences, matching the
Edwards curve negation identities.
-/

set_option linter.unusedVariables false
open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.curve_models

/- [curve25519_dalek::backend::serial::curve_models::{core::ops::arith::Neg<curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint> for &1 (curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint)}::neg]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 500:4-511:5 -/
/-- Lean extraction of `ProjectiveNielsPoint::neg`.
Returns a new ProjectiveNielsPoint with swapped Y+/Y−, same Z, and negated T2d. -/
def ProjectiveNielsPoint.neg
  (self : ProjectiveNielsPoint) : Result ProjectiveNielsPoint := do
  let T2d_neg ← backend.serial.u64.field.FieldElement51.neg self.T2d
  ok { Y_plus_X := self.Y_minus_X
     , Y_minus_X := self.Y_plus_X
     , Z := self.Z
     , T2d := T2d_neg }

/-- Spec for `ProjectiveNielsPoint::neg`:
- No panic (always returns successfully under standard bounds)
- Y_plus_X and Y_minus_X are swapped (mod p equalities hold trivially)
- Z is unchanged (mod p)
- T2d is negated, i.e., T2d' + T2d ≡ 0 (mod p)
- Uses the `FieldElement51.neg` spec for the T2d limb negation. -/
@[progress]
theorem ProjectiveNielsPoint.neg_spec
  (n : ProjectiveNielsPoint)
  (h_YpX_bounds : ∀ i, i < 5 → (n.Y_plus_X[i]!).val < 2 ^ 54)
  (h_YmX_bounds : ∀ i, i < 5 → (n.Y_minus_X[i]!).val < 2 ^ 54)
  (h_Z_bounds : ∀ i, i < 5 → (n.Z[i]!).val < 2 ^ 54)
  (h_T2d_bounds : ∀ i, i < 5 → (n.T2d[i]!).val < 2 ^ 54) :
∃ n',
  ProjectiveNielsPoint.neg n = ok n' ∧
  let YpX := Field51_as_Nat n.Y_plus_X
  let YmX := Field51_as_Nat n.Y_minus_X
  let Z₀  := Field51_as_Nat n.Z
  let T2d := Field51_as_Nat n.T2d
  let YpX' := Field51_as_Nat n'.Y_plus_X
  let YmX' := Field51_as_Nat n'.Y_minus_X
  let Z'   := Field51_as_Nat n'.Z
  let T2d' := Field51_as_Nat n'.T2d
  YpX' % p = YmX % p ∧
  YmX' % p = YpX % p ∧
  Z'   % p = Z₀  % p ∧
  (T2d' + T2d) % p = 0 := by
  unfold ProjectiveNielsPoint.neg
  obtain ⟨tneg, h_call, h_tneg_mod, _⟩ :=
    curve25519_dalek.backend.serial.u64.field.FieldElement51.Neg.neg_spec n.T2d h_T2d_bounds
  refine ⟨{ Y_plus_X := n.Y_minus_X, Y_minus_X := n.Y_plus_X, Z := n.Z, T2d := tneg }, ?_⟩
  constructor
  · simp [h_call]
  · refine And.intro ?h1 ?hrest
    · simp
    refine And.intro ?h2 ?hrest2
    · simp
    refine And.intro ?h3 ?h4
    · simp
    · have : (Field51_as_Nat n.T2d + Field51_as_Nat tneg) % p = 0 := h_tneg_mod
      simpa [Nat.add_comm] using this

end curve25519_dalek.backend.serial.curve_models
