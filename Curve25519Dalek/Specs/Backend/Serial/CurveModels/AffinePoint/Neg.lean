/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg

/-! # Spec Theorem for `Neg` on AffineNielsPoint

Specification and proof for negation on AffineNielsPoint used by the
serial backend. This file provides specifications matching the Rust code in
`curve25519-dalek/src/backend/serial/curve_models/mod.rs` around the
"Negation" section (lines ~513-523), adapted to the extracted Lean functions.

In particular, we cover:

• AffineNielsPoint::neg: swaps y_plus_x and y_minus_x, and negates xy2d.

Mathematically, this corresponds to taking the additive inverse of the cached
product coordinate without changing the cached sums/differences, matching the
Edwards curve negation identities.
-/

set_option linter.unusedVariables false
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

namespace curve25519_dalek.backend.serial.curve_models

/- [curve25519_dalek::backend::serial::curve_models::{core::ops::arith::Neg<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for &1 (curve25519_dalek::backend::serial::curve_models::AffineNielsPoint)}::neg]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 513:4-523:5 -/
/-- Lean extraction of `AffineNielsPoint::neg`.
Returns a new AffineNielsPoint with swapped y_plus_x/y_minus_x and negated xy2d. -/
def AffineNielsPoint.neg
  (self : backend.serial.curve_models.AffineNielsPoint) : Result backend.serial.curve_models.AffineNielsPoint := do
  let xy2d_neg ← backend.serial.u64.field.FieldElement51.neg self.xy2d
  ok { y_plus_x := self.y_minus_x
     , y_minus_x := self.y_plus_x
     , xy2d := xy2d_neg }

/-- Spec for `AffineNielsPoint::neg`:
- No panic (always returns successfully under standard bounds)
- y_plus_x and y_minus_x are swapped (mod p equalities hold trivially)
- xy2d is negated, i.e., xy2d' + xy2d ≡ 0 (mod p)
- Uses the `FieldElement51.neg` spec for the xy2d limb negation. -/
@[progress]
theorem AffineNielsPoint.neg_spec
  (n : backend.serial.curve_models.AffineNielsPoint)
  (h_YpX_bounds : ∀ i, i < 5 → (n.y_plus_x[i]!).val < 2 ^ 54)
  (h_YmX_bounds : ∀ i, i < 5 → (n.y_minus_x[i]!).val < 2 ^ 54)
  (h_xy2d_bounds : ∀ i, i < 5 → (n.xy2d[i]!).val < 2 ^ 54) :
∃ n',
  AffineNielsPoint.neg n = ok n' ∧
  let ypx := Field51_as_Nat n.y_plus_x
  let ymx := Field51_as_Nat n.y_minus_x
  let xy2d := Field51_as_Nat n.xy2d
  let ypx' := Field51_as_Nat n'.y_plus_x
  let ymx' := Field51_as_Nat n'.y_minus_x
  let xy2d' := Field51_as_Nat n'.xy2d
  ypx' % p = ymx % p ∧
  ymx' % p = ypx % p ∧
  (xy2d' + xy2d) % p = 0 := by
  unfold AffineNielsPoint.neg
  obtain ⟨xyneg, h_call, h_xyneg_mod, _⟩ :=
    curve25519_dalek.backend.serial.u64.field.FieldElement51.Neg.neg_spec n.xy2d h_xy2d_bounds
  refine ⟨{ y_plus_x := n.y_minus_x, y_minus_x := n.y_plus_x, xy2d := xyneg }, ?_⟩
  constructor
  · simp [h_call]
  · refine And.intro ?h1 ?hrest
    · simp
    refine And.intro ?h2 ?h3
    · simp
    · have : (Field51_as_Nat n.xy2d + Field51_as_Nat xyneg) % p = 0 := h_xyneg_mod
      simpa [Nat.add_comm] using this

end curve25519_dalek.backend.serial.curve_models
