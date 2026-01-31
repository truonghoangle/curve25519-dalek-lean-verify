/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `differential_add_and_double`

Specification and proof for
`curve25519_dalek::montgomery::differential_add_and_double`.

This function performs the double-and-add step of the Montgomery ladder.
Given projective points (U_P : W_P) = u(P), (U_Q : W_Q) = u(Q), and the
affine difference u_{P-Q} = u(P-Q), it computes u([2]P) and u(P + Q).

**Source**: curve25519-dalek/src/montgomery.rs, lines 351:0-389:1

--/

open Aeneas.Std Result
namespace curve25519_dalek.montgomery

/-
Natural language description:

    • Takes two projective points P and Q on the Montgomery curve (or its twist),
      along with the affine u-coordinate of their difference P-Q.

    • Performs a differential addition and doubling operation:
      - Computes [2]P (the doubling of P)
      - Computes P + Q (the sum of P and Q)

    • This is the core operation of the Montgomery ladder for scalar multiplication.

    • The computation uses the affine difference u(P-Q) to enable the addition
      without needing the full coordinates of both points.

Natural language specs:

    • The function always succeeds (no panic).

    • Returns a pair of projective points: ([2]P, P+Q).

    • The first result has coordinates:
      - U = (U_P + W_P)² · (U_P - W_P)²
      - W = 4·U_P·W_P · ((U_P - W_P)² + ((A+2)/4)·4·U_P·W_P)

    • The second result has coordinates:
      - U = 4·(U_P·U_Q - W_P·W_Q)²
      - W = u(P-Q) · 4·(W_P·U_Q - U_P·W_Q)²
-/

/-- **Spec and proof concerning `montgomery.differential_add_and_double`**:
- No panic (always returns successfully)
- Returns ([2]P, P+Q) as projective points
- Implements the Montgomery ladder double-and-add operation
-/
@[progress]
theorem differential_add_and_double_spec
    (P Q : montgomery.ProjectivePoint)
    (affine_PmQ : backend.serial.u64.field.FieldElement51) :
    ∃ (P' Q' : montgomery.ProjectivePoint),
    montgomery.differential_add_and_double P Q affine_PmQ = ok (P', Q') := by
  unfold montgomery.differential_add_and_double
  sorry

end curve25519_dalek.montgomery
