/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `Scalar52::conditional_add_l`

Specification and proof for `Scalar52::conditional_add_l`.

This function conditionally adds the group order L to a scalar based on a boolean-style choice parameter.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar u and a binary condition c.
    • If condition is true (1), adds L to the scalar and returns the result u' and a carry bit;
      if false (0), returns the scalar unchanged.
    • The carry bit represents potential overflow beyond the
      52-bit limb representation.

natural language specs:

    • If condition is 1: scalar_to_nat(u') + (carry * 2^260) = scalar_to_nat(u) + L
    • If condition is 0: scalar_to_nat(u') = scalar_to_nat(u) and carry = 0
-/
/-
 **Spec and proof concerning `scalar.Scalar52.conditional_add_l`**:
- No panic (always returns successfully)
- If condition is true (1), the result represents the input scalar plus L
- If condition is false (0), the result represents the input scalar unchanged
- The carry bit captures any overflow from the 52-bit limb representation
-/

set_option maxHeartbeats 10000000 in
-- progress simp_all is heavy

/-- Spec for one full pass of `conditional_add_l_loop` starting at i = 0 with
zero incoming carry and mask = 2^52 - 1. It states that the routine computes
`u + (c ? L : 0)` modulo 2^(52*5) and returns the final carry word whose upper
bits (above 52) capture the overflow beyond 260 bits. The result limbs are
properly 52-bit bounded.

Formally, if `(carry, u')` is the output of the loop started with zero state, then

  Scalar52_as_Nat u' + 2^(52*5) * (carry.val >>> 52)
    = Scalar52_as_Nat u + (if c.val = 1#u8 then L else 0)

and for all j<5, u'[j]!.val < 2^52.

We keep the proof as a TODO, mirroring the style of other spec files. -/
@[progress]
theorem conditional_add_l_loop_spec
    (u : Scalar52) (c : subtle.Choice) (mask : U64)
    (hmask : mask.val = 2 ^ 52 - 1) :
    ∃ carry u',
      conditional_add_l_loop u c 0#u64 mask 0#usize = ok (carry, u') ∧
      Scalar52_as_Nat u' + 2 ^ (5 * 52) * (carry.val >>> 52)
        = Scalar52_as_Nat u + (if c.val = 1#u8 then L else 0) ∧
      (∀ j < 5, u'[j]!.val < 2 ^ 52) := by
  -- Outline: unfold `conditional_add_l_loop` and proceed by induction on the limb
  -- index, tracking the carry and using the mask hypothesis to show each limb is
  -- reduced modulo 2^52. The arithmetic relation follows from base-2^52 addition
  -- with addend selected as either 0 or L depending on `c`.
  -- TODO: complete proof
  sorry

@[progress]
theorem conditional_add_l_spec (u : Scalar52) (c : subtle.Choice) :
    ∃ carry u',
    conditional_add_l u c = ok (carry, u') ∧
    (c.val = 1#u8 → Scalar52_as_Nat u' + carry.val * 2^260 = Scalar52_as_Nat u + L) ∧
    (c.val = 0#u8 → Scalar52_as_Nat u' = Scalar52_as_Nat u ∧ carry.val = 0)
    := by
  unfold conditional_add_l
  -- TODO: derive from `conditional_add_l_loop_spec` with `mask = 2^52 - 1`
  -- and structural properties of the returned carry.
  sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
