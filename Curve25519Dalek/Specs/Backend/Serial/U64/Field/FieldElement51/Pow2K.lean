/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::pow2k`

Specification and proof for `FieldElement51::pow2k`.

This function computes the 2^k-th power of the element.

**Source**: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 10000000000000


/-
natural language description:

    • Computes the 2^k-th power of a field element a in the field 𝔽_p where p = 2^255 - 19
    • The field element is represented as five u64 limbs
    • This generalizes the square operation: applying pow2k(a, k) computes a^(2^k)

natural language specs:

    • The function always succeeds (no panic) when k > 0
    • Field51_as_Nat(result) ≡ Field51_as_Nat(a)^(2^k) (mod p)
    • Each limb of the result is bounded: result[i] < 2^51 for all i < 5
-/

/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.pow2k`**:
- No panic (always returns successfully) when k > 0
- The result, when converted to a natural number, is congruent to the input raised to the (2^k)-th power modulo p
- Each limb of the result is strictly less than 2^51 (maintained by LOW_51_BIT_MASK)
- Note: this generalizes the square operation (square is pow2k with k=1)
-/





lemma bound_prod_2pow54
  {x y : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) :
  x * (19 * y) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' : x ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hy
  have hxy : x * (19 * y) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  -- now combine with global bound
  apply le_trans hxy
  scalar_tac

lemma bound_prod_2pow54I
  {x y : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) :
  x *  y ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' : x ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hy
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  -- now combine with global bound
  apply le_trans hxy
  scalar_tac



lemma bound_prod_add_2pow54
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  x * (19 * y) + u * (19 * v) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' := Nat.le_pred_of_lt hx
  have hy' := Nat.le_pred_of_lt hy
  have hu' := Nat.le_pred_of_lt hu
  have hv' := Nat.le_pred_of_lt hv
  have hxy : x * (19 * y) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : x * (19 * y) +  u * (19 * v) ≤ 2*(2^54 - 1)^2 * 19 := by
    apply le_trans (add_le_add hxy huv)
    scalar_tac
  apply le_trans hxyuv
  scalar_tac


lemma bound_prod_add_2pow54I
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  x  * y + u * (19 * v) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' := Nat.le_pred_of_lt hx
  have hy' := Nat.le_pred_of_lt hy
  have hu' := Nat.le_pred_of_lt hu
  have hv' := Nat.le_pred_of_lt hv
  have hxy : x  * y ≤ (2 ^ 54 - 1)  * (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx'  hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : x  * y +  u * (19 * v) ≤ 2*(2^54 - 1)^2 * 19 := by
    apply le_trans (add_le_add hxy huv)
    scalar_tac
  apply le_trans hxyuv
  scalar_tac

lemma bound_prod_add_2pow54II
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  x  * y + u *  v ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' := Nat.le_pred_of_lt hx
  have hy' := Nat.le_pred_of_lt hy
  have hu' := Nat.le_pred_of_lt hu
  have hv' := Nat.le_pred_of_lt hv
  have hxy : x  * y ≤ (2 ^ 54 - 1)  * (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx'  hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : x  * y +  u *  v ≤ 2*(2^54 - 1)^2 * 19 := by
    apply le_trans (add_le_add hxy huv)
    scalar_tac
  apply le_trans hxyuv
  scalar_tac



lemma bound_2prod_add_2pow54
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  2 * (x * (19 * y) + u * (19 * v)) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' : x ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hy
  have hu' : u ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hu
  have hv' : v ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hv
  have hxy : x * (19 * y) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x * (19 * y) +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  apply le_trans hxyuv
  scalar_tac





lemma bound_2prod_add_2pow54I
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  2 * (x *  y + u * (19 * v)) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' : x ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hy
  have hu' : u ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hu
  have hv' : v ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hv
  have hxy : x  * y ≤ (2 ^ 54 - 1) * (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *   y +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  apply le_trans hxyuv
  scalar_tac


lemma bound_2prod_add_2pow54II
  {x y u v : ℕ} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  2 * (x *  y + u *  v) ≤ (2 ^ 128 - 1 : ℕ) := by
  have hx' : x ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hy
  have hu' : u ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hu
  have hv' : v ≤ 2 ^ 54 - 1 := Nat.le_pred_of_lt hv
  have hxy : x  * y ≤ (2 ^ 54 - 1) * (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *   y +  u *  v) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  apply le_trans hxyuv
  scalar_tac





lemma bound_add_2prod_add_2pow54
  {a x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  a * a + 2 * (x * (19 * y) + u * (19 * v)) ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x * (19 * y) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x * (19 * y) +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * a ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul ha' ha'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a * a + 2 * (x * (19 * y) +  u * (19 * v)) ≤(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  apply le_trans haxyuv
  scalar_tac



lemma bound_add_2prod_add_2pow54I
  {a x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  a * (19 * a) + 2 * (x *  y + u * (19 * v)) ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * (19 * a) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 ha')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a *(19* a) + 2 * (x *  y +  u * (19 * v)) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  apply le_trans haxyuv
  scalar_tac



lemma bound_add_2prod_add_2pow54II
  {a x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  a *  a + 2 * (x *  y + u * (19 * v)) ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u * (19 * v) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a *  a ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul ha' ha'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a * a + 2 * (x *  y +  u * (19 * v)) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  apply le_trans haxyuv
  scalar_tac



lemma bound_add_2prod_addr_2pow54I
  {a x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  a * (19 * a) + 2 * (x *  y + u *  v) ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u *   v) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * (19 * a) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 ha')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a *(19* a) + 2 * (x *  y +  u *  v) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  apply le_trans haxyuv
  scalar_tac




lemma bound_add_2prod_three_add_2pow
  {a b x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) (hb : b < 2 ^ 64) :
  a * (19 * a) + 2 * (x *  y + u *  v) + b ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hb'  := Nat.le_pred_of_lt hb
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u *   v) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * (19 * a) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 ha')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a *(19* a) + 2 * (x *  y +  u *  v) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  have haxyuv : a *(19* a) + 2 * (x *  y +  u *  v) + b ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 + (2 ^ 64 - 1):= by
    have hK := Nat.add_le_add  haxyuv hb'
    apply le_trans hK
    norm_num
  apply le_trans haxyuv
  scalar_tac





lemma bound_add_2prod_threer_add_2pow
  {a b x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) (hb : b < 2 ^ 64) :
  a *  a + 2 * (x *  y + u *  v) + b ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hb'  := Nat.le_pred_of_lt hb
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u *   v) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a *  a ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul ha' ha'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a * a + 2 * (x *  y +  u *  v) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  have haxyuv : a * a + 2 * (x *  y +  u *  v) + b ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 + (2 ^ 64 - 1):= by
    have hK := Nat.add_le_add  haxyuv hb'
    apply le_trans hK
    norm_num
  apply le_trans haxyuv
  scalar_tac


lemma bound_add_2prod_three_add_2powI
  {a b x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) (hb : b < 2 ^ 64) :
  a * (19 * a) + 2 * (x *  y + u * (19* v)) + b ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hb'  := Nat.le_pred_of_lt hb
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  (19 * v) ≤ (2 ^ 54 - 1) *  (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * (19 * a) ≤ (2 ^ 54 - 1) * (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 ha')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a *(19* a) + 2 * (x *  y +  u * (19 * v)) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  have haxyuv : a *(19* a) + 2 * (x *  y +  u * (19 * v)) + b ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 + (2 ^ 64 - 1):= by
    have hK := Nat.add_le_add  haxyuv hb'
    apply le_trans hK
    norm_num
  apply le_trans haxyuv
  scalar_tac






lemma bound_add_2prod_threer_add_2powI
  {a b x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) (hb : b < 2 ^ 64) :
  a *  a + 2 * (x *  y + u * (19* v)) + b ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hb'  := Nat.le_pred_of_lt hb
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  (19 * v) ≤ (2 ^ 54 - 1) *  (19 * (2 ^ 54 - 1)) := by
    have := Nat.mul_le_mul hu' (Nat.mul_le_mul_left 19 hv')
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u * (19 * v)) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a * a ≤ (2 ^ 54 - 1) * (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul ha' ha'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a * a + 2 * (x *  y +  u * (19 * v)) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  have haxyuv : a * a + 2 * (x *  y +  u * (19 * v)) + b ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 + (2 ^ 64 - 1):= by
    have hK := Nat.add_le_add  haxyuv hb'
    apply le_trans hK
    norm_num
  apply le_trans haxyuv
  scalar_tac


lemma bound_add_2prod_addr_2pow54II
  {a x y u v : ℕ} (ha : a < 2 ^ 54) (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) (hu : u < 2 ^ 54) (hv : v < 2 ^ 54) :
  a *  a + 2 * (x *  y + u *  v) ≤ (2 ^ 128 - 1 : ℕ) := by
  have ha'  := Nat.le_pred_of_lt ha
  have hx'  := Nat.le_pred_of_lt hx
  have hy'  := Nat.le_pred_of_lt hy
  have hu'  := Nat.le_pred_of_lt hu
  have hv'  := Nat.le_pred_of_lt hv
  have hxy : x *  y ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hx' hy'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have huv : u *  v ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul hu' hv'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this
  have hxyuv : 2 * (x *  y +  u *   v) ≤ 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.mul_le_mul_left 2 (add_le_add hxy huv)
    apply le_trans hK
    scalar_tac
  have haa : a *  a ≤ (2 ^ 54 - 1) *  (2 ^ 54 - 1) := by
    have := Nat.mul_le_mul ha' ha'
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, pow_two] using this

  have haxyuv : a * a + 2 * (x *  y +  u *  v) ≤19*(2^54 - 1)^2  + 2*2*(2^54 - 1)^2 * 19 := by
    have hK := Nat.add_le_add haa hxyuv
    apply le_trans hK
    scalar_tac
  apply le_trans haxyuv
  scalar_tac





lemma one_le_cases {k : ℕ} (hk : 1 ≤ k) :
    k = 1 ∨ 2 ≤ k := by
  scalar_tac


lemma band_le_left (a b : Nat) : a &&& b ≤ a := by
  sorry

lemma band_le_right (a b : Nat) : a &&& b ≤ b := by
  sorry


lemma low_51_bit_eq : pow2k.LOW_51_BIT_MASK.val = 2 ^51-1 := by
   unfold pow2k.LOW_51_BIT_MASK pow2k.LOW_51_BIT_MASK_body eval_global
   rfl






lemma mod_lt_of_lt_of_lt {a b c : ℕ}
    (hcb : c < b) (hac : a < c) :
    a % b < c := by
  -- from c < b and a < c we get a < b
  have hab : a < b := lt_trans hac hcb
  -- for naturals, if a < b then a % b = a
  have hmod : a % b = a := Nat.mod_eq_of_lt hab
  -- now rewrite and use a < c
  simpa [hmod] using hac


theorem land_pow_two_sub_one_eq_mod (a n : Nat) :
    a &&& (2^n - 1) = a % 2^n := by
  induction n generalizing a
  . simp
    scalar_tac
  . simp




@[progress]
theorem pow2k_spec (a : Array U64 5#usize) (k : U32) (hk : 0 < k.val) (h_bounds : ∀ i, i < 5 → a[i]!.val < 2 ^ 54) :
    ∃ r, pow2k a k = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
    (∀ i : Nat, i < 5 → r[i]!.val < 2^51)
    := by
  have h_bounds_a0:= h_bounds 0 (by simp)
  have h_bounds_a1:= h_bounds 1 (by simp)
  have h_bounds_a2:= h_bounds 2 (by simp)
  have h_bounds_a3:= h_bounds 3 (by simp)
  have h_bounds_a4:= h_bounds 4 (by simp)
  unfold pow2k pow2k_loop
  progress
  progress as ⟨ a3, ha3⟩
  progress as ⟨ am3, ham3⟩
  progress as ⟨ a4, ha4⟩
  progress as ⟨ am4, ham4⟩
  progress as ⟨ a0, ha0⟩
  unfold backend.serial.u64.field.FieldElement51.pow2k.m
  progress as ⟨ ac0, hac0⟩
  progress as ⟨ ap0, hap0⟩
  . simp[hac0]
    scalar_tac
  progress as ⟨ a1, ha1⟩
  progress as ⟨ ac1, hac1⟩
  progress as ⟨ a1a4, ha1a4⟩
  progress as ⟨ m14, hm14⟩
  . have :=bound_prod_2pow54 h_bounds_a1 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ a2, ha2⟩
  progress as ⟨ ac2, hac2⟩
  progress as ⟨ amc3, hamc3⟩
  progress as ⟨ m23, hm23⟩
  . have :=bound_prod_2pow54 h_bounds_a2 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d1423, hd1423⟩
  . have := bound_prod_add_2pow54 h_bounds_a1 h_bounds_a4 h_bounds_a2 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d1, hd1⟩
  . have := bound_2prod_add_2pow54 h_bounds_a1 h_bounds_a4 h_bounds_a2 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ da1, hda1⟩
  . have := bound_add_2prod_add_2pow54 h_bounds_a0 h_bounds_a1 h_bounds_a4 h_bounds_a2 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ a30, ha30⟩
  progress as ⟨ m33, hm33⟩
  . have :=bound_prod_2pow54 h_bounds_a3 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m01, hm01⟩
  . have :=bound_prod_2pow54I h_bounds_a0 h_bounds_a1
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m24, hm24⟩
  . have :=bound_prod_2pow54 h_bounds_a2 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d0124, hd0124⟩
  . have :=bound_prod_add_2pow54I h_bounds_a0 h_bounds_a1 h_bounds_a2 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d2, hd2⟩
  . have :=bound_2prod_add_2pow54I h_bounds_a0 h_bounds_a1 h_bounds_a2 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ da2, hda2⟩
  . have :=bound_add_2prod_add_2pow54I h_bounds_a3 h_bounds_a0 h_bounds_a1 h_bounds_a2 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m11, hm11⟩
  . have :=bound_prod_2pow54I h_bounds_a1 h_bounds_a1
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m02, hm02⟩
  . have :=bound_prod_2pow54I h_bounds_a0 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ ac4, hac4⟩
  progress as ⟨ m43, hm43⟩
  . have :=bound_prod_2pow54 h_bounds_a4 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d0243, hd0243⟩
  . have :=bound_prod_add_2pow54I h_bounds_a0 h_bounds_a2 h_bounds_a4 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d3, hd3⟩
  . have :=bound_2prod_add_2pow54I h_bounds_a0 h_bounds_a2 h_bounds_a4 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ da3, hda3⟩
  . have :=bound_add_2prod_add_2pow54II h_bounds_a1 h_bounds_a0 h_bounds_a2 h_bounds_a4 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m44, hm44⟩
  . have :=bound_prod_2pow54 h_bounds_a4 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m03, hm03⟩
  . have :=bound_prod_2pow54I h_bounds_a0 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m12, hm12⟩
  . have :=bound_prod_2pow54I h_bounds_a1 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d0312, hd0312⟩
  . have :=bound_prod_add_2pow54II h_bounds_a0 h_bounds_a3 h_bounds_a1 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d4, hd4⟩
  . have :=bound_2prod_add_2pow54II h_bounds_a0 h_bounds_a3 h_bounds_a1 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ da4, hda4⟩
  . have :=bound_add_2prod_addr_2pow54I h_bounds_a4 h_bounds_a0 h_bounds_a3 h_bounds_a1 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m22, hm22⟩
  . have :=bound_prod_2pow54I h_bounds_a2 h_bounds_a2
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m04, hm04⟩
  . have :=bound_prod_2pow54I h_bounds_a0 h_bounds_a4
    simp_all[U128.max, U128.numBits]
  progress as ⟨ m13, hm13⟩
  . have :=bound_prod_2pow54I h_bounds_a1 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d0413, hd0413⟩
  . have :=bound_prod_add_2pow54II h_bounds_a0 h_bounds_a4 h_bounds_a1 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ d5, hd5⟩
  . have :=bound_2prod_add_2pow54II h_bounds_a0 h_bounds_a4 h_bounds_a1 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ da5, hda5⟩
  . have :=bound_add_2prod_addr_2pow54II h_bounds_a2 h_bounds_a0 h_bounds_a4 h_bounds_a1 h_bounds_a3
    simp_all[U128.max, U128.numBits]
  progress as ⟨ u, hu, hu_bv⟩
  have ha0u: a0<u := by
    simp_all[U64.size, U64.numBits]
  have ha1u: a1<u := by
    simp_all[U64.size, U64.numBits]
  have ha2u: a2<u := by
    simp_all[U64.size, U64.numBits]
  have ha3u: a3<u := by
    simp_all[U64.size, U64.numBits]
  have ha4u: a4<u := by
    simp_all[U64.size, U64.numBits]
  simp[ha0u,ha1u, ha2u, ha3u, ha4u]
  progress as ⟨ s1, hs1, hs1_bv⟩
  progress as ⟨ sa1, hsa1⟩
  progress as ⟨ sca1, hsca1⟩
  progress as ⟨ aa1, haa1⟩
  . have := @Nat.mod_lt s1.val (2 ^ 64) (by simp)
    have :=bound_add_2prod_three_add_2powI h_bounds_a3 h_bounds_a0 h_bounds_a1 h_bounds_a2 h_bounds_a4 this
    simp_all[U128.max, U128.numBits, UScalar.cast_val_eq,UScalarTy.numBits]
  progress as ⟨ s2, hs2⟩
  progress as ⟨ sa2, hsa2, hsa2_bv⟩
  progress as ⟨ ud, hud⟩
  progress as ⟨ s3, hs3, hs3_bv⟩
  progress as ⟨ sa3, hsa3⟩
  progress as ⟨ sca3, hsca3⟩
  progress as ⟨ aa2, haa2⟩
  . have := @Nat.mod_lt s3.val (2 ^ 64) (by simp)
    have :=bound_add_2prod_threer_add_2powI h_bounds_a1 h_bounds_a0 h_bounds_a2 h_bounds_a4 h_bounds_a3 this
    simp_all[U128.max, U128.numBits, UScalar.cast_val_eq,UScalarTy.numBits]
  progress as ⟨ s4, hs4⟩
  progress as ⟨ sa4, hsa4, hsa4_bv⟩
  progress as ⟨ ud1, hud1⟩
  progress as ⟨ s5, hs5, hs5_bv⟩
  progress as ⟨ sa5, hsa5⟩
  progress as ⟨ sca5, hsca5⟩
  progress as ⟨ aa3, haa3⟩
  . have := @Nat.mod_lt s5.val (2 ^ 64) (by simp)
    have :=bound_add_2prod_three_add_2pow h_bounds_a4 h_bounds_a0 h_bounds_a3 h_bounds_a1 h_bounds_a2 this
    simp_all[U128.max, U128.numBits, UScalar.cast_val_eq,UScalarTy.numBits]
  progress as ⟨ s6, hs6⟩
  progress as ⟨ sa6, hsa6, hsa6_bv⟩
  progress as ⟨ ud2, hud2⟩
  progress as ⟨ s7, hs7, hs7_bv⟩
  progress as ⟨ sa7, hsa7⟩
  progress as ⟨ sca7, hsca7⟩
  progress as ⟨ aa4, haa4⟩
  . have := @Nat.mod_lt s7.val (2 ^ 64) (by simp)
    have :=bound_add_2prod_threer_add_2pow h_bounds_a2 h_bounds_a0 h_bounds_a4 h_bounds_a1 h_bounds_a3 this
    simp_all[U128.max, U128.numBits, UScalar.cast_val_eq,UScalarTy.numBits]
  progress as ⟨ s8, hs8⟩
  progress as ⟨ sa8, hsa8, hsa8_bv⟩
  progress as ⟨ ud3, hud3⟩
  progress as ⟨ s9, hs9, hs9_bv⟩
  progress as ⟨ sa9, hsa9⟩
  progress as ⟨ sca9, hsca9⟩
  progress as ⟨ saa9, hsaa9, hsaa9_bv⟩
  progress as ⟨ ud4, hud4⟩
  have hs1_lt : s1.val < 2 ^ UScalarTy.U64.numBits:= by
    rw[hs1, Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    set con:= 2*(19* (2 ^ 54).pred * (2 ^ 54).pred+ 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (2 ^ 54).pred))/ 2 ^ 51 with hcon
    rw[hda1]
    have h₂₀:=  (Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a0) (Nat.le_pred_of_lt h_bounds_a0))
    have h₂₁: d1.val ≤  2 ^ 51 * 2* con - (2 ^ 54-1)* (2 ^ 54-1):= by
     have ha'  := Nat.le_pred_of_lt h_bounds_a1
     have hb'  := Nat.le_pred_of_lt h_bounds_a4
     have hx'  := Nat.le_pred_of_lt h_bounds_a2
     have hy'  := Nat.le_pred_of_lt h_bounds_a3
     have hay:= Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 hb')
     have hbx:= Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
     have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
     simp_all
     apply le_trans hK
     simp
    have :=Nat.add_le_add h₂₀ h₂₁
    simp_all
    apply Nat.lt_succ_of_le
    apply le_trans this
    simp
  have hsa1_lt : sa1.val <  2 ^ UScalarTy.U128.numBits        := by
    have := Nat.mod_eq_of_lt hs1_lt
    rw[hsa1, UScalar.cast_val_eq, this ]
    apply lt_trans hs1_lt
    simp
  have hsa9_le: sa9.val ≤ (2 ^ 64- 2 ^ 51)/19 := by
     rw[hsa9,UScalar.cast_val_eq]
     have hs9_le: s9.val ≤ (2 ^ 64- 2 ^ 51) /19 := by
      rw[hs9, Nat.shiftRight_eq_div_pow]
      apply Nat.div_le_of_le_mul
      rw[haa4]
      set con:= 2*(19* (2 ^ 54).pred * (2 ^ 54).pred+ 2 * ((2 ^ 54).pred * (2 ^ 54).pred + (2 ^ 54).pred * (2 ^ 54).pred))/ 2 ^ 51 with hcon
      have h₁: da5.val ≤ 2 ^ 51 * ((2 ^ 64- 2 ^ 51)/19)-con := by ---b
        rw[hda5]
        have h₁₀:= Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a2) (Nat.le_pred_of_lt h_bounds_a2)
        have h₁₁: d5.val ≤  2 ^ 51 * ((2 ^ 64- 2 ^ 51)/19)- con - (2 ^ 54-1)* (2 ^ 54-1):= by
          have ha'  := Nat.le_pred_of_lt h_bounds_a0
          have hb'  := Nat.le_pred_of_lt h_bounds_a1
          have hx'  := Nat.le_pred_of_lt h_bounds_a3
          have hy'  := Nat.le_pred_of_lt h_bounds_a4
          have hay:= Nat.mul_le_mul ha' hy'
          have hbx:= Nat.mul_le_mul hb' hx'
          have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
          simp_all
          apply le_trans hK
          simp

        have :=Nat.add_le_add h₁₀ h₁₁
        simp_all

      have h₂: sca7.val ≤ con := by
        rw[hsca7,UScalar.cast_val_eq, Nat.mod_eq_of_lt, hsa7, UScalar.cast_val_eq, Nat.mod_eq_of_lt, hs7, Nat.shiftRight_eq_div_pow]
        apply Nat.div_le_of_le_mul
        rw[haa3]
        have h₃: da4.val ≤2 ^ 51 * con -2 * con  := by
         rw[hda4]
         have h₂₀:=  (Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a4) (Nat.mul_le_mul_left 19 (Nat.le_pred_of_lt h_bounds_a4)))
         have h₂₁: d4.val ≤  2 ^ 51 * con - 2 *con - 19*(2 ^ 54-1)* (2 ^ 54-1):= by
          have ha'  := Nat.le_pred_of_lt h_bounds_a0
          have hb'  := Nat.le_pred_of_lt h_bounds_a3
          have hx'  := Nat.le_pred_of_lt h_bounds_a1
          have hy'  := Nat.le_pred_of_lt h_bounds_a2
          have hay:= Nat.mul_le_mul ha' hb'
          have hbx:= Nat.mul_le_mul hx' hy'
          have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
          simp_all
          apply le_trans hK
          simp

         have :=Nat.add_le_add h₂₀ h₂₁
         simp_all
        have h₄: sca5.val ≤ 2 * con := by
         rw[hsca5,UScalar.cast_val_eq, Nat.mod_eq_of_lt, hsa5, UScalar.cast_val_eq, Nat.mod_eq_of_lt, hs5, Nat.shiftRight_eq_div_pow]
         apply Nat.div_le_of_le_mul
         rw[haa2]
         have h₅: da3.val ≤2 ^ 51 * con  := by
          rw[hda3]
          have h₂₀:=  (Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a1) (Nat.le_pred_of_lt h_bounds_a1))
          have h₂₁: d3.val ≤  2 ^ 51 * con - (2 ^ 54-1)* (2 ^ 54-1):= by
            have ha'  := Nat.le_pred_of_lt h_bounds_a0
            have hb'  := Nat.le_pred_of_lt h_bounds_a2
            have hx'  := Nat.le_pred_of_lt h_bounds_a4
            have hy'  := Nat.le_pred_of_lt h_bounds_a3
            have hay:= Nat.mul_le_mul ha' hb'
            have hbx:= Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
            have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
            simp_all
            apply le_trans hK
            simp
          have :=Nat.add_le_add h₂₀ h₂₁
          simp_all
         have h₆: sca3.val ≤ 2 ^ 51 * con  := by
           rw[hsca3,UScalar.cast_val_eq, Nat.mod_eq_of_lt, hsa3, UScalar.cast_val_eq, Nat.mod_eq_of_lt, hs3, Nat.shiftRight_eq_div_pow]
           apply Nat.div_le_of_le_mul
           rw[haa1]
           have h₇ : da2.val ≤ 2  *(2 ^ 51 * con)-con  := by
            rw[hda2]
            have h₂₀:=  (Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a3) (Nat.mul_le_mul_left 19 (Nat.le_pred_of_lt h_bounds_a3)))
            have h₂₁: d2.val ≤  2 ^ 51 * con - (2 ^ 54-1)* (2 ^ 54-1):= by
             have ha'  := Nat.le_pred_of_lt h_bounds_a0
             have hb'  := Nat.le_pred_of_lt h_bounds_a1
             have hx'  := Nat.le_pred_of_lt h_bounds_a2
             have hy'  := Nat.le_pred_of_lt h_bounds_a4
             have hay:= Nat.mul_le_mul ha' hb'
             have hbx:= Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
             have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
             simp_all
             apply le_trans hK
             simp
            have :=Nat.add_le_add h₂₀ h₂₁
            simp_all
            apply le_trans this
            simp
           have h₈ : sca1.val ≤ 2*con  := by
            rw[hsca1,UScalar.cast_val_eq, Nat.mod_eq_of_lt, hsa1, UScalar.cast_val_eq, Nat.mod_eq_of_lt, hs1, Nat.shiftRight_eq_div_pow]
            apply Nat.div_le_of_le_mul
            rw[hda1]
            have h₂₀:=  (Nat.mul_le_mul (Nat.le_pred_of_lt h_bounds_a0) (Nat.le_pred_of_lt h_bounds_a0))
            have h₂₁: d1.val ≤  2 ^ 51 * 2* con - (2 ^ 54-1)* (2 ^ 54-1):= by
             have ha'  := Nat.le_pred_of_lt h_bounds_a1
             have hb'  := Nat.le_pred_of_lt h_bounds_a4
             have hx'  := Nat.le_pred_of_lt h_bounds_a2
             have hy'  := Nat.le_pred_of_lt h_bounds_a3
             have hay:= Nat.mul_le_mul ha' (Nat.mul_le_mul_left 19 hb')
             have hbx:= Nat.mul_le_mul hx' (Nat.mul_le_mul_left 19 hy')
             have hK := Nat.mul_le_mul_left 2 (Nat.add_le_add hay hbx)
             simp_all
             apply le_trans hK
             simp
            have :=Nat.add_le_add h₂₀ h₂₁
            simp_all
            apply hs1_lt
            apply hsa1_lt
           have := Nat.add_le_add h₇ h₈
           apply le_trans this
           scalar_tac
         have := Nat.add_le_add h₅ h₆
         apply le_trans this
         scalar_tac
        have := Nat.add_le_add h₃ h₄
        apply le_trans this
        scalar_tac
      have :=Nat.add_le_add h₁ h₂
      apply le_trans this
      simp_all
     scalar_tac

  progress as ⟨ aa5, haa5⟩
  progress as ⟨ud40, hud40⟩
  have ud40_le:ud40.val ≤ 2 ^51:= by
     simp[hud40, hud4, hud3, hud2, hud1, hud, hsa2]
     apply le_trans (band_le_right s2.val (pow2k.LOW_51_BIT_MASK).val)
     simp[low_51_bit_eq]
  progress as ⟨aa6, haa6⟩
  progress as ⟨ud5, hud5⟩
  progress as ⟨ud50, hud50⟩
  progress as ⟨sud, hsud, hsud_bv⟩
  progress as ⟨ud51, hud51⟩
  have ud51_le:ud51.val ≤  2^51 := by
     simp[hud51, hud5, hud4, hud3, hud2, hud1, hsa4]
     apply le_trans (band_le_right s4.val (pow2k.LOW_51_BIT_MASK).val)
     simp[low_51_bit_eq]
  progress as ⟨aa7, haa7⟩
  progress as ⟨udu1, hudu1⟩
  progress as ⟨ud10, hud10⟩
  progress as ⟨uda, huda, huda_bv⟩
  progress as ⟨udm, hudm⟩
  progress as ⟨udms, hudms, hudms_bv⟩
  rcases (one_le_cases hudms_bv) with h₁ | h₂
  simp[h₁] at hudms
  have :udms = 0#u32 := by scalar_tac
  simp[this, h₁]
  constructor
  rw[Field51_as_Nat, Field51_as_Nat]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
  simp[hudu1, haa7, hud51]

  --simp_all[UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow]
  have : uda.val = ud10.val &&& (2 ^ 51 -1):= by
   simp[huda, low_51_bit_eq]
  have udac: uda.val = ud10.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod
  have : saa9.val = sca9.val &&& (2 ^ 51 - 1) := by
    simp[hsaa9,low_51_bit_eq]
  have saa9c: saa9.val = sca9.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod
  have : sa8.val = s8.val &&& (2 ^ 51 - 1) := by
    simp[hsa8,low_51_bit_eq]
  have sa8c: sa8.val = s8.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod
  have : sa6.val = s6.val &&& (2 ^ 51 - 1) := by
    simp[hsa6,low_51_bit_eq]
  have sa6c: sa6.val = s6.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod
  have : sa4.val = s4.val &&& (2 ^ 51 - 1) := by
    simp[hsa4,low_51_bit_eq]
  have sa4c: sa4.val = s4.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod
  have : sa2.val = s2.val &&& (2 ^ 51 - 1) := by
    simp[hsa2,low_51_bit_eq]
  have sa2c: sa2.val = s2.val % 2 ^ 51 := by
   rw[this]
   apply land_pow_two_sub_one_eq_mod


  simp[udac, hud10, hud5, hud4, hud3, saa9c, sa8c, hud2, sa6c,
  hud1, sa4c, hsud, hud50, haa6, hudu1, hud40, hud,
   sa2c, hs2, UScalar.cast_val_eq, hda1, hap0, haa5, hs6, haa2,
   hs8, hsca9, hsca3, hsa3, hs3,hda3,hsa9, hs9, hs4, haa4, hda5, hsca7, hsa7]


  sorry












  . intro i hi
    cases i
    simp[huda]
    apply lt_of_le_of_lt (band_le_right ud10.val (pow2k.LOW_51_BIT_MASK).val)
    simp[low_51_bit_eq ]
    rename_i i
    cases i
    simp[hudu1, haa7, hud51, hud5, hud4,hud3, hud2, hud1]
    have : sa4.val = s4.val &&& (2 ^ 51 - 1) := by
      simp[hsa4,low_51_bit_eq]
    have sa4c: sa4.val = s4.val % 2 ^ 51 := by
     rw[this]
     apply land_pow_two_sub_one_eq_mod
    rw[sa4c]
    simp[hs4, UScalar.cast_val_eq, hsud, haa1]
    sorry





    rename_i i
    cases i
    simp[hudu1, hud5, hud4, hud3, hud2, hsa6]
    apply lt_of_le_of_lt (band_le_right s6.val (pow2k.LOW_51_BIT_MASK).val)
    simp[low_51_bit_eq ]
    rename_i i
    cases i
    simp[hudu1, hud5, hud4, hud3, hud2, hsa8]
    apply lt_of_le_of_lt (band_le_right s8.val (pow2k.LOW_51_BIT_MASK).val)
    simp[low_51_bit_eq ]
    rename_i i
    cases i
    simp[hudu1, hud5, hud4, hud3, hud2, hsaa9]
    apply lt_of_le_of_lt (band_le_right sca9.val (pow2k.LOW_51_BIT_MASK).val)
    simp[low_51_bit_eq ]
    rename_i i
    cases i
    simp at hi
    rename_i i
    scalar_tac

  have : udms ≠  0#u32 := by
   intro h
   simp_all
   have hk1 : (↑k : ℕ) = 1 := by
    have := Nat.sub_eq_zero_iff_le.mp hudms
    have h_le1 : (↑k : ℕ) ≤ 1 := this
    exact le_antisymm h_le1 hudms_bv
   rw[hk1] at h₂
   simp_all
  simp[this]
































































































end curve25519_dalek.backend.serial.u64.field.FieldElement51
