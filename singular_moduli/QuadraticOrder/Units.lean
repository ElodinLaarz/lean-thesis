import QuadraticOrder.Norm
import QuadraticOrder.Defs.Setup

/-!
# Units of imaginary quadratic orders

**Thesis.** §1.2 (`w_i = #O_{d_i}^×`) and §2.1 — the unit counts
`w ∈ {2, 4, 6}` (with `w = 4` iff `d = −4`, `w = 6` iff `d = −3`) normalize
every `J(d₁,d₂)` exponent in Chapter 2.

**Human-readable companion.** `proofs/infra-units.md`.

**This file states:**

* `units_eq_one_or_neg_one` — `O_d^× = {±1}` for `d < −4`
* `card_units_eq_two` — `#O_d^× = 2` for `d < −4`

**Proof strategy** (WP-A): the norm form is positive definite for `d < 0`
(completed square — see `proofs/infra-units.md` for the exact identity), a
unit has norm-form value `1`, and for `d < −4` the only lattice points of
norm `1` are `±1`.  Mathlib's torsion-unit theory (`NumberField.Units`)
applies only to maximal orders and is not used.

**Status.** WP-A stubs (`sorry`).  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-- For `d < −4` (and `d` a genuine discriminant) the only units of `O_d` are
`±1`.  The excluded discriminants: `d = −4` has `w = 4` (the Gaussian units)
and `d = −3` has `w = 6` (the Eisenstein units). -/
theorem units_eq_one_or_neg_one (hd : d < -4) (hdisc : d % 4 = 0 ∨ d % 4 = 1)
    (u : (QuadraticOrder d)ˣ) : u = 1 ∨ u = -1 := by
  sorry

/-- For `d < −4`: `#O_d^× = 2`. -/
theorem card_units_eq_two (hd : d < -4) (hdisc : d % 4 = 0 ∨ d % 4 = 1) :
    Nat.card (QuadraticOrder d)ˣ = 2 := by
  sorry

end QuadraticOrder
