import QuadraticOrder.Norm
import QuadraticOrder.Prime.ConductorPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at the unique prime over `p ∣ f` (Lemma 3.2.2)

**Thesis.** Lemma 3.2.2 — with the standing hypothesis made explicit
(ERRATA E6.2): `P` is the UNIQUE prime of `O_d` over `p` (true whenever
`p ∣ f`, by `existsUnique_isPrime_mem_of_dvd_conductor`); the lemma is FALSE
for split `p`.

**Human-readable companion.** `proofs/lem-3-2-2.md`.

**This file states:**

* `exists_int_denominator` — every element of `(O_d)_P` is `α/t` with `α ∈ O_d`
  and `t ∈ ℤ` prime to `p` (the thesis's "`O_P = ℤ_(p)[τ]`")
* `isUnit_algebraMap_atPrime_iff_not_dvd_norm` — `x + y·τ` becomes a unit in
  `(O_d)_P` iff `p ∤ N(x + y·τ)`

**Proof strategy** (WP-D): `β·β̄ = N(β) ∈ ℤ`, the norm is the product of local
indices, and `P` being the unique prime over `p` forces `p ∤ β·β̄` for
`β ∉ P`; hence `1/β = β̄/N(β)` has an integer denominator prime to `p`.

**Status.** WP-D stubs (`sorry`).  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- Every element of the localization of `O_d` at the (unique) prime `P` over
`p ∣ f` has an integer denominator prime to `p`:
`z = α / t` with `α ∈ O_d`, `t ∈ ℤ`, `p ∤ t`.  This is the precise content of
the thesis's "`O_P = ℤ_(p)[τ]`". -/
theorem exists_int_denominator [ConductorPrimeSetup d D f p]
    (P : Ideal (QuadraticOrder d)) [P.IsPrime]
    (hP : (p : QuadraticOrder d) ∈ P)
    (z : Localization.AtPrime P) :
    ∃ (α : QuadraticOrder d) (t : ℤ), ¬ (p : ℤ) ∣ t ∧
      z * algebraMap (QuadraticOrder d) (Localization.AtPrime P) (t : QuadraticOrder d) =
        algebraMap (QuadraticOrder d) (Localization.AtPrime P) α := by
  sorry

/-- Invertibility criterion in the localization: for `p ∣ f` and `P` the
unique prime over `p`, the element `x + y·τ` maps to a unit of `(O_d)_P` iff
`p` does not divide its norm `N(x + y·τ) = normForm d x y`.
FALSE for split `p` — the `ConductorPrimeSetup` hypothesis is essential
(ERRATA E6.2). -/
theorem isUnit_algebraMap_atPrime_iff_not_dvd_norm [ConductorPrimeSetup d D f p]
    (P : Ideal (QuadraticOrder d)) [P.IsPrime]
    (hP : (p : QuadraticOrder d) ∈ P) (x y : ℤ) :
    IsUnit (algebraMap (QuadraticOrder d) (Localization.AtPrime P)
        ((x : QuadraticOrder d) + y • tau)) ↔
      ¬ (p : ℤ) ∣ normForm d x y := by
  sorry

end QuadraticOrder
