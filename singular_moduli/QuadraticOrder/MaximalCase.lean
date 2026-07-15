import QuadraticOrder.Defs.Counting
import QuadraticOrder.Prime

/-!
# Ideal counts in the maximal order (Proposition 3.1.1)

**Thesis.** Proposition 3.1.1: for the maximal order `O_K` (here:
`QuadraticOrder D` with `D` a fundamental discriminant) and a rational prime
`p`, the number of ideals of norm `p^m` is `m + 1` / `1` / `0` according to
the splitting of `p`.

**Human-readable companion.** `proofs/prop-3-1-1.md`.

**This file states** (`p`-uniformly, via `kroneckerAtPrime`):

* `maximalIdealCount_split`    — `(D/p) = 1`:  count `= m + 1`
* `maximalIdealCount_inert`    — `(D/p) = −1`: count `= 1` if `m` even, `0` if odd
* `maximalIdealCount_ramified` — `(D/p) = 0`:  count `= 1`

**Divergence from thesis.** Stated without `D < 0` — the proposition holds in
any quadratic field's maximal order (ERRATA E6.9); negativity is nowhere used.

**Proof strategy** (WP-E): `QuadraticOrder D` is the ring of integers of
`ℚ(√D)` for fundamental `D` (this identification is part of the package),
hence a Dedekind domain: unique factorization of ideals reduces the count to
factoring `(p)` per the trichotomy (Prime/ files), and the ideals of norm
`p^m` are `𝔭₁^i·𝔭₂^{m−i}` (split), `𝔭^{m/2}` (inert, `m` even), `𝔭^m`
(ramified).  Mathlib's `Ideal.absNorm`/`UniqueFactorizationMonoid` machinery
IS legitimate here — the order is maximal.

**Status.** WP-E stubs (`sorry`).  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {D : ℤ} {p : ℕ}

/-- **Proposition 3.1.1, split case.**  `D` fundamental, `(D/p) = 1`:
there are exactly `m + 1` ideals of norm `p^m` in the maximal order. -/
theorem maximalIdealCount_split [Fact p.Prime]
    (hD : IsFundamentalDiscriminant D) (h : kroneckerAtPrime D p = 1)
    (m : ℕ) :
    idealCount D (p ^ m) = m + 1 := by
  sorry

/-- **Proposition 3.1.1, inert case.**  `D` fundamental, `(D/p) = −1`:
one ideal of norm `p^m` for even `m` (namely `(p)^{m/2}`), none for odd `m`. -/
theorem maximalIdealCount_inert [Fact p.Prime]
    (hD : IsFundamentalDiscriminant D) (h : kroneckerAtPrime D p = -1)
    (m : ℕ) :
    idealCount D (p ^ m) = if Even m then 1 else 0 := by
  sorry

/-- **Proposition 3.1.1, ramified case.**  `D` fundamental, `(D/p) = 0`
(i.e. `p ∣ D`): exactly one ideal of norm `p^m`, namely `𝔭^m`. -/
theorem maximalIdealCount_ramified [Fact p.Prime]
    (hD : IsFundamentalDiscriminant D) (h : kroneckerAtPrime D p = 0)
    (m : ℕ) :
    idealCount D (p ^ m) = 1 := by
  sorry

end QuadraticOrder
