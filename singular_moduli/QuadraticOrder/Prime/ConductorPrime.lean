import QuadraticOrder.Prime
import QuadraticOrder.Defs.Setup

/-!
# The unique prime above a conductor prime

**Thesis.** Remark 3.2.3's load-bearing consequence, never isolated in the
thesis (ERRATA E6.10): for `p ∣ f` there is a UNIQUE prime ideal of `O_d`
containing `p`.  This is the standing hypothesis under which all of
§3.2/§3.3 operates.

**Human-readable companion.** `proofs/prop-3-2-1.md` (statement, proof, and
the promotion of Remark 3.2.3 to a lemma).

**This file states:**

* `existsUnique_isPrime_mem_of_dvd_conductor` — uniqueness of the prime above
  `p ∣ f`

**Proof strategy** (for the implementer, WP-A): `p ∣ f ⟹ p² ∣ d ⟹ p ∣ d`, so
by `prime_ramified_iff`-side reasoning `g ≡ (x − d/2)² (mod p)` for odd `p`
(and `g ≡ (x+1)² (mod 2)` resp. `x²` in the 2-adic cases) — a square of a
linear polynomial; the quotient isomorphism
`quadraticOrderModP_equiv_polyModQuot` (Prime/QuotientIso.lean) then shows
`O/(p)` is local, so the primes over `p` — which biject with primes of
`O/(p)` — collapse to one.  Do NOT route through Mathlib's Kummer–Dedekind:
it excludes conductor primes (PLAN §3.1).

**Status.** WP-A stub (`sorry`).  Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- For a prime `p` dividing the conductor there is exactly one prime ideal of
`O_d` containing `p` (Remark 3.2.3's consequence, promoted; ERRATA E6.10).

The unique `P` is the radical of `(p)`; every `p`-power-index ideal is
`P`-primary (`isPrimary_of_idealIndex_prime_pow`). -/
theorem existsUnique_isPrime_mem_of_dvd_conductor
    [ConductorPrimeSetup d D f p] :
    ∃! P : Ideal (QuadraticOrder d), P.IsPrime ∧ (p : QuadraticOrder d) ∈ P := by
  sorry

end QuadraticOrder
