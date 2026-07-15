import QuadraticOrder.Prime.ConductorPrime
import QuadraticOrder.Defs.Counting
import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Bridge lemma: prime-power index forces primary

**Thesis.** Unstated bridge (ERRATA E6.4a): the thesis counts `P`-primary
ideals via the normal form (Lemma 3.2.4) but the theorem (3.1.2) counts ALL
ideals of index `p^m` — the two agree only because, for `p ∣ f`, an ideal of
index `p^m` is automatically primary for the unique prime `P` above `p`.

**Human-readable companion.** `proofs/infra-index.md` §"Bridge lemma".

**This file states:**

* `isPrimary_of_idealIndex_prime_pow` — index `p^m` (`m ≥ 1`) ⟹ `I.IsPrimary`

**Proof strategy** (WP-A): `p^m·O ⊆ I`, so every prime over `I` is a prime
over `(p)`; by `existsUnique_isPrime_mem_of_dvd_conductor` that prime is
unique, hence `I.radical = P` is prime and maximal (finite quotient domain),
and an ideal whose radical is maximal is primary
(`Ideal.isPrimary_of_isMaximal_radical`-style; verify the exact Mathlib name
on the pin).

**Status.** WP-A stub (`sorry`).  Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- For `p ∣ f`: an ideal of index `p^m`, `m ≥ 1`, is primary (for the unique
prime above `p`).  This is what lets Lemma 3.2.4's count of primary ideals
equal Theorem 3.1.2*'s count of all ideals of index `p^m` (ERRATA E6.4a). -/
theorem isPrimary_of_idealIndex_prime_pow
    [ConductorPrimeSetup d D f p]
    {I : Ideal (QuadraticOrder d)} {m : ℕ} (hm : 0 < m)
    (hI : idealIndex I = p ^ m) :
    Ideal.IsPrimary I := by
  sorry

end QuadraticOrder
