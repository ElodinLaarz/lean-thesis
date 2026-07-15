import QuadraticOrder.CanonicalForm
import QuadraticOrder.Index.Primary
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The normal-form bijection (Lemma 3.2.4, completed)

**Thesis.** Lemma 3.2.4 + Remark 3.2.5, strengthened with the two clauses the
thesis leaves unstated (ERRATA E6.4): the converse must produce an ideal whose
minimal `p`-power is EXACTLY `p^k` (else ideals double-count across `k`), and
the passage from "`P`-primary" to "all ideals of index `p^m`" needs the bridge
`isPrimary_of_idealIndex_prime_pow`.

**Human-readable companion.** `proofs/lem-3-2-4.md` — the keystone document;
read it before implementing anything here.

**This file states:**

* `idealIndex_canonicalIdeal` — `[O : (p^k, p^{m−k}(τ−A))] = p^m` for
  admissible parameters
* `canonicalIdeal_minimal_pow` — `p^k` lies in the canonical ideal and no
  smaller `p`-power does (the thesis's gap, E6.4b)
* `exists_canonicalIdeal_eq` — every ideal of index `p^m` IS a canonical ideal
  (existence half; primary-ness comes from the bridge lemma)
* `canonicalIdeal_inj` — uniqueness of the residue class `[A]` at fixed `k`
* `idealCount_prime_pow_eq_sum_rootCount` — the **summation formula**
  `#{I : [O:I] = p^m} = Σ_{k=⌈m/2⌉}^{m} #{A ∈ ℤ/p^{2k−m} : g(A) = 0}` —
  the exact interface `IdealCount.lean` consumes (WP-C's exit criterion)

**Proof strategy** (WP-C): existence via the two-generator reduction in
`ℤ/p^k[x]/(g)` (thesis pp. 15–16; sign slips fixed in `proofs/lem-3-2-4.md`);
`ℤ`-span bookkeeping via the proved `canonicalIdeal_eq_zSpan`; the index by a
`ℤ`-basis determinant through `canonicalZSpan`; minimality because `p^{k−1}`
in the ideal would contradict the size computation of the cyclic module
`(p^{m−k}(x−A))` in `ℤ/p^k[x]/(g)`.

**Status.** WP-C stubs (`sorry`); `canonicalIdeal`, `CanonicalAdmissible`,
`canonicalZSpan`, `canonicalIdeal_eq_zSpan` are already proved in
`CanonicalForm.lean`.  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- Admissible canonical parameters give an ideal of index exactly `p^m`. -/
theorem idealIndex_canonicalIdeal [ConductorPrimeSetup d D f p]
    {k m : ℕ} {A : ℤ} (h1 : m ≤ 2 * k) (h2 : k ≤ m)
    (hA : CanonicalAdmissible d p k m A) :
    idealIndex (canonicalIdeal d p k m A) = p ^ m := by
  sorry

/-- The canonical ideal contains `p^k` and no smaller power of `p` — the
minimality clause missing from the thesis's converse (ERRATA E6.4b).  Without
it, the parameter `k` would not be recoverable from the ideal and the
summation formula would double-count. -/
theorem canonicalIdeal_minimal_pow [ConductorPrimeSetup d D f p]
    {k m : ℕ} {A : ℤ} (h1 : m ≤ 2 * k) (h2 : k ≤ m)
    (hA : CanonicalAdmissible d p k m A) :
    (p : QuadraticOrder d) ^ k ∈ canonicalIdeal d p k m A ∧
      ∀ j < k, (p : QuadraticOrder d) ^ j ∉ canonicalIdeal d p k m A := by
  sorry

/-- Existence: every ideal of `O_d` of index `p^m` (`p ∣ f`) is a canonical
ideal `(p^k, p^{m−k}(τ−A))` for some `⌈m/2⌉ ≤ k ≤ m` and admissible `A`.
(`P`-primaryness is automatic: `isPrimary_of_idealIndex_prime_pow`.) -/
theorem exists_canonicalIdeal_eq [ConductorPrimeSetup d D f p]
    {m : ℕ} (I : Ideal (QuadraticOrder d)) (hI : idealIndex I = p ^ m) :
    ∃ (k : ℕ) (A : ℤ), m ≤ 2 * k ∧ k ≤ m ∧ CanonicalAdmissible d p k m A ∧
      I = canonicalIdeal d p k m A := by
  sorry

/-- Uniqueness of the residue class: two canonical ideals with the same `k`
and `m` coincide only when `A ≡ B (mod p^{2k−m})`.  (Distinct `k` are
separated by `canonicalIdeal_minimal_pow`.) -/
theorem canonicalIdeal_inj [ConductorPrimeSetup d D f p]
    {k m : ℕ} {A B : ℤ} (h1 : m ≤ 2 * k) (h2 : k ≤ m)
    (hA : CanonicalAdmissible d p k m A) (hB : CanonicalAdmissible d p k m B)
    (h : canonicalIdeal d p k m A = canonicalIdeal d p k m B) :
    A ≡ B [ZMOD (p : ℤ) ^ (2 * k - m)] := by
  sorry

/-- **The summation formula** (Lemma 3.2.4 as a counting statement): the
number of ideals of index `p^m` equals the number of roots of `g` modulo
`p^{2k−m}`, summed over `⌈m/2⌉ ≤ k ≤ m`.  This is the interface consumed by
Theorem 3.1.2* (`IdealCount.lean`); Lemma 3.2.6 evaluates the summands. -/
theorem idealCount_prime_pow_eq_sum_rootCount [ConductorPrimeSetup d D f p]
    (m : ℕ) :
    idealCount d (p ^ m) =
      ∑ k ∈ Finset.Icc ((m + 1) / 2) m, rootCountMod d (p ^ (2 * k - m)) := by
  sorry

end QuadraticOrder
