import QuadraticOrder.IdealCount
import QuadraticOrder.Index.Invertible
import QuadraticOrder.Localization.PrincipalEq

/-!
# Corollary 3.1.3* — invertible ideals of norm `p^m` (CORRECTED)

**Thesis.** Corollary 3.1.3 — **in the corrected regime of ERRATA E5**, with
the two statement repairs of E6.1: the count is of INVERTIBLE (locally
principal) ideals — the thesis display omits the word — and the inert/odd
case (count `0`) is included.

The corrected regime (E5): the trivial branch applies iff `m < v` OR
(`m = v` and `v = 2w − 2`, i.e. `p = 2` with `D` odd); the case branch applies
iff `m > v` OR (`m = v ≥ 2w`, i.e. `p` odd or `4 ∣ D`).  The thesis's regime
(`>` / `≤`) is FALSE for `p = 2`, `D` odd: at `d = −112`, `m = 2` its split
formula yields `−2`.  The corrected regime also makes `m = 0` come out right
(count `1`) without a separate hypothesis.

**Do not harmonize the regime conditions with Theorem 3.1.2*'s** — the
asymmetry is forced; see ERRATA E5 and `proofs/cor-3-1-3.md`.

**Human-readable companion.** `proofs/cor-3-1-3.md`.

**This file states:**

* `invertibleIdealCount_prime_pow_trivial` — trivial branch:
  `p^{m/2}` (even `m`) or `0`
* `invertibleIdealCount_prime_pow_ramified` — case branch, `(D/p) = 0`: `p^w`
* `invertibleIdealCount_prime_pow_inert` — case branch, `(D/p) = −1`:
  `p^w + p^{w−1}` (even `m`) or `0`
* `invertibleIdealCount_prime_pow_split` — case branch, `(D/p) = 1`:
  `(p^w − p^{w−1})(m+1−2w)`

**Proof strategy** (WP-G): an invertible ideal of index `p^m` is locally
principal (`isInvertibleIdeal_iff_isLocallyPrincipal`); by Lemmas 3.2.7/3.2.8
its normal-form parameter `A` has `v_p(g(A))` EXACTLY `2k − m` — a root mod
`p^{2k−m}` that does not lift mod `p^{2k−m+1}` — and the root-minus-lift
bookkeeping over `k` with Lemma 3.2.6 produces the four formulas; the
boundary analysis producing the corrected regime is in the companion doc.

**Status.** WP-G stubs (`sorry`).  Statements frozen by WP-0 against
ERRATA E5.  Regression vectors: `Harness/Regression.lean`.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- **Corollary 3.1.3*, trivial branch** (corrected regime, ERRATA E5):
if `m < v`, or `m = v` with `v = 2w − 2` (the `p = 2`, `D` odd boundary),
then the invertible ideals of index `p^m` number `p^{m/2}` for even `m` and
`0` for odd `m`.  At `m = 0` this gives `1`, fixing the thesis's `m = 0`
corner bug. -/
theorem invertibleIdealCount_prime_pow_trivial [Fact p.Prime]
    [ConductorPrimeSetup d D f p] (m : ℕ)
    (hreg : m < valD4 d p ∨
      (m = valD4 d p ∧ valD4 d p = 2 * padicValNat p f - 2)) :
    invertibleIdealCount d (p ^ m) = if Even m then p ^ (m / 2) else 0 := by
  sorry

/-- **Corollary 3.1.3*, ramified case** (corrected regime): if `m > v`, or
`m = v ≥ 2w`, and `(D/p) = 0`, the invertible count is `p^w` — for BOTH
parities of `m` (the thesis's total in the `D ≡ 4 (mod 8)`, `m` odd case was
smaller than this invertible count; the internal contradiction of ERRATA E2). -/
theorem invertibleIdealCount_prime_pow_ramified [Fact p.Prime]
    [ConductorPrimeSetup d D f p] (m : ℕ)
    (hreg : valD4 d p < m ∨
      (m = valD4 d p ∧ 2 * padicValNat p f ≤ valD4 d p))
    (hK : kroneckerAtPrime D p = 0) :
    invertibleIdealCount d (p ^ m) = p ^ padicValNat p f := by
  sorry

/-- **Corollary 3.1.3*, inert case** (corrected regime): count
`p^w + p^{w−1}` for even `m`, `0` for odd `m` (the odd case is missing from
the thesis display; ERRATA E6.1). -/
theorem invertibleIdealCount_prime_pow_inert [Fact p.Prime]
    [ConductorPrimeSetup d D f p] (m : ℕ)
    (hreg : valD4 d p < m ∨
      (m = valD4 d p ∧ 2 * padicValNat p f ≤ valD4 d p))
    (hK : kroneckerAtPrime D p = -1) :
    invertibleIdealCount d (p ^ m) =
      if Even m then p ^ padicValNat p f + p ^ (padicValNat p f - 1) else 0 := by
  sorry

/-- **Corollary 3.1.3*, split case** (corrected regime): count
`(p^w − p^{w−1})·(m + 1 − 2w)`.  Regression anchor: `d = −112`, `m = 2` gives
`2` — the thesis's regime placed this datum in the case branch where the
formula evaluates to `−2` (ERRATA E5). -/
theorem invertibleIdealCount_prime_pow_split [Fact p.Prime]
    [ConductorPrimeSetup d D f p] (m : ℕ)
    (hreg : valD4 d p < m ∨
      (m = valD4 d p ∧ 2 * padicValNat p f ≤ valD4 d p))
    (hK : kroneckerAtPrime D p = 1) :
    invertibleIdealCount d (p ^ m) =
      (p ^ padicValNat p f - p ^ (padicValNat p f - 1)) *
        (m + 1 - 2 * padicValNat p f) := by
  sorry

end QuadraticOrder
