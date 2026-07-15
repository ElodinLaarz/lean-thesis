import QuadraticOrder.CanonicalForm.Bijection
import QuadraticOrder.RootCounting.TwoPower

/-!
# Theorem 3.1.2* — all ideals of norm `p^m` in `O_d`, `p ∣ f` (CORRECTED)

**Thesis.** Theorem 3.1.2 — **in the corrected, `p`-uniform form of
ERRATA E4**.  The thesis's separate five-case 2-adic display contains two
false cases (E1: 2-inert with `w ≥ 2`; E2: `D ≡ 4 (mod 8)` with `m` odd);
after correction the `p = 2` count coincides with the `p ≠ 2` formulas, so
this file states ONE statement per splitting type, valid for every `p ∣ f`.

**Do not "fix" these statements back toward the thesis text.**  Ground truth
is `ERRATA.md`; the numerical counterexamples live in
`Harness/Regression.lean` and will fail loudly if the statements drift.

**Human-readable companion.** `proofs/thm-3-1-2.md` — the full corrected
proof, including the boundary-regime analysis and the worked E1/E2 tables.

Notation: `w = v_p(f) = padicValNat p f`, `v = v_p(d/4) = valD4 d p`
(E6.8 convention), `ε = epsilonEven m` (`1` iff `m` even).  Geometric sums
are written `Σ_{i<k} p^i` to avoid division.

**This file states:**

* `idealCount_prime_pow_of_le`     — trivial branch `v ≥ m`: `Σ_{i≤⌊m/2⌋} p^i`
* `idealCount_prime_pow_ramified`  — `v < m`, `(D/p) = 0`:  `Σ_{i≤w} p^i`
* `idealCount_prime_pow_inert`     — `v < m`, `(D/p) = −1`: `Σ_{i<w+ε} p^i`
* `idealCount_prime_pow_split`     — `v < m`, `(D/p) = 1`:  `Σ_{i<w+ε} p^i + p^w(m+1−2w−ε)`

**Proof strategy** (WP-F): the summation formula
`idealCount_prime_pow_eq_sum_rootCount` reduces to root counts of `g` mod
`p^{2k−m}`; complete the square (`x ↦ x + d/2`; 2-adic variant in the
companion doc) so the summand is `cardSqrts` of `p^{2r}·u`; apply
`cardSqrts_prime_pow_even_val` / `cardSqrts_two_pow_even_val` with
`r = w` (resp. `w − 1` for `p = 2`, `D` odd), tracking the residual exponent
`s − 2r` — NEVER `s` (ERRATA E3, the thesis's proof bug); sum the geometric
pieces over `k ≤ κ < k`, `κ = (v + m)/2`.  Case files may be split off
(`TotalRamified.lean` etc.) if this file grows past ~400 lines.

**Status.** WP-F stubs (`sorry`).  Statements frozen by WP-0 against
ERRATA E4.  Regression vectors: `Harness/Regression.lean`.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- **Theorem 3.1.2*, trivial branch.**  For `m ≤ v = v_p(d/4)`:
`#{I : [O:I] = p^m} = 1 + p + ⋯ + p^{⌊m/2⌋}`.

(The thesis states this branch for `v ≥ m` and it is correct as stated; the
boundary `v = m` MUST stay in this branch — the split-case formula would
evaluate to a negative number there.  ERRATA E5 discussion.) -/
theorem idealCount_prime_pow_of_le [Fact p.Prime] [ConductorPrimeSetup d D f p]
    (m : ℕ) (hm : m ≤ valD4 d p) :
    idealCount d (p ^ m) = ∑ i ∈ Finset.range (m / 2 + 1), p ^ i := by
  sorry

/-- **Theorem 3.1.2*, ramified case** (`p ∣ D`, i.e. `(D/p) = 0`), `v < m`:
`#{I : [O:I] = p^m} = 1 + p + ⋯ + p^{w}`.

Corrected: for `p = 2` this is the SAME formula (the thesis's
`D ≡ 4 (mod 8)`, `m` odd case claimed `2^w − 1`; false — ERRATA E2,
counterexample `d = −16`, `m = 3` has 3 ideals, not 1). -/
theorem idealCount_prime_pow_ramified [Fact p.Prime] [ConductorPrimeSetup d D f p]
    (m : ℕ) (hv : valD4 d p < m) (hK : kroneckerAtPrime D p = 0) :
    idealCount d (p ^ m) = ∑ i ∈ Finset.range (padicValNat p f + 1), p ^ i := by
  sorry

/-- **Theorem 3.1.2*, inert case** (`(D/p) = −1`), `v < m`:
`#{I : [O:I] = p^m} = 1 + p + ⋯ + p^{w+ε−1}`  (`ε = 1` iff `m` even).

Corrected: valid for ALL `w ≥ 1` including `p = 2` (the thesis claimed
`2^{w−1+ε} − 1` for `w ≠ 1`; false — ERRATA E1, counterexamples `d = −48`,
`m = 3, 4` and `d = −192`, `m = 5`). -/
theorem idealCount_prime_pow_inert [Fact p.Prime] [ConductorPrimeSetup d D f p]
    (m : ℕ) (hv : valD4 d p < m) (hK : kroneckerAtPrime D p = -1) :
    idealCount d (p ^ m) =
      ∑ i ∈ Finset.range (padicValNat p f + epsilonEven m), p ^ i := by
  sorry

/-- **Theorem 3.1.2*, split case** (`(D/p) = 1`), `v < m`:
`#{I : [O:I] = p^m} = (1 + p + ⋯ + p^{w+ε−1}) + p^w·(m + 1 − 2w − ε)`.

In the valid regime `v < m` one has `m ≥ 2w + 1`, so the `ℕ`-subtraction
`m + 1 − 2w − ε` never truncates. -/
theorem idealCount_prime_pow_split [Fact p.Prime] [ConductorPrimeSetup d D f p]
    (m : ℕ) (hv : valD4 d p < m) (hK : kroneckerAtPrime D p = 1) :
    idealCount d (p ^ m) =
      ∑ i ∈ Finset.range (padicValNat p f + epsilonEven m), p ^ i
        + p ^ padicValNat p f * (m + 1 - 2 * padicValNat p f - epsilonEven m) := by
  sorry

end QuadraticOrder
