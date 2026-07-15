import QuadraticOrder.MaximalCase
import QuadraticOrder.Index.Basic

/-!
# Glue: counts for arbitrary norm `n` (beyond the thesis)

**Thesis.** Not stated — the natural completion of §3.1 (see PLAN §5, WP-H):
assemble the prime-power counts (Theorem 3.1.2* for `p ∣ f`,
Proposition 3.1.1 for `p ∤ f`) into a count for arbitrary `n`, and transfer
counts to the maximal order away from the conductor.

**Human-readable companion.** `proofs/infra-glue.md`.

**This file states:**

* `idealCount_eq_prod_primeFactors` — `idealCount d n = Π_p idealCount d (p^{v_p(n)})`
* `idealCount_eq_of_coprime_conductor` — for `gcd(n, f) = 1`,
  `idealCount d n = idealCount D n` (the maximal-order transfer)
* `invertibleIdealCount_eq_prod_primeFactors` — invertible analogue

**Proof strategy** (WP-H): the first from `idealCount_multiplicative` by
induction on the prime factorization; the transfer via the conductor-avoiding
correspondence (localization isomorphism between `O_d` and `O_D` away from
`f`, upgraded to a norm-preserving ideal bijection — Mathlib's
`Localization.localRingHom_bijective_of_not_conductor_le` is the germ); the
invertible analogue rides the same bijections, which preserve invertibility.

**Status.** WP-H stubs (`sorry`).  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-- The ideal count is determined by its prime-power values:
`idealCount d n = Π_{p ∣ n} idealCount d (p^{v_p(n)})`. -/
theorem idealCount_eq_prod_primeFactors (hd : IsDiscriminant d)
    {n : ℕ} (hn : 0 < n) :
    idealCount d n = ∏ q ∈ n.primeFactors, idealCount d (q ^ n.factorization q) := by
  sorry

/-- Away from the conductor the order and the maximal order count alike:
for `gcd(n, f) = 1`, `idealCount d n = idealCount D n` (where `d = D·f²`,
`D` fundamental).  Together with Proposition 3.1.1 this evaluates the count
at every prime not dividing `f`. -/
theorem idealCount_eq_of_coprime_conductor
    {D : ℤ} {f : ℕ} (hD : IsFundamentalDiscriminant D)
    (hdf : d = D * (f : ℤ) ^ 2) (hf : 0 < f)
    {n : ℕ} (hn : 0 < n) (hcop : n.Coprime f) :
    idealCount d n = idealCount D n := by
  sorry

/-- Invertible analogue of `idealCount_eq_prod_primeFactors`. -/
theorem invertibleIdealCount_eq_prod_primeFactors (hd : IsDiscriminant d)
    {n : ℕ} (hn : 0 < n) :
    invertibleIdealCount d n =
      ∏ q ∈ n.primeFactors, invertibleIdealCount d (q ^ n.factorization q) := by
  sorry

end QuadraticOrder
