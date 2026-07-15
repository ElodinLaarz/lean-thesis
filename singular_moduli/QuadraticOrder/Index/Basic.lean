import QuadraticOrder.Defs.Counting

/-!
# The index layer: finiteness and multiplicativity

**Thesis.** Not stated — infrastructure the thesis uses silently whenever it
multiplies counts across primes or speaks of "the number of ideals of norm n".

**Human-readable companion.** `proofs/infra-index.md` — full statements,
proofs, and the warning about why Mathlib's `Ideal.absNorm` API cannot be used
here (its multiplicativity is Dedekind-gated, and unrestricted
index-multiplicativity is FALSE for non-invertible ideals of a non-maximal
order).

**This file states:**

* `idealIndex_mul_of_codisjoint` — CRT multiplicativity: `[O : I·J] = [O : I]·[O : J]`
  for comaximal `I, J`
* `finite_setOf_idealIndex_eq` — finitely many ideals of a given index `n ≥ 1`
* `idealCount_multiplicative` — `idealCount d (m·n) = idealCount d m · idealCount d n`
  for coprime `m, n`

**Proof strategy** (WP-A): comaximal case via `Ideal.quotientMulEquivQuotientProd`
(CRT for the quotient ring); finiteness because an index-`n` ideal contains
`n·O_d`, and the sublattices of `ℤ²` between `n·ℤ²` and `ℤ²` are finite (Smith
normal form: `Submodule.smithNormalFormOfLE` exists in Mathlib);
count-multiplicativity from the bijection `I ↦ (I + m·O, I + n·O)` whose
inverse is intersection — the primary-decomposition bookkeeping is written out
in `proofs/infra-index.md`.

**Status.** WP-A stubs (`sorry`).  Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-- CRT multiplicativity of the index: if `I ⊔ J = ⊤` then
`[O : I·J] = [O : I]·[O : J]`.

Unrestricted multiplicativity (without comaximality) is FALSE in a non-maximal
order — see `proofs/infra-index.md` for a counterexample — which is why the
Dedekind-gated `Ideal.absNorm` API is off-limits (PLAN §4.2). -/
theorem idealIndex_mul_of_codisjoint (I J : Ideal (QuadraticOrder d))
    (h : I ⊔ J = ⊤) :
    idealIndex (I * J) = idealIndex I * idealIndex J := by
  sorry

/-- There are finitely many ideals of `O_d` of index `n ≥ 1`: any such ideal
is an intermediate lattice `n·O_d ⊆ I ⊆ O_d`, and `O_d/n·O_d` is finite. -/
theorem finite_setOf_idealIndex_eq (d : ℤ) {n : ℕ} (hn : 0 < n) :
    {I : Ideal (QuadraticOrder d) | idealIndex I = n}.Finite := by
  sorry

/-- The ideal count is multiplicative over coprime indices:
`idealCount d (m·n) = idealCount d m · idealCount d n` for `gcd(m,n) = 1`.

Via the CRT bijection `I ↦ (I + m·O, I + n·O)`; the proof is written out in
`proofs/infra-index.md`. -/
theorem idealCount_multiplicative (d : ℤ) {m n : ℕ} (h : m.Coprime n)
    (hm : 0 < m) (hn : 0 < n) :
    idealCount d (m * n) = idealCount d m * idealCount d n := by
  sorry

end QuadraticOrder
