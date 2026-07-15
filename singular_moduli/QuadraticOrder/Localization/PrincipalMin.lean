import QuadraticOrder.Localization.Basic
import QuadraticOrder.CanonicalForm
import QuadraticOrder.Defs.Counting

/-!
# Contraction of a principal local ideal (Lemma 3.2.7)

**Thesis.** Lemma 3.2.7, restated at the level of ideals of `O_d` (the form
Corollary 3.1.3* actually consumes): the contraction to `O_d` of the local
principal ideal `(p^r(τ − a))·(O_d)_P` is the canonical ideal
`(p^{r+ν}, p^r(τ − a))` where `ν = v_p(N(τ − a)) = v_p(g(a))` — equivalently,
`p^{r+ν}` is the minimal `p`-power in the local ideal.

Standing hypotheses explicit per ERRATA E6.2 (unique prime over `p`; false for
split `p`).  The thesis's shift variable `s` is renamed `a` to avoid the
collision with Lemma 3.2.6's modulus exponent (ERRATA E6.7).

**Human-readable companion.** `proofs/lem-3-2-7.md`.

**This file states:**

* `comap_map_span_tau_sub_eq_canonicalIdeal` — the contraction form of
  Lemma 3.2.7 used by the invertible-ideal count.

**Proof strategy** (WP-D): `p^r(τ−a)·(τ̄−a) = p^r·g(a)` gives containment; for
minimality, the determinant/rank-1 argument of the thesis (any `β` with
`p^r(τ−a)·β ∈ ℤ` is a `ℤ_(p)`-multiple of the conjugate), using
`exists_int_denominator`.

**Status.** WP-D stub (`sorry`).  Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- **Lemma 3.2.7** (contraction form).  For `p ∣ f`, `P` the unique prime
over `p`, `r ≥ 0`, `a ∈ ℤ`, and `ν := v_p(g(a))` (`g(a) = normEval d a`):
the contraction of `(p^r(τ − a))·(O_d)_P` to `O_d` is the canonical ideal
with parameters `k = r + ν`, `m = 2r + ν` (so `m − k = r`). -/
theorem comap_map_span_tau_sub_eq_canonicalIdeal [ConductorPrimeSetup d D f p]
    (P : Ideal (QuadraticOrder d)) [P.IsPrime]
    (hP : (p : QuadraticOrder d) ∈ P) (r : ℕ) (a : ℤ) :
    Ideal.comap (algebraMap (QuadraticOrder d) (Localization.AtPrime P))
      (Ideal.map (algebraMap (QuadraticOrder d) (Localization.AtPrime P))
        (Ideal.span {(p : QuadraticOrder d) ^ r * (tau - (a : QuadraticOrder d))})) =
      canonicalIdeal d p (r + padicValInt p (normEval d a))
        (2 * r + padicValInt p (normEval d a)) a := by
  sorry

end QuadraticOrder
