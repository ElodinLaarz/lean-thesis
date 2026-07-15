import QuadraticOrder.Localization.PrincipalMin

/-!
# Equality criterion for principal local ideals (Lemma 3.2.8)

**Thesis.** Lemma 3.2.8, with the delegation to 3.2.7 + 3.2.4 spelled out
(the thesis's two-line proof hides the identification of the contraction's
normal form — the formal proof must make it explicit; see the companion doc).

**Human-readable companion.** `proofs/lem-3-2-8.md`.

**This file states:**

* `map_span_tau_sub_eq_iff` — `(p^r(τ−α))·O_P = (p^r(τ−β))·O_P` iff
  `v_p(g(α)) = v_p(g(β))` and `α ≡ β (mod p^{v_p(g(α))})`

**Proof strategy** (WP-D, after WP-C's `canonicalIdeal_inj`): contract both
sides with `comap_map_span_tau_sub_eq_canonicalIdeal`; equal local ideals have
equal contractions, and canonical ideals with the same parameters pin the
residue class by `canonicalIdeal_inj`; conversely congruent `α, β` differ by
an element already in the contraction.  The criterion is independent of `r`.

**Status.** WP-D stub (`sorry`).  Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- **Lemma 3.2.8.**  For `p ∣ f` and `P` the unique prime over `p`:
`(p^r(τ−α))·(O_d)_P = (p^r(τ−β))·(O_d)_P` iff `g(α)` and `g(β)` have the same
`p`-adic valuation `ν` and `α ≡ β (mod p^ν)`. -/
theorem map_span_tau_sub_eq_iff [ConductorPrimeSetup d D f p]
    (P : Ideal (QuadraticOrder d)) [P.IsPrime]
    (hP : (p : QuadraticOrder d) ∈ P) (r : ℕ) (α β : ℤ) :
    Ideal.map (algebraMap (QuadraticOrder d) (Localization.AtPrime P))
        (Ideal.span {(p : QuadraticOrder d) ^ r * (tau - (α : QuadraticOrder d))}) =
      Ideal.map (algebraMap (QuadraticOrder d) (Localization.AtPrime P))
        (Ideal.span {(p : QuadraticOrder d) ^ r * (tau - (β : QuadraticOrder d))}) ↔
      padicValInt p (normEval d α) = padicValInt p (normEval d β) ∧
        α ≡ β [ZMOD (p : ℤ) ^ padicValInt p (normEval d α)] := by
  sorry

end QuadraticOrder
