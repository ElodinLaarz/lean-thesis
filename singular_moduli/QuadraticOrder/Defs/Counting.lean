import QuadraticOrder.Defs.Setup
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The counting quantities (statement freeze)

**Thesis.** §1.2: the norm of an integral ideal `a ⊆ O_d` is the index
`N(a) = [O_d : a]` — including for NON-invertible ideals, where this index is
the only sensible norm (the thesis convention; see `proofs/notation.md`).

**Human-readable companion.** `proofs/notation.md` §"Counting quantities".

**This file defines** (definitions only — no theorems, no proofs):

* `idealIndex I` — the index `[O_d : I]` as a natural number
  (`Nat.card` of the quotient ring; `0` when the quotient is infinite, i.e.
  for `I = ⊥`)
* `idealCount d n` — `#{ I ⊆ O_d : [O_d : I] = n }`, the LHS of Theorem 3.1.2*
* `IsInvertibleIdeal I` — invertibility in the fraction-free form
  `∃ J, x ≠ 0, I·J = (x)`; `WP-G` proves this equivalent to locally principal
  (see `QuadraticOrder/Index/Invertible.lean` and `proofs/infra-invertibility.md`)
* `invertibleIdealCount d n` — `#{ I : [O_d : I] = n, I invertible }`, the LHS
  of Corollary 3.1.3*
* `rootCountMod d N` — `#{ A ∈ ℤ/N : g(A) ≡ 0 (mod N) }`, the root count the
  normal-form bijection (Lemma 3.2.4) converts ideal counting into

**Design note (why not `Ideal.absNorm`).** Mathlib's bundled
`Ideal.absNorm : Ideal S →*₀ ℕ` and its multiplicativity are Dedekind-gated,
and unrestricted index-multiplicativity is FALSE for non-invertible ideals of a
non-maximal order (see `PLAN.md` §4.2).  The project therefore builds on the
raw index.  `WP-A` supplies the replacement API: finiteness, comaximal (CRT)
multiplicativity, and the prime-power factorization of the count.

**Proof strategy.** This file only fixes definitions.  Each definition is a
literal Lean transcription of the corresponding set or cardinality in
`proofs/notation.md`; all finiteness and arithmetic facts are proved later in
the files named above, so no mathematical assertion is hidden here.

**Status.** WP-0 statement freeze.  Definitions are final API.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-- The index `[O_d : I]` of an ideal, as a natural number: the cardinality of
the quotient ring, with the `Nat.card` convention that an infinite quotient
(only `I = ⊥`) has index `0`.

This is the thesis's ideal norm `N(I)`, valid for non-invertible ideals. -/
noncomputable def idealIndex (I : Ideal (QuadraticOrder d)) : ℕ :=
  Nat.card (QuadraticOrder d ⧸ I)

/-- The number of ideals of `O_d` of index (= norm) `n`.  Finiteness for
`n ≥ 1` is `finite_setOf_idealIndex_eq` (WP-A); `Nat.card` makes the
definition total regardless. -/
noncomputable def idealCount (d : ℤ) (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (QuadraticOrder d) // idealIndex I = n}

/-- Invertibility of an integral ideal, in fraction-field-free form: `I` is
invertible iff `I·J` is a nonzero principal ideal for some integral ideal `J`.

For a domain this is equivalent to invertibility as a fractional ideal and to
being locally principal (`isInvertibleIdeal_iff_isLocallyPrincipal`, WP-G);
the thesis says "locally principal / proper". -/
def IsInvertibleIdeal (I : Ideal (QuadraticOrder d)) : Prop :=
  ∃ (J : Ideal (QuadraticOrder d)) (x : QuadraticOrder d),
    x ≠ 0 ∧ I * J = Ideal.span {x}

/-- The number of INVERTIBLE ideals of `O_d` of index `n` — the corrected
Corollary 3.1.3*'s left-hand side.  (The thesis's display omits the word
"invertible"; ERRATA E6.1.) -/
noncomputable def invertibleIdealCount (d : ℤ) (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (QuadraticOrder d) // idealIndex I = n ∧ IsInvertibleIdeal I}

/-- The number of roots of the defining polynomial `g(x) = x² − dx + (d²−d)/4`
in `ℤ/N`.  The normal-form bijection (Lemma 3.2.4) proves
`idealCount d (p^m) = Σ_k rootCountMod d (p^{2k−m})`
(`idealCount_prime_pow_eq_sum_rootCount`), and Lemma 3.2.6 evaluates these
counts in closed form after completing the square. -/
noncomputable def rootCountMod (d : ℤ) (N : ℕ) : ℕ :=
  Nat.card {A : ZMod N // ((poly d).map (Int.castRingHom (ZMod N))).eval A = 0}

end QuadraticOrder
