import QuadraticOrder.RootCounting.Defs
import QuadraticOrder.RootCounting.OddPrimeCoprime
import QuadraticOrder.RootCounting.OddPrimeEvenVal
import QuadraticOrder.RootCounting.ZeroCase
import QuadraticOrder.RootCounting.TwoPower

/-!
# Root counting for quadratic congruences

**Thesis.** Corrected and completed Lemma 3.2.6 (ERRATA E3 and E6.5).

**Human-readable companion.** `proofs/lem-3-2-6.md`.

**This file states/proves:** This compatibility module re-exports the complete
`cardSqrts` API: the definition, odd-prime unit and valuation formulas, the odd-
valuation vanishing theorem, the zero case, and the corrected powers-of-two formula.

**Proof strategy.** The implementation is split by the five mathematical steps of the
companion proof into `Defs`, `OddPrimeCoprime`, `OddPrimeEvenVal`, `ZeroCase`, and
`TwoPower`.  Importing this module preserves the pre-WP-B public import path.

**Divergence from thesis.** The two-adic residue condition is explicitly a condition on
the residual exponent `s - 2r`, not on `s`.

**Status.** WP-B proved; all frozen statements are sorry-free.
-/
