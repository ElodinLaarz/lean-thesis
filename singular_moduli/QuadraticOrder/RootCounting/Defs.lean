import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Square-root counting: definition

**Thesis.** Infrastructure for the corrected and completed Lemma 3.2.6.

**Human-readable companion.** `proofs/lem-3-2-6.md`.

**This file states/proves:**

* `cardSqrts` -- the number of square roots of a residue in `ZMod n`.

**Proof strategy.** This file only fixes the common counting definition.  The subsequent
files separately prove the odd-prime unit case, valuation reduction, zero case, and
the corrected two-adic case, following Steps 1--5 of the companion proof.

**Status.** WP-B proved; definition unchanged from the WP-0 statement freeze.
-/

namespace QuadraticOrder

open Finset

/-- The number of elements `x` in `ZMod n` satisfying `x ^ 2 = c`. -/
def cardSqrts (n : ℕ) [NeZero n] (c : ZMod n) : ℕ :=
  (univ.filter fun x : ZMod n => x ^ 2 = c).card

end QuadraticOrder
