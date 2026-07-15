import QuadraticOrder.Harness.Enumerate
import QuadraticOrder.RootCounting.TwoPower

/-!
# Regression vectors (ERRATA ground truth)

**Thesis.** Corrected Theorem 3.1.2* and Corollary 3.1.3*, specifically the
counterexamples and boundary cases in ERRATA E1, E2, and E5.

**Human-readable companion.** `proofs/lem-3-2-6.md`, `proofs/thm-3-1-2.md`,
and `proofs/cor-3-1-3.md` explain every family of rows and the formulas they pin.

**This file proves:** closed Boolean equalities for the square-root counts and
for the total and invertible counts returned by `Harness/Enumerate.lean` on the
ERRATA data set.

Every data point that exposed an error in the thesis — plus boundary and
maximal-order sanity rows — pinned as `native_decide` facts about the brute
enumerator.  If a frozen statement ever drifts from these numbers, the drift
is caught here, loudly, at build time.

Provenance: each row was verified by THREE independent computations — the two
enumeration methods recorded in `ERRATA.md` (normal-form and HNF-sublattice)
and this harness (validated row-by-row before commit).  See
`proofs/thm-3-1-2.md` and `proofs/cor-3-1-3.md` for the role each row plays.

`native_decide` trusts the Lean compiler; that is acceptable here because the
harness is a test oracle, not part of the proof development (see
`Harness/Enumerate.lean`, Trust model).

**Proof strategy.** Each example is normalized by the executable HNF
enumerator and discharged with `native_decide`; the rows are deliberately
redundant with the two independent computations recorded in `ERRATA.md`.

**Status.** WP-0 regression gate, extended by WP-B with the complete residual
exponent grid for the corrected two-adic square-root count.  These vectors are
ground truth and must not be weakened to accommodate a later closed form.
-/

-- The harness is a test oracle, not part of the proof development; compiler
-- trust is acceptable here (see the module docstring).
set_option linter.style.nativeDecide false

namespace QuadraticOrder.Harness

/-! ## Square-root counts (Lemma 3.2.6, corrected two-adic branch) -/

-- Residual exponent one: every odd unit gives one residual root, hence `2^r` roots.
example : cardSqrts 2 (1 : ZMod 2) = 1 := by native_decide
example : cardSqrts 8 ((4 : ℤ) : ZMod 8) = 2 := by native_decide
example : cardSqrts 8 ((12 : ℤ) : ZMod 8) = 2 := by native_decide

-- Residual exponent two: precisely the units congruent to one modulo four contribute.
example : cardSqrts 4 (1 : ZMod 4) = 2 := by native_decide
example : cardSqrts 4 (3 : ZMod 4) = 0 := by native_decide
example : cardSqrts 16 ((4 : ℤ) : ZMod 16) = 4 := by native_decide
example : cardSqrts 16 ((12 : ℤ) : ZMod 16) = 0 := by native_decide

-- Residual exponent at least three: precisely the units congruent to one modulo eight.
example : cardSqrts 8 (1 : ZMod 8) = 4 := by native_decide
example : cardSqrts 8 (3 : ZMod 8) = 0 := by native_decide
example : cardSqrts 8 (5 : ZMod 8) = 0 := by native_decide
example : cardSqrts 8 (7 : ZMod 8) = 0 := by native_decide
example : cardSqrts 32 ((4 : ℤ) : ZMod 32) = 8 := by native_decide
example : cardSqrts 32 ((12 : ℤ) : ZMod 32) = 0 := by native_decide

-- The prime-uniform companion cases: odd valuation has no roots; zero has the stated count.
example : cardSqrts 8 (2 : ZMod 8) = 0 := by native_decide
example : cardSqrts 16 (0 : ZMod 16) = 4 := by native_decide

/-! ## Total counts (Theorem 3.1.2*) -/

-- ERRATA E2: d = −16 (D = −4, w = 1), m odd — thesis said 1, corrected 2^{w+1}−1 = 3.
example : idealCountBrute (-16) 8 = 3 := by native_decide
example : idealCountBrute (-16) 32 = 3 := by native_decide

-- ERRATA E1: d = −48 (D = −3, w = 2, 2 inert) — thesis said 1, 3; corrected 3, 7.
example : idealCountBrute (-48) 8 = 3 := by native_decide
example : idealCountBrute (-48) 16 = 7 := by native_decide

-- ERRATA E1: d = −192 (w = 3, 2 inert), m = 5 — thesis said 3, corrected 7.
example : idealCountBrute (-192) 32 = 7 := by native_decide

-- Trivial branch (v ≥ m): d = −48, m = 2 (v = 2): Σ_{i≤1} 2^i = 3.
example : idealCountBrute (-48) 4 = 3 := by native_decide
-- d = −112 (D = −7, w = 2, 2 split), m = 2 = v: trivial branch, 3.
example : idealCountBrute (-112) 4 = 3 := by native_decide
-- Odd p rows: d = −27 (p = 3 ramified, v = 3 ≥ m = 3): 1 + 3 = 4.
example : idealCountBrute (-27) 27 = 4 := by native_decide
-- d = −72 (D = −8, f = 3, p = 3 split), m = 2 = v: trivial branch, 4.
example : idealCountBrute (-72) 9 = 4 := by native_decide
-- d = −36 (D = −4, f = 3, p = 3 inert), m = 2 = v: trivial branch, 4.
example : idealCountBrute (-36) 9 = 4 := by native_decide

/-! ## Invertible counts (Corollary 3.1.3*) -/

-- Ramified, case branch: d = −16, m = 3: 2^w = 2 (exceeds the thesis's TOTAL of 1 — E2's
-- internal contradiction).
example : invertibleIdealCountBrute (-16) 8 = 2 := by native_decide
example : invertibleIdealCountBrute (-16) 32 = 2 := by native_decide

-- ERRATA E5 boundary (p = 2, D odd, m = v = 2w−2 → trivial branch):
-- d = −48, m = 2 → 2 (thesis regime gave 6 > total 3);
-- d = −112, m = 2 → 2 (thesis regime gave −2);
-- d = −192, m = 4 → 4 = 2^{m/2} (thesis regime gave 12 > total 7).
example : invertibleIdealCountBrute (-48) 4 = 2 := by native_decide
example : invertibleIdealCountBrute (-112) 4 = 2 := by native_decide
example : invertibleIdealCountBrute (-192) 16 = 4 := by native_decide

-- Inert, odd m: 0 (the case line missing from the thesis display, E6.1).
example : invertibleIdealCountBrute (-48) 8 = 0 := by native_decide
example : invertibleIdealCountBrute (-192) 32 = 0 := by native_decide

-- Inert, even m, case branch: d = −48, m = 4: 2^w + 2^{w−1} = 6
-- (corroborated by the 12 representations of 16 by the two reduced forms of disc −48).
example : invertibleIdealCountBrute (-48) 16 = 6 := by native_decide

-- Odd p boundary rows (m = v ≥ 2w → case branch; ERRATA E5 "do not harmonize"):
-- d = −72 (3 split), m = 2: (3 − 1)(2 + 1 − 2) = 2, NOT p^{m/2} = 3;
-- d = −36 (3 inert), m = 2: 3 + 1 = 4;
-- d = −27 (3 ramified), m = 3: 3.
example : invertibleIdealCountBrute (-72) 9 = 2 := by native_decide
example : invertibleIdealCountBrute (-36) 9 = 4 := by native_decide
example : invertibleIdealCountBrute (-27) 27 = 3 := by native_decide

/-! ## Maximal-order sanity rows (Proposition 3.1.1; f = 1, every ideal invertible) -/

-- d = −4: 5 splits (m + 1 = 3); 3 inert, m = 2 (count 1).
example : idealCountBrute (-4) 25 = 3 := by native_decide
example : idealCountBrute (-4) 9 = 1 := by native_decide
example : invertibleIdealCountBrute (-4) 25 = 3 := by native_decide
example : invertibleIdealCountBrute (-4) 9 = 1 := by native_decide
-- d = −3: 7 splits (m + 1 = 3).
example : idealCountBrute (-3) 49 = 3 := by native_decide

end QuadraticOrder.Harness
