import QuadraticOrder.RootCounting

/-!
# Root counting modulo powers of 2 (Lemma 3.2.6, the `p = 2` case)

**Thesis.** Lemma 3.2.6, `p = 2` — completed and CORRECTED per ERRATA E6.5:
the quadratic-residue condition for `p = 2` means `u ≡ 1 (mod min(2^{s−2r}, 8))`,
and the count depends on `s − 2r`, **not** on `s`.

⚠ **ERRATA E3.** Conflating `s` with `s − 2r` when invoking this lemma is
exactly the slip that broke two cases of thesis Theorem 3.1.2.  The statement
below keeps `s − 2r` explicit; implementers of `IdealCount.lean` must pass
`r = w` (`D ≡ 0 (mod 4)`) resp. `r = w − 1` (`D` odd) and track the residual
exponent `s − 2r`, never `s`.

**Human-readable companion.** `proofs/lem-3-2-6.md` (all `p` together, with
the units-group proof).

**This file states:**

* `cardSqrts_two_pow_even_val` — the number of `x ∈ ℤ/2^s` with
  `x² ≡ 2^{2r}·u`, for odd `u` and `2r < s`:
  `2^r` when `s − 2r = 1` (always solvable);
  `2^{r+1}` when `s − 2r = 2` and `u ≡ 1 (mod 4)`, else `0`;
  `2^{r+2}` when `s − 2r ≥ 3` and `u ≡ 1 (mod 8)`, else `0`.

The odd-valuation vanishing (`x² ≡ 2^{2r+1}·u` has no solutions for
`2r + 1 < s`) is already proved in full generality — including `p = 2` — as
`cardSqrts_odd_val_eq_zero` in `RootCounting.lean`.

**Proof strategy** (WP-B): factor `x = 2^r·y`; count `y` with
`y² ≡ u (mod 2^{s−2r})` via the unit-group structure
`(ℤ/2^n)^× ≅ {±1} × ℤ/2^{n−2}` for `n ≥ 3` (squares have index 4, each square
has exactly 4 square roots `±y, 2^{n−1} ± y`), with the degenerate moduli
`n = 1, 2` by inspection (`cardSqrts_two`, `cardSqrts_four_odd` are the base
cases already in `RootCounting.lean`); then multiply by the `2^r` lift
ambiguity, minus the care at the boundary — the full accounting is in
`proofs/lem-3-2-6.md`.

**Status.** WP-B stub (`sorry`).  Statement frozen by WP-0.
-/

namespace QuadraticOrder

/-- Solutions of `x² ≡ 2^{2r}·u (mod 2^s)` for odd `u`, `2r < s` (Lemma 3.2.6,
`p = 2`, corrected form).  The residue conditions and the count are functions
of `s − 2r` — see the module docstring warning (ERRATA E3). -/
theorem cardSqrts_two_pow_even_val (s r : ℕ) (u : ℤ)
    (hr : 2 * r < s) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ s) ((2 ^ (2 * r) * u : ℤ) : ZMod (2 ^ s)) =
      if s - 2 * r = 1 then 2 ^ r
      else if s - 2 * r = 2 then (if u % 4 = 1 then 2 ^ (r + 1) else 0)
      else (if u % 8 = 1 then 2 ^ (r + 2) else 0) := by
  sorry

end QuadraticOrder
