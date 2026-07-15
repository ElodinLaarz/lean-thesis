import QuadraticOrder.RootCounting.ZeroCase
import ForMathlib.Data.ZMod.SqrtCard

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

**This file states/proves:**

* `cardSqrts_two`, `cardSqrts_four_odd`, and `cardSqrts_eight` -- the finite
  unit-level base cases;
* `cardSqrts_two_pow_even_val` — the number of `x ∈ ℤ/2^s` with
  `x² ≡ 2^{2r}·u`, for odd `u` and `2r < s`:
  `2^r` when `s − 2r = 1` (always solvable);
  `2^{r+1}` when `s − 2r = 2` and `u ≡ 1 (mod 4)`, else `0`;
  `2^{r+2}` when `s − 2r ≥ 3` and `u ≡ 1 (mod 8)`, else `0`.

The odd-valuation vanishing (`x² ≡ 2^{2r+1}·u` has no solutions for
`2r + 1 < s`) is already proved in full generality — including `p = 2` — as
`cardSqrts_odd_val_eq_zero` in `RootCounting/OddPrimeEvenVal.lean`.

**Proof strategy.** Step 1 of the companion proof is
`cardSqrts_prime_pow_even_val_reduction`, the prime-uniform bijection obtained by
factoring `x = 2^r·y`; it contributes the factor `2^r`.  At residual exponents
one and two, the counts are the finite base cases `cardSqrts_two` and
`cardSqrts_four_odd`.  For residual exponent at least three,
`ZMod.sqrtCard_two_pow_unit` proves that the squaring kernel on units has order
four and that its image consists exactly of the units congruent to one modulo
eight.  Multiplying these unit-level counts by `2^r` gives the three displayed
branches.

**Status.** WP-B proved.  Statement frozen by WP-0 and unchanged.
-/

namespace QuadraticOrder

/-- In `ZMod 2`, squaring is the identity, so every residue has one square root. -/
theorem cardSqrts_two (u : ZMod 2) : cardSqrts 2 u = 1 := by
  fin_cases u <;> decide

/-- In `ZMod 4`, an odd residue has two square roots exactly when it is one. -/
theorem cardSqrts_four_odd (u : ZMod 4) (hu : u = 1 ∨ u = 3) :
    cardSqrts 4 u = if u = 1 then 2 else 0 := by
  rcases hu with rfl | rfl <;> decide

/-- In `ZMod 8`, an odd residue has four square roots exactly when it is one. -/
theorem cardSqrts_eight (u : ZMod 8) (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    cardSqrts 8 u = if u = 1 then 4 else 0 := by
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- Transporting an integer square-root count across equal positive moduli does not
change the count.  Keeping this transport explicit avoids dependent rewriting of the
`NeZero` instance carried by `cardSqrts`. -/
private lemma cardSqrts_intCast_congr {m n : ℕ} [NeZero m] [NeZero n]
    (h : m = n) (u : ℤ) :
    cardSqrts m (u : ZMod m) = cardSqrts n (u : ZMod n) := by
  subst n
  rfl

/-- Solutions of `x² ≡ 2^{2r}·u (mod 2^s)` for odd `u`, `2r < s` (Lemma 3.2.6,
`p = 2`, corrected form).  The residue conditions and the count are functions
of `s − 2r` — see the module docstring warning (ERRATA E3). -/
theorem cardSqrts_two_pow_even_val (s r : ℕ) (u : ℤ)
    (hr : 2 * r < s) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ s) ((2 ^ (2 * r) * u : ℤ) : ZMod (2 ^ s)) =
      if s - 2 * r = 1 then 2 ^ r
      else if s - 2 * r = 2 then (if u % 4 = 1 then 2 ^ (r + 1) else 0)
      else (if u % 8 = 1 then 2 ^ (r + 2) else 0) := by
  -- Companion Step 1: factor every root as `2^r y`; the remaining ambiguity has size `2^r`.
  have hreduce := cardSqrts_prime_pow_even_val_reduction 2 s r u hr
  norm_num at hreduce
  push_cast
  rw [hreduce]
  have ht_pos : 0 < s - 2 * r := by omega
  by_cases ht_one : s - 2 * r = 1
  · -- Companion Step 2(c): every odd class modulo two is one, with one square root.
    rw [if_pos ht_one]
    have hroot :
        cardSqrts (2 ^ (s - 2 * r)) (u : ZMod (2 ^ (s - 2 * r))) = 1 := by
      have hpow : 2 ^ (s - 2 * r) = 2 := by norm_num [ht_one]
      exact (cardSqrts_intCast_congr hpow u).trans (cardSqrts_two (u : ZMod 2))
    rw [hroot, one_mul]
  by_cases ht_two : s - 2 * r = 2
  · -- Companion Step 2(d): the two odd roots modulo four both square to one.
    rw [if_neg ht_one, if_pos ht_two]
    have hu_mod_two : u % 2 = 1 := by simpa using hu
    have hu_mod_four : u % 4 = 1 ∨ u % 4 = 3 := by
      have hcompat := Int.emod_emod_of_dvd u (show (2 : ℤ) ∣ 4 by norm_num)
      have hnonneg := Int.emod_nonneg u (by norm_num : (4 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos u (by norm_num : (0 : ℤ) < 4)
      rw [hu_mod_two] at hcompat
      omega
    have hu_four : (u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3 := by
      rcases hu_mod_four with h | h
      · exact Or.inl <| (ZMod.intCast_eq_intCast_iff' u 1 4).2 (by norm_num [h])
      · exact Or.inr <| (ZMod.intCast_eq_intCast_iff' u 3 4).2 (by norm_num [h])
    have hcast_iff : (u : ZMod 4) = 1 ↔ u % 4 = 1 := by
      exact (ZMod.intCast_eq_intCast_iff' u 1 4).trans (by norm_num)
    have hroot :
        cardSqrts (2 ^ (s - 2 * r)) (u : ZMod (2 ^ (s - 2 * r))) =
          if u % 4 = 1 then 2 else 0 := by
      have hpow : 2 ^ (s - 2 * r) = 4 := by norm_num [ht_two]
      exact (cardSqrts_intCast_congr hpow u).trans <| by
        simpa [hcast_iff] using cardSqrts_four_odd (u : ZMod 4) hu_four
    rw [hroot]
    by_cases h : u % 4 = 1
    · simp [h, pow_succ]
      ring
    · simp [h]
  · -- Companion Step 2(e--f): from exponent three onward, the unit count is zero or four.
    rw [if_neg ht_one, if_neg ht_two]
    have ht_three : 3 ≤ s - 2 * r := by omega
    have hunit :
        cardSqrts (2 ^ (s - 2 * r)) (u : ZMod (2 ^ (s - 2 * r))) =
          if u % 8 = 1 then 4 else 0 :=
      ZMod.sqrtCard_two_pow_unit (s - 2 * r) ht_three u hu
    rw [hunit]
    by_cases h : u % 8 = 1
    · simp [h, pow_add]
      ring
    · simp [h]

end QuadraticOrder
