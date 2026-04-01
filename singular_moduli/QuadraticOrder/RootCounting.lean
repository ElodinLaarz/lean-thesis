import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Layer 3: Root Counting for Quadratic Congruences

This file counts solutions to `x² ≡ c (mod p^n)` for prime powers `p^n`.
These are the "analytic inputs" for the ideal-counting theorems (Layer 4).

## Main results

* `cardSqrts_prime`: base case mod an odd prime, via the Legendre symbol
* `cardSqrts_prime_pow_coprime`: mod `p^n` for odd `p` and `gcd(c, p) = 1`
* `cardSqrts_prime_pow_even_val`: mod `p^n` when `c = p^{2r} · u`
* `cardSqrts_odd_val_eq_zero`: no solutions when `v_p(c)` is odd
* `cardSqrts_zero`: all solutions when `c ≡ 0 (mod p^n)`
* `cardSqrts_two_pow_coprime`: the `p = 2` analogue

## Strategy

For odd primes the key observation is that each simple root of `x² ≡ c (mod p)`
lifts uniquely to `ZMod (p^n)` by Hensel's lemma (the derivative `2x` is nonzero
mod `p` at any root, since `p` is odd and `p ∤ x`). So the count is constant
across all `n ≥ 1`. The `p = 2` case requires separate analysis because the
derivative `2x ≡ 0 (mod 2)` always vanishes.
-/

namespace QuadraticOrder

open Finset

/-! ## Definition -/

/-- The number of elements `x` in `ZMod n` satisfying `x ^ 2 = c`. -/
def cardSqrts (n : ℕ) [NeZero n] (c : ZMod n) : ℕ :=
  (univ.filter (fun x : ZMod n => x ^ 2 = c)).card

/-! ## Base case: odd prime `p` -/

section PrimeBase

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `Finset.filter` definition of `cardSqrts` agrees with the `Set.toFinset`
formulation used by Mathlib's `legendreSym.card_sqrts`. -/
private lemma filter_eq_toFinset (c : ZMod p) :
    univ.filter (fun x : ZMod p => x ^ 2 = c) =
    {x : ZMod p | x ^ 2 = c}.toFinset := by
  ext x; simp [Finset.mem_filter]

/-- For an odd prime `p`, the number of solutions to `x² = c` in `ZMod p`
equals `legendreSym p c + 1`:
  - `0` solutions when `c` is a non-residue (`legendreSym p c = -1`)
  - `1` solution when `c = 0` (`legendreSym p c = 0`)
  - `2` solutions when `c` is a nonzero QR (`legendreSym p c = 1`) -/
theorem cardSqrts_prime (hp2 : p ≠ 2) (c : ℤ) :
    (cardSqrts p ((c : ℤ) : ZMod p) : ℤ) = legendreSym p c + 1 := by
  unfold cardSqrts
  rw [filter_eq_toFinset]
  exact legendreSym.card_sqrts p hp2 c

end PrimeBase

/-! ## Odd prime powers -/

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

/-- For odd prime `p` and `p ∤ c`, each of the 0 or 2 roots mod `p` lifts
uniquely through all `ZMod (p^n)` by Hensel's lemma (the derivative `2x₀` is
a unit mod `p` at any root `x₀`), so the count is preserved. -/
theorem cardSqrts_prime_pow_coprime (n : ℕ) (hn : 0 < n)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    cardSqrts (p ^ n) ((c : ℤ) : ZMod (p ^ n)) =
      if legendreSym p c = 1 then 2 else 0 := by
  sorry -- requires discrete Hensel lifting for ZMod

/-- When `c = p^{2r} · u` with `p ∤ u` and `2r < n`, the substitution `x = p^r · y`
reduces the problem to solving `y² ≡ u (mod p^{n-2r})`.
Each solution for `y` gives `p^r` values of `x`, yielding `2 · p^r` or `0` total. -/
theorem cardSqrts_prime_pow_even_val (n r : ℕ)
    (u : ℤ) (hr : 2 * r < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) =
      if legendreSym p u = 1 then 2 * p ^ r else 0 := by
  sorry -- requires substitution argument + cardSqrts_prime_pow_coprime

/-- If the `p`-adic valuation of `c` is odd and less than `n`, then `x² ≡ c (mod p^n)`
has no solutions, because `v_p(x²)` is always even while `v_p(c)` is odd. -/
theorem cardSqrts_odd_val_eq_zero (n r : ℕ)
    (u : ℤ) (hr : 2 * r + 1 < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r + 1) * u : ℤ) : ZMod (p ^ n)) = 0 := by
  sorry -- valuation parity argument

/-- When `c ≡ 0 (mod p^n)`, every multiple of `p^{⌈n/2⌉}` is a solution,
giving `p^{⌊n/2⌋}` solutions in `ZMod (p^n)`. -/
theorem cardSqrts_zero (n : ℕ) (hn : 0 < n) :
    cardSqrts (p ^ n) (0 : ZMod (p ^ n)) = p ^ (n / 2) := by
  sorry -- counting argument on multiples of p^{⌈n/2⌉}

end OddPrimePower

/-! ## Powers of 2

The `p = 2` case requires separate treatment because the derivative `2x` of
`x²` vanishes mod 2, so Hensel lifting is not directly applicable. Instead,
the structure of `(ℤ/2^n ℤ)ˣ ≅ ℤ/2 × ℤ/2^{n-2}` (for `n ≥ 3`) determines
the square classes.

Key facts:
- mod 2: `x² = x`, so every `c` has exactly 1 root
- mod 4: `x² ∈ {0, 1}`, so odd `c` has 2 roots iff `c ≡ 1 (mod 4)`
- mod 2^n (n ≥ 3): odd `c` has 4 roots iff `c ≡ 1 (mod 8)`, else 0
-/

section TwoPower

/-- In `ZMod 2`, squaring is the identity, so every element has exactly one
square root. -/
theorem cardSqrts_two (u : ZMod 2) : cardSqrts 2 u = 1 := by
  fin_cases u <;> decide

/-- In `ZMod 4`, the squares are `{0, 1}`. For odd `u`, there are 2 roots
when `u ≡ 1 (mod 4)` and none when `u ≡ 3 (mod 4)`. -/
theorem cardSqrts_four_odd (u : ZMod 4) (hu : u = 1 ∨ u = 3) :
    cardSqrts 4 u = if u = 1 then 2 else 0 := by
  rcases hu with rfl | rfl <;> decide

/-- For `n ≥ 3` and odd `u`, `x² ≡ u (mod 2^n)` has 4 solutions when
`u ≡ 1 (mod 8)`, and no solutions otherwise. -/
theorem cardSqrts_two_pow_coprime (n : ℕ) (hn : 3 ≤ n) (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ n) ((u : ℤ) : ZMod (2 ^ n)) =
      if (u : ZMod 8) = 1 then 4 else 0 := by
  sorry -- uses structure of (ZMod (2^n))ˣ ≅ ℤ/2 × ℤ/2^{n-2}

/-- For `c = 2^{2r} · u` with `u` odd and `n - 2r ≥ 3`,
the count is `4 · 2^r` when `u ≡ 1 (mod 8)`, else 0. -/
theorem cardSqrts_two_pow_even_val (n r : ℕ) (hn : 3 ≤ n - 2 * r)
    (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ n) ((2 ^ (2 * r) * u : ℤ) : ZMod (2 ^ n)) =
      if (u : ZMod 8) = 1 then 4 * 2 ^ r else 0 := by
  sorry -- substitution x = 2^r · y + cardSqrts_two_pow_coprime

end TwoPower

end QuadraticOrder
