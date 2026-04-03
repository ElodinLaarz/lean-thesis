import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Layer 3: Root Counting for Quadratic Congruences

This file counts solutions to `x² ≡ c (mod p^n)` for prime powers `p^n`.
These are the "analytic inputs" for the ideal-counting theorems (Layer 4).
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

/-- For an odd prime `p`, the number of solutions to `x² = c` in `ZMod p`
equals `legendreSym p c + 1`. -/
theorem cardSqrts_prime (hp2 : p ≠ 2) (c : ℤ) :
    (cardSqrts p ((c : ℤ) : ZMod p) : ℤ) = legendreSym p c + 1 := by
  unfold cardSqrts
  have : (univ.filter (fun x : ZMod p => x ^ 2 = (c : ZMod p))) =
      {x : ZMod p | x ^ 2 = (c : ZMod p)}.toFinset := by
    ext x; simp [Finset.mem_filter]
  rw [this]
  exact legendreSym.card_sqrts p hp2 c

end PrimeBase

/-! ## Odd prime powers -/

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

/-- For odd prime `p` and `p ∤ c`, each of the 0 or 2 roots mod `p` lifts
uniquely through all `ZMod (p^n)` by Hensel's lemma. -/
theorem cardSqrts_prime_pow_coprime (n : ℕ) (hn : 0 < n)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    cardSqrts (p ^ n) ((c : ℤ) : ZMod (p ^ n)) =
      if legendreSym p c = 1 then 2 else 0 := by
  sorry

/-- When `c = p^{2r} · u` with `p ∤ u` and `2r < n`, the substitution `x = p^r · y`
reduces the problem to solving `y² ≡ u (mod p^{n-2r})`. -/
theorem cardSqrts_prime_pow_even_val (n r : ℕ)
    (u : ℤ) (hr : 2 * r < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) =
      if legendreSym p u = 1 then 2 * p ^ r else 0 := by
  sorry

omit hp in
/-- If `p` is prime and `p^(2r+1) ∣ a²`, then `p^(r+1) ∣ a`. -/
private lemma prime_pow_dvd_sq_imp (r : ℕ) {a : ℤ} (hpp : Prime (p : ℤ))
    (h : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2) : (p : ℤ) ^ (r + 1) ∣ a := by
  induction r generalizing a with
  | zero =>
    simp only [mul_zero, zero_add, pow_one] at h ⊢
    exact hpp.dvd_of_dvd_pow h
  | succ r ih =>
    have h_weaker : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2 :=
      dvd_trans (pow_dvd_pow _ (by omega)) h
    have h_r1 : (p : ℤ) ^ (r + 1) ∣ a := ih h_weaker
    obtain ⟨b, rfl⟩ := h_r1
    have h_pb : (p : ℤ) ∣ b ^ 2 := by
      have key : (p : ℤ) ^ (2 * r + 2) * (p : ℤ) ∣ (p : ℤ) ^ (2 * r + 2) * b ^ 2 := by
        have : (p : ℤ) ^ (2 * (r + 1) + 1) = (p : ℤ) ^ (2 * r + 2) * p := by
          rw [show 2 * (r + 1) + 1 = 2 * r + 2 + 1 from by omega, pow_succ]
        rw [this] at h
        convert h using 1; ring
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hpp.ne_zero)).mp key
    obtain ⟨c, rfl⟩ := hpp.dvd_of_dvd_pow h_pb
    rw [show (r + 1) + 1 = r + 2 from by omega, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)

/-- If the `p`-adic valuation of `c` is odd and less than `n`, then `x² ≡ c (mod p^n)`
has no solutions. -/
theorem cardSqrts_odd_val_eq_zero (n r : ℕ)
    (u : ℤ) (hr : 2 * r + 1 < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r + 1) * u : ℤ) : ZMod (p ^ n)) = 0 := by
  unfold cardSqrts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  push_cast
  intro h
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hdvd : (p : ℤ) ^ n ∣ a ^ 2 - (p : ℤ) ^ (2 * r + 1) * u := by
    have h0 : ((a ^ 2 - (p : ℤ) ^ (2 * r + 1) * u : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast; exact sub_eq_zero.mpr h
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
  have h1 : (p : ℤ) ^ (2 * r + 1) ∣ a ^ 2 := by
    have hpow : (p : ℤ) ^ (2 * r + 1) ∣ (p : ℤ) ^ n := pow_dvd_pow _ (by omega)
    have hdiff := dvd_trans hpow hdvd
    have hpu : (p : ℤ) ^ (2 * r + 1) ∣ (p : ℤ) ^ (2 * r + 1) * u := dvd_mul_right _ _
    have := dvd_add hdiff hpu
    rwa [sub_add_cancel] at this
  obtain ⟨b, rfl⟩ := prime_pow_dvd_sq_imp p r hpp h1
  have key : ((p : ℤ) ^ (r + 1) * b) ^ 2 - (p : ℤ) ^ (2 * r + 1) * u =
      (p : ℤ) ^ (2 * r + 1) * ((p : ℤ) * b ^ 2 - u) := by ring
  rw [key] at hdvd
  have hpne : (p : ℤ) ^ (2 * r + 1) ≠ 0 := pow_ne_zero _ hpp.ne_zero
  have hnsplit : (p : ℤ) ^ n = (p : ℤ) ^ (2 * r + 1) * (p : ℤ) ^ (n - (2 * r + 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [hnsplit, mul_dvd_mul_iff_left hpne] at hdvd
  apply hu
  have h3 : (p : ℤ) ∣ (p : ℤ) * b ^ 2 - u := by
    calc (p : ℤ) = (p : ℤ) ^ 1 := (pow_one _).symm
    _ ∣ (p : ℤ) ^ (n - (2 * r + 1)) := pow_dvd_pow _ (by omega)
    _ ∣ (p : ℤ) * b ^ 2 - u := hdvd
  have h4 := dvd_sub (dvd_mul_right (p : ℤ) (b ^ 2)) h3
  rwa [show (p : ℤ) * b ^ 2 - ((p : ℤ) * b ^ 2 - u) = u from by ring] at h4

omit hp hp2 in
/-- If `p` is prime and `p^n ∣ a²`, then `p^⌈n/2⌉ ∣ a`.
Case-split on parity of `n`: the odd case is `prime_pow_dvd_sq_imp`; the even case
`n = 2m` weakens to the odd `p^(2m-1) ∣ a²` case (for `m ≥ 1`). -/
private lemma prime_pow_dvd_sq_ceil {a : ℤ} (hpp : Prime (p : ℤ)) (n : ℕ)
    (h : (p : ℤ) ^ n ∣ a ^ 2) : (p : ℤ) ^ ((n + 1) / 2) ∣ a := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = m + m; ⌈n/2⌉ = m; want p^m ∣ a
    subst hm
    simp only [show (m + m + 1) / 2 = m from by omega]
    rcases m with _ | m
    · simp
    · -- n = (m+1)+(m+1); weaken to p^(2m+1) ∣ a² then apply imp
      exact prime_pow_dvd_sq_imp p m hpp
        (dvd_trans (pow_dvd_pow _ (by omega)) h)
  · -- n = 2*m+1; ⌈n/2⌉ = m+1; this is exactly prime_pow_dvd_sq_imp
    subst hm
    simp only [show (2 * m + 1 + 1) / 2 = m + 1 from by omega]
    exact prime_pow_dvd_sq_imp p m hpp h

/-- When `c ≡ 0 (mod p^n)`, every multiple of `p^⌈n/2⌉` is a solution,
giving `p^⌊n/2⌋` solutions total. -/
theorem cardSqrts_zero (n : ℕ) (hn : 0 < n) :
    cardSqrts (p ^ n) (0 : ZMod (p ^ n)) = p ^ (n / 2) := by
  unfold cardSqrts
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hp_pos : 0 < p := hp.out.pos
  set k := (n + 1) / 2 with hk_def
  have hnk_add : n / 2 + k = n := by omega
  have hpk_pos : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  -- Step 1: x² = 0 in ZMod(p^n) ↔ p^k | x
  have h_iff : ∀ x : ZMod (p ^ n), x ^ 2 = 0 ↔ (p : ZMod (p ^ n)) ^ k ∣ x := by
    intro x; constructor
    · -- Forward: x² = 0 → p^k | x (via prime_pow_dvd_sq_ceil)
      intro hx
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
      have ha2 : (p : ℤ) ^ n ∣ a ^ 2 := by
        have : ((a ^ 2 : ℤ) : ZMod (p ^ n)) = 0 := by push_cast; simpa using hx
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at this
      obtain ⟨b, hb⟩ := prime_pow_dvd_sq_ceil p hpp n ha2
      rw [hb]; push_cast; exact dvd_mul_right _ _
    · -- Backward: p^k | x → x² = 0 (since (↑p)^n = 0 and 2k ≥ n)
      intro ⟨c, hc⟩
      have hp0 : (p : ZMod (p ^ n)) ^ n = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      rw [hc, mul_pow, ← pow_mul,
        show k * 2 = n + (k * 2 - n) from by omega, pow_add, hp0, zero_mul, zero_mul]
  -- Step 2: show filter = image of range(p^(n/2)) under i ↦ ↑(i * p^k)
  classical
  rw [show (univ.filter (fun x : ZMod (p ^ n) => x ^ 2 = 0)) =
           (univ.filter (fun x : ZMod (p ^ n) => (p : ZMod (p ^ n)) ^ k ∣ x)) from
      Finset.filter_congr fun x _ => h_iff x]
  set f : ℕ → ZMod (p ^ n) := fun i => ↑(i * p ^ k) with hf_def
  -- Injectivity of f on range(p^(n/2))
  have hf_inj : Set.InjOn f (Finset.range (p ^ (n / 2))) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only [hf_def] at hab
    rw [ZMod.natCast_eq_natCast_iff] at hab
    have ha' : a * p ^ k < p ^ n := by
      calc a * p ^ k < p ^ (n / 2) * p ^ k := Nat.mul_lt_mul_of_pos_right ha hpk_pos
        _ = p ^ n := by rw [← pow_add, hnk_add]
    have hb' : b * p ^ k < p ^ n := by
      calc b * p ^ k < p ^ (n / 2) * p ^ k := Nat.mul_lt_mul_of_pos_right hb hpk_pos
        _ = p ^ n := by rw [← pow_add, hnk_add]
    have := hab.eq_of_lt_of_lt ha' hb'
    exact mul_right_cancel₀ (by positivity) this
  -- The filter equals the image
  have h_eq : univ.filter (fun x : ZMod (p ^ n) => (p : ZMod (p ^ n)) ^ k ∣ x) =
      (Finset.range (p ^ (n / 2))).image f := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · -- x divisible by p^k → x in image
      intro ⟨c, hc⟩
      have hval_dvd : p ^ k ∣ x.val := by
        have hv : x.val = (p ^ k * c.val) % (p ^ n) := by
          rw [hc, ← Nat.cast_pow, ZMod.val_mul, ZMod.val_natCast]
          have hc_mod : c.val = c.val % (p ^ n) := (Nat.mod_eq_of_lt c.val_lt).symm
          nth_rw 1 [hc_mod]
          exact (Nat.mul_mod (p ^ k) c.val (p ^ n)).symm
        rw [hv]
        have hdvd : p ^ k ∣ p ^ n := pow_dvd_pow p (show k ≤ n by omega)
        rw [Nat.dvd_mod_iff hdvd]
        exact dvd_mul_right _ _
      obtain ⟨i, hi_eq⟩ := hval_dvd
      use i
      have hi_lt : i < p ^ (n / 2) := by
        have : p ^ k * i < p ^ k * p ^ (n / 2) := by
          calc p ^ k * i = x.val := hi_eq.symm
            _ < p ^ n := ZMod.val_lt _
            _ = p ^ (k + n / 2) := by rw [show k + n / 2 = n by omega]
            _ = p ^ k * p ^ (n / 2) := pow_add _ _ _
        exact Nat.lt_of_mul_lt_mul_left this
      refine ⟨by simpa using hi_lt, ?_⟩
      rw [hf_def]
      change (↑(i * p ^ k) : ZMod (p ^ n)) = x
      rw [mul_comm, ← hi_eq, ZMod.natCast_zmod_val]
    · -- x in image → x divisible by p^k
      intro ⟨i, hi, hix⟩
      rw [← hix]
      change (p : ZMod (p ^ n)) ^ k ∣ ↑(i * p ^ k)
      rw [show (↑(i * p ^ k) : ZMod (p ^ n)) =
        (↑i : ZMod (p ^ n)) * (p : ZMod (p ^ n)) ^ k from by push_cast; ring]
      exact dvd_mul_left _ _
  rw [h_eq, Finset.card_image_of_injOn hf_inj, Finset.card_range]


end OddPrimePower

/-! ## Powers of 2 -/

section TwoPower

/-- In `ZMod 2`, squaring is the identity. -/
theorem cardSqrts_two (u : ZMod 2) : cardSqrts 2 u = 1 := by
  fin_cases u <;> decide

/-- In `ZMod 4`, for odd `u`, there are 2 roots or none. -/
theorem cardSqrts_four_odd (u : ZMod 4) (hu : u = 1 ∨ u = 3) :
    cardSqrts 4 u = if u = 1 then 2 else 0 := by
  rcases hu with rfl | rfl <;> decide

/-- For `n ≥ 3` and odd `u`, `x² ≡ u (mod 2^n)` has 4 solutions when `u ≡ 1 (mod 8)`. -/
theorem cardSqrts_two_pow_coprime (n : ℕ) (hn : 3 ≤ n) (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ n) ((u : ℤ) : ZMod (2 ^ n)) =
      if (u : ZMod 8) = 1 then 4 else 0 := by
  sorry

/-- For `c = 2^{2r} · u` with `u` odd and `n - 2r ≥ 3`, the count is `4 · 2^r` or 0. -/
theorem cardSqrts_two_pow_even_val (n r : ℕ) (hn : 3 ≤ n - 2 * r)
    (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    cardSqrts (2 ^ n) ((2 ^ (2 * r) * u : ℤ) : ZMod (2 ^ n)) =
      if (u : ZMod 8) = 1 then 4 * 2 ^ r else 0 := by
  sorry

end TwoPower

end QuadraticOrder
