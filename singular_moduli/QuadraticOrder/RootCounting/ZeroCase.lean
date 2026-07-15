import QuadraticOrder.RootCounting.OddPrimeEvenVal

/-!
# Square-root counting for zero

**Thesis.** Completed Lemma 3.2.6(iii), promoted from the inline zero case in
the proof of Theorem 3.1.2.

**Human-readable companion.** `proofs/lem-3-2-6.md`, Step 5.

**This file states/proves:**

* `cardSqrts_zero` -- modulo `p^n`, zero has `p^(n/2)` square roots.

**Proof strategy.** A residue squares to zero modulo `p^n` exactly when it is
divisible by `p^ceil(n/2)`.  Those residues are parameterized injectively by
`0 ≤ i < p^floor(n/2)`, via `i ↦ i p^ceil(n/2)`.

**Status.** WP-B proved; public statement unchanged from WP-0.
-/

namespace QuadraticOrder

open Finset

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

omit hp2 in
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

end QuadraticOrder

