import QuadraticOrder.RootCounting.Defs

/-!
# Square-root counting for units at odd prime powers

**Thesis.** Corrected/completed Lemma 3.2.6(i), the odd-prime unit case.

**Human-readable companion.** `proofs/lem-3-2-6.md`, Step 2(a)--(b).

**This file states/proves:**

* `cardSqrts_prime` -- the Legendre-symbol root count modulo an odd prime;
* `cardSqrts_prime_pow_coprime` -- unique Hensel lifting through odd prime powers.

**Proof strategy.** The base count is Mathlib's Legendre-symbol theorem.  For the
prime-power result, every root modulo `p^(k+1)` has a unique lift among its `p`
possible lifts modulo `p^(k+2)`, because the derivative `2x` is a unit.  The proof
makes the lift coordinate and the fiberwise cardinality argument explicit.

**Divergence from thesis.** The quadratic-residue condition is normalized modulo `p`;
the proof shows this is equivalent to solvability modulo every positive power of `p`.

**Status.** WP-B proved; public statements unchanged from WP-0.
-/

namespace QuadraticOrder

open Finset

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

-- Linear order on `ZMod p` is not available, so we use `legendreSym`.
end PrimeBase

/-! ## Odd prime powers -/

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

/-- For odd prime `p` and `p ∤ c`, each of the 0 or 2 roots mod `p` lifts
uniquely through all `ZMod (p^n)` by Hensel's lemma. -/
theorem cardSqrts_prime_pow_coprime (hp2 : p ≠ 2) (n : ℕ) (hn : 0 < n)
    (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    cardSqrts (p ^ n) ((c : ℤ) : ZMod (p ^ n)) =
      if legendreSym p c = 1 then 2 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  clear hn
  induction k with
  | zero =>
    have h_equiv : ∀ (m : ℕ) [NeZero m] (hm : m = p),
        cardSqrts m ((c : ℤ) : ZMod m) = cardSqrts p ((c : ℤ) : ZMod p) := by
      intro m _ hm
      subst hm
      rfl
    have hp_eq : p ^ Nat.succ 0 = p := by rw [pow_succ, pow_zero, one_mul]
    rw [h_equiv (p ^ Nat.succ 0) hp_eq]
    have h_prime := cardSqrts_prime p hp2 c
    by_cases h : legendreSym p c = 1
    · rw [h] at h_prime
      rw [if_pos h]
      omega
    · rw [if_neg h]
      have h_c_nz : (c : ZMod p) ≠ 0 := by
        intro h0
        apply hc
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0
      rcases legendreSym.eq_one_or_neg_one p h_c_nz with h_pos | h_neg
      · exact False.elim (h h_pos)
      · rw [h_neg] at h_prime
        omega
  | succ k ih =>
    have h_fiber : ∀ (x : ZMod (p^(k+1))) (y : ZMod (p^(k+2))), ZMod.cast y = x ↔
      ∃ (t : ZMod p), y = (x.val : ZMod (p^(k+2))) +
        (t.val : ZMod (p^(k+2))) * (p^(k+1) : ZMod (p^(k+2))) := by
      intro x y
      constructor
      · intro h
        have h_val : (ZMod.cast y : ZMod (p^(k+1))).val = x.val := by rw [h]
        have h_mod : y.val % p^(k+1) = x.val := by
          have h_val : (ZMod.cast y : ZMod (p^(k+1))).val = x.val := by rw [h]
          rw [ZMod.cast_eq_val] at h_val
          rw [ZMod.val_natCast] at h_val
          exact h_val
        let t := y.val / p^(k+1)
        have h_y_val : y.val = x.val + t * p^(k+1) := by
          dsimp [t]
          have h_div_add_mod := Nat.div_add_mod y.val (p^(k+1))
          rw [h_mod] at h_div_add_mod
          rw [mul_comm (p^(k+1))] at h_div_add_mod
          rw [add_comm] at h_div_add_mod
          exact h_div_add_mod.symm
        have h_t_lt : t < p := by
          dsimp [t]
          apply Nat.div_lt_of_lt_mul
          have h_y_lt : y.val < p^(k+2) := y.val_lt
          have h_pow : p^(k+2) = p * p^(k+1) := by ring
          linarith
        have h_t_val : ((t : ZMod p).val : ZMod (p^(k+2))) = (t : ZMod (p^(k+2))) := by
          rw [ZMod.val_cast_of_lt h_t_lt]
        use (t : ZMod p)
        rw [h_t_val]
        apply ZMod.val_injective
        rw [ZMod.val_add]
        rw [ZMod.val_mul]
        have h_x_lt : x.val < p^(k+2) := by
          have h1 := x.val_lt
          have hp_two_le := Nat.Prime.two_le hp.out
          have h_pow : p^(k+2) = p^(k+1) * p := by ring
          have : 1 ≤ p := by omega
          nlinarith
        have h_t_lt' : t < p^(k+2) := by
          have hp_two_le := Nat.Prime.two_le hp.out
          have h_pow : p^(k+2) = p^(k+1) * p := by ring
          have : 0 < p^(k+1) := by positivity
          nlinarith
        have h_p_pow_lt : p^(k+1) < p^(k+2) := by
          have hp_two_le := Nat.Prime.two_le hp.out
          have h_pow : p^(k+2) = p^(k+1) * p := by ring
          have : 0 < p^(k+1) := by positivity
          nlinarith
        rw [ZMod.val_cast_of_lt h_x_lt]
        rw [ZMod.val_cast_of_lt h_t_lt']
        have h_pow_eq : (p : ZMod (p^(k+2))) ^ (k+1) = ((p^(k+1) : ℕ) : ZMod (p^(k+2))) := by
          norm_cast
        rw [h_pow_eq]
        rw [ZMod.val_cast_of_lt h_p_pow_lt]
        -- Goal is y.val = (x.val + t * p^(k+1) % p^(k+2)) % p^(k+2)
        have h_t_mul_lt : t * p^(k+1) < p^(k+2) := by
          have hp_two_le := Nat.Prime.two_le hp.out
          have h_pow : p^(k+2) = p^(k+1) * p := by ring
          have : 0 < p^(k+1) := by positivity
          nlinarith
        rw [Nat.mod_eq_of_lt h_t_mul_lt]
        -- Goal is y.val = (x.val + t * p^(k+1)) % p^(k+2)
        rw [← h_y_val]
        -- Goal is y.val = y.val % p^(k+2)
        rw [Nat.mod_eq_of_lt y.val_lt]
      · rintro ⟨t, rfl⟩
        have h_dvd : p^(k+1) ∣ p^(k+2) := pow_dvd_pow p (by omega)
        rw [ZMod.cast_add h_dvd]
        rw [ZMod.cast_mul h_dvd]
        have h_pow : ((p : ZMod (p^(k+2))) ^ (k+1)) = ((p ^ (k+1) : ℕ) : ZMod (p^(k+2))) := by simp
        rw [h_pow]
        have h_cast :
            (ZMod.cast ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) :
              ZMod (p ^ (k + 1))) = 0 := by
          rw [ZMod.cast_natCast h_dvd]
          rw [ZMod.natCast_self]
        have h_id : (ZMod.cast ((x.val : ℕ) : ZMod (p ^ (k + 2))) : ZMod (p ^ (k + 1))) = x := by
          rw [ZMod.cast_natCast h_dvd]
          rw [ZMod.natCast_val]
          rw [ZMod.cast_id]
        rw [h_cast]
        simp only [mul_zero, add_zero]
        exact h_id
    have h_map : ∀ (y : ZMod (p^(k+2))), y^2 = c → (ZMod.cast y : ZMod (p^(k+1)))^2 = c := by
      intro y hy
      have h_dvd : p^(k+1) ∣ p^(k+2) := pow_dvd_pow p (by omega)
      rw [pow_two] at hy ⊢
      rw [← ZMod.cast_mul h_dvd]
      rw [hy]
      exact ZMod.cast_intCast h_dvd c
    have h_lift : ∀ (x : ZMod (p^(k+1))), x^2 = c →
        ∃! (y : ZMod (p^(k+2))), y.cast = x ∧ y^2 = c := by
      intro x hx
      have h_pow_sq : ((p ^ (k + 1) : ℕ) : ZMod (p ^ (k + 2))) ^ 2 = 0 := by
        rw [pow_two]
        rw [← Nat.cast_mul]
        have h_pow_add : p^(k+1) * p^(k+1) = p^(2*k+2) := by ring
        rw [h_pow_add]
        have h_dvd : p^(k+2) ∣ p^(2*k+2) := pow_dvd_pow p (by omega)
        obtain ⟨m, hm⟩ := h_dvd
        rw [hm]
        rw [Nat.cast_mul]
        rw [show ((p^(k+2) : ℕ) : ZMod (p^(k+2))) = 0 by rw [ZMod.natCast_self]]
        rw [zero_mul]
      have h_dvd_diff : (p : ℤ)^(k+1) ∣ (c : ℤ) - (x.val : ℤ)^2 := by
        have h_sub : (((x.val : ℤ)^2 - c : ℤ) : ZMod (p^(k+1))) = 0 := by
          push_cast
          simp [hx]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_sub
        have h_neg : (c : ℤ) - (x.val : ℤ)^2 = -((x.val : ℤ)^2 - c) := by ring
        rw [h_neg]
        exact dvd_neg.mpr h_sub
      have h_x_nz : ((x.val : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        have h0' : ((x.val : ℤ) : ZMod p) = 0 := by
          push_cast
          exact h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0'
        obtain ⟨L, hL⟩ := h_dvd_diff
        have h_c_eq : (c : ℤ) = (x.val : ℤ)^2 + (p : ℤ)^(k+1) * L := by linarith
        have h_p_dvd_c : (p : ℤ) ∣ c := by
          rw [h_c_eq]
          apply dvd_add
          · rw [pow_two]
            exact dvd_mul_of_dvd_left h0' (x.val : ℤ)
          · have hp_dvd_pow : (p : ℤ) ∣ (p : ℤ)^(k+1) := dvd_pow_self _ (by omega)
            exact dvd_mul_of_dvd_left hp_dvd_pow L
        exact hc h_p_dvd_c
      obtain ⟨L, hL⟩ := h_dvd_diff
      let t : ZMod p := (L : ZMod p) * (2 * (x.val : ZMod p))⁻¹
      have h_c_eq' : (c : ZMod (p^(k+2))) = (x.val : ZMod (p^(k+2)))^2 +
          (p^(k+1) : ZMod (p^(k+2))) * (L : ZMod (p^(k+2))) := by
        have hL' : (c : ℤ) = (x.val : ℤ)^2 + (p : ℤ)^(k+1) * L := by linarith
        have h_cast := congr_arg (fun (a : ℤ) => (a : ZMod (p^(k+2)))) hL'
        push_cast at h_cast
        exact h_cast
      have h_t_prop : (2 : ZMod p) * ((x.val : ℕ) : ZMod p) * t = (L : ZMod p) := by
        dsimp [t]
        have h_assoc :
            (2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
                ((L : ZMod p) * ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹) =
              ((2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
                ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹) * (L : ZMod p) := by
          ring
        rw [h_assoc]
        have h_inv : (2 : ZMod p) * ((x.val : ℕ) : ZMod p) *
            ((2 : ZMod p) * ((x.val : ℕ) : ZMod p))⁻¹ = 1 := by
          apply mul_inv_cancel₀
          intro h_zero
          cases mul_eq_zero.mp h_zero with
          | inl h2 =>
            have h_p_dvd_2 : (p : ℤ) ∣ 2 := by
              have h2' : ((2 : ℤ) : ZMod p) = 0 := by
                push_cast
                exact h2
              rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2'
              exact h2'
            have hp_le_2 : p ≤ 2 := by
              have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by decide) h_p_dvd_2
              omega
            have hp_ge_2 : 2 ≤ p := Fact.out (p := Nat.Prime p) |>.two_le
            have : p = 2 := by omega
            exact hp2 this
          | inr hx =>
            exact h_x_nz hx
        rw [h_inv, one_mul]
      let y : ZMod (p^(k+2)) := (x.val : ZMod (p^(k+2))) +
        (t.val : ZMod (p^(k+2))) * (p^(k+1) : ZMod (p^(k+2)))
      have hy_cast : y.cast = x := by
        have h_fib := h_fiber x y
        rw [h_fib]
        use t
      have hy_sq : y^2 = c := by
        have h_expand : y^2 = (x.val : ZMod (p^(k+2)))^2 +
            2 * (x.val : ZMod (p^(k+2))) * (t.val : ZMod (p^(k+2))) *
              (p^(k+1) : ZMod (p^(k+2))) +
            (t.val : ZMod (p^(k+2)))^2 * ((p^(k+1) : ZMod (p^(k+2))))^2 := by
          dsimp [y]
          ring
        rw [h_expand]
        have h_pow_sq' : ((p : ZMod (p^(k+2)))^(k+1))^2 = 0 := by
          rw [← Nat.cast_pow]
          exact h_pow_sq
        rw [h_pow_sq']
        simp only [mul_zero, add_zero]
        rw [h_c_eq']
        have h_t_prop' : (p : ℤ) ∣ 2 * (x.val : ℤ) * (t.val : ℤ) - L := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          have h_eq : (2 : ZMod p) * (x.val : ZMod p) * (t.val : ZMod p) - (L : ZMod p) = 0 := by
            rw [ZMod.natCast_zmod_val t]
            rw [h_t_prop]
            exact sub_self _
          exact h_eq
        obtain ⟨m', hm'⟩ := h_t_prop'
        have h_eq' : 2 * (x.val : ℤ) * (t.val : ℤ) * (p : ℤ)^(k+1) =
            (L : ℤ) * (p : ℤ)^(k+1) + m' * (p : ℤ)^(k+2) := by
          calc 2 * (x.val : ℤ) * (t.val : ℤ) * (p : ℤ)^(k+1)
            _ = (L + p * m') * (p : ℤ)^(k+1) := by
              rw [show 2 * (x.val : ℤ) * (t.val : ℤ) = L + p * m' by linarith]
            _ = (L : ℤ) * (p : ℤ)^(k+1) + m' * (p : ℤ)^(k+2) := by ring
        have h_cast := congr_arg (fun (a : ℤ) => (a : ZMod (p^(k+2)))) h_eq'
        push_cast at h_cast
        have hp_pow_zero : (p : ZMod (p^(k+2)))^(k+2) = 0 := by
          rw [← Nat.cast_pow]
          exact ZMod.natCast_self (p^(k+2))
        rw [hp_pow_zero, mul_zero, add_zero] at h_cast
        rw [h_cast, mul_comm (L : ZMod (p^(k+2)))]
      refine ⟨y, ⟨hy_cast, hy_sq⟩, ?_⟩
      intro y' ⟨hy'_cast, hy'_sq⟩
      have h_fib' := h_fiber x y' |>.mp hy'_cast
      obtain ⟨t', ht'⟩ := h_fib'
      have hy'_expand : y'^2 = (x.val : ZMod (p^(k+2)))^2 +
          2 * (x.val : ZMod (p^(k+2))) * (t'.val : ZMod (p^(k+2))) *
            (p^(k+1) : ZMod (p^(k+2))) := by
        rw [ht']
        have : (↑x.val + ↑t'.val * ↑p ^ (k + 1) : ZMod (p^(k+2)))^2 =
            ↑x.val ^ 2 + 2 * ↑x.val * ↑t'.val * ↑p ^ (k + 1) +
              ↑t'.val ^ 2 * (↑p ^ (k + 1)) ^ 2 := by
          ring
        rw [this]
        have h_pow_sq' : ((p : ZMod (p^(k+2)))^(k+1))^2 = 0 := by
          rw [← Nat.cast_pow]
          exact h_pow_sq
        rw [h_pow_sq']
        simp only [mul_zero, add_zero]
      have h_eq'_mod :
          2 * (x.val : ZMod (p^(k+2))) * (t'.val : ZMod (p^(k+2))) *
              (p^(k+1) : ZMod (p^(k+2))) =
            (p^(k+1) : ZMod (p^(k+2))) * (L : ZMod (p^(k+2))) := by
        have h_eq : y'^2 = c := hy'_sq
        rw [hy'_expand] at h_eq
        rw [h_c_eq'] at h_eq
        exact add_left_cancel h_eq
      have h_dvd : (p : ℤ)^(k+2) ∣ (2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ)^(k+1) := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd
          ((2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ)^(k+1)) (p^(k+2))).mp ?_
        have h_ring :
            (((2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ)^(k+1) : ℤ) :
              ZMod (p^(k+2))) =
              2 * (x.val : ZMod (p^(k+2))) * (t'.val : ZMod (p^(k+2))) *
                (p : ZMod (p^(k+2)))^(k+1) -
              (p : ZMod (p^(k+2)))^(k+1) * (L : ZMod (p^(k+2))) := by
          push_cast
          ring
        rw [h_ring]
        rw [h_eq'_mod]
        exact sub_self _
      have hp_pos : p > 0 := Fact.out (p := Nat.Prime p) |>.pos
      have hp_pow_nz : (p : ℤ)^(k+1) ≠ 0 := by positivity
      have h_div : (p : ℤ) ∣ 2 * (x.val : ℤ) * (t'.val : ℤ) - L := by
        have h_dvd' : (p : ℤ) * (p : ℤ)^(k+1) ∣
            (2 * (x.val : ℤ) * (t'.val : ℤ) - L) * (p : ℤ)^(k+1) := by
          rw [mul_comm, ← pow_succ]
          exact h_dvd
        exact Int.dvd_of_mul_dvd_mul_right hp_pow_nz h_dvd'
      have h_t'_prop : (2 : ZMod p) * (x.val : ZMod p) * t' = (L : ZMod p) := by
        have h_zero : ((2 * (x.val : ℤ) * (t'.val : ℤ) - L : ℤ) : ZMod p) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact h_div
        push_cast at h_zero
        have : (2 : ZMod p) * (x.val : ZMod p) * (t'.val : ZMod p) =
            (L : ZMod p) := sub_eq_zero.mp h_zero
        rw [← ZMod.natCast_zmod_val t']
        exact this
      have h_x_nz' : (2 : ZMod p) * (x.val : ZMod p) ≠ 0 := by
        intro h_zero
        cases mul_eq_zero.mp h_zero with
        | inl h2 =>
          have h_p_dvd_2 : (p : ℤ) ∣ 2 := by
            have h2' : ((2 : ℤ) : ZMod p) = 0 := by
              push_cast
              exact h2
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2'
            exact h2'
          have hp_le_2 : p ≤ 2 := by
            have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by decide) h_p_dvd_2
            omega
          have hp_ge_2 : 2 ≤ p := Fact.out (p := Nat.Prime p) |>.two_le
          have : p = 2 := by omega
          exact hp2 this
        | inr hx =>
          exact h_x_nz hx
      have ht_eq : t' = t := by
        have : (2 : ZMod p) * (x.val : ZMod p) * t' = (2 : ZMod p) * (x.val : ZMod p) * t := by
          rw [h_t'_prop, h_t_prop]
        exact mul_left_cancel₀ h_x_nz' this
      have ht_val_eq : t'.val = t.val := by rw [ht_eq]
      rw [ht']
      rw [ht_val_eq]
    have h_fiber_card : ∀ x ∈ univ.filter
        (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1)))),
        ((univ.filter (fun y : ZMod (p^(k+2)) => y ^ 2 = (c : ZMod (p^(k+2))))).filter
          (fun y => ZMod.cast y = x)).card = 1 := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨y, ⟨hy_cast, hy_sq⟩, hy_uniq⟩ := h_lift x hx
      rw [Finset.card_eq_one]
      refine ⟨y, ?_⟩
      ext y'
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hy'_sq, hy'_cast⟩
        exact hy_uniq y' ⟨hy'_cast, hy'_sq⟩
      · rintro rfl
        exact ⟨hy_sq, hy_cast⟩
    unfold cardSqrts
    have h_sum : (univ.filter (fun y : ZMod (p^(k+2)) => y ^ 2 = (c : ZMod (p^(k+2))))).card =
        ∑ x ∈ univ.filter (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1)))),
          ((univ.filter (fun y : ZMod (p^(k+2)) => y ^ 2 = (c : ZMod (p^(k+2))))).filter
            (fun y => ZMod.cast y = x)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro y hy
      have hy_sq : y^2 = c := (Finset.mem_filter.mp hy).2
      have h_map_goal : (ZMod.cast y : ZMod (p^(k+1)))^2 = c := h_map y hy_sq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_map_goal⟩
    
    rw [h_sum]
    have h_sum_one :
        ∑ x ∈ univ.filter (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1)))),
            ((univ.filter
              (fun y : ZMod (p^(k+2)) => y ^ 2 = (c : ZMod (p^(k+2))))).filter
                (fun y => ZMod.cast y = x)).card =
          ∑ x ∈ univ.filter
            (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1)))), 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact h_fiber_card x hx
    rw [h_sum_one]
    rw [Finset.sum_const]
    have h_smul :
        (univ.filter
          (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1))))).card • (1 : ℕ) =
        (univ.filter
          (fun x : ZMod (p^(k+1)) => x ^ 2 = (c : ZMod (p^(k+1))))).card := by
      simp
    rw [h_smul]
    exact ih
end OddPrimePower

end QuadraticOrder
