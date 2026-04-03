import Mathlib.Data.ZMod.Basic

example {p n k : ℕ} (hkn : k ≤ n) [hp_pos : NeZero (p^n)] {x : ZMod (p ^ n)} (hval_dvd : p ^ k ∣ x.val)
    (f : ℕ → ZMod (p ^ n)) (hf_def : f = fun i => ↑(i * p ^ k)) (hn_eq : k + n / 2 = n) (hpk_pos' : 0 < p ^ k) :
    ∃ i ∈ Finset.range (p ^ (n / 2)), f i = x := by
  obtain ⟨i, hi_eq⟩ := hval_dvd
  use i
  have hi_lt : i < p ^ (n / 2) := by
    have : p ^ k * i < p ^ k * p ^ (n / 2) := by
      calc p ^ k * i = x.val := hi_eq.symm
        _ < p ^ n := ZMod.val_lt _
        _ = p ^ (k + n / 2) := by rw [hn_eq]
        _ = p ^ k * p ^ (n / 2) := pow_add _ _ _
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨by rwa [Finset.mem_range], ?_⟩
  rw [hf_def]
  change (↑(i * p ^ k) : ZMod (p ^ n)) = x
  rw [mul_comm, ← hi_eq, ZMod.natCast_zmod_val]
