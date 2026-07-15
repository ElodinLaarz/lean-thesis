import QuadraticOrder.RootCounting.OddPrimeCoprime

/-!
# Square-root counting with nonzero valuation

**Thesis.** Corrected/completed Lemma 3.2.6(i)--(ii).

**Human-readable companion.** `proofs/lem-3-2-6.md`, Steps 1, 3, and 4.

**This file states/proves:**

* `cardSqrts_odd_val_eq_zero` -- a valuation that is odd below the modulus
  exponent admits no square roots, for every prime;
* `prime_pow_dvd_sq_ceil` -- divisibility of a square forces half as much
  divisibility of its root;
* `cardSqrts_prime_pow_even_val_reduction` -- the prime-uniform reduction
  `N_n(p^(2r)u) = p^r N_(n-2r)(u)`;
* `cardSqrts_prime_pow_even_val` -- the resulting odd-prime closed form.

**Proof strategy.** Divisibility of a square forces half the required prime-power
divisibility of its root.  The even-valuation theorem then gives an explicit bijection:
a residual root `y` and one of `p^r` lift coordinates map to
`p^r y + k p^(n-r)`.  The proof checks surjectivity and injectivity by integer
representatives.  The odd-valuation theorem derives a contradiction from parity of the
valuation.

**Status.** WP-B proved; frozen public statements unchanged.  The prime-uniform
reduction is the extracted structural lemma shared by the odd and two-adic cases.
-/

namespace QuadraticOrder

open Finset

section OddPrimePower

variable (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)

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

omit hp2 in
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
lemma prime_pow_dvd_sq_ceil {a : ℤ} (hpp : Prime (p : ℤ)) (n : ℕ)
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

/-- When `2r < n`, the substitution `x = p^r · y` reduces the square-root count at
modulus `p^n` to the unit-level count at modulus `p^(n-2r)`, with `p^r` choices in
each reduction fiber.  This prime-uniform form is the common structural step behind
both the odd-prime theorem and the corrected `p = 2` theorem. -/
theorem cardSqrts_prime_pow_even_val_reduction (n r : ℕ)
    (u : ℤ) (hr : 2 * r < n) :
    cardSqrts (p ^ n) ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) =
      cardSqrts (p ^ (n - 2 * r)) (u : ZMod (p ^ (n - 2 * r))) * p ^ r := by
  have hdvd : ∀ x : ZMod (p ^ n),
      x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) →
        (p : ZMod (p ^ n)) ^ r ∣ x := by
    intro x hx
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    push_cast at hx
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have hdvd_int : (p : ℤ) ^ n ∣ a ^ 2 - (p : ℤ) ^ (2 * r) * u := by
      have h0 : ((a ^ 2 - (p : ℤ) ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) = 0 := by
        push_cast; exact sub_eq_zero.mpr hx
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
    have h_div : (p : ℤ) ^ (2 * r) ∣ a ^ 2 := by
      have hpow : (p : ℤ) ^ (2 * r) ∣ (p : ℤ) ^ n := pow_dvd_pow _ (by omega)
      have hdiff := dvd_trans hpow hdvd_int
      have hpu : (p : ℤ) ^ (2 * r) ∣ (p : ℤ) ^ (2 * r) * u := dvd_mul_right _ _
      have := dvd_add hdiff hpu
      rwa [sub_add_cancel] at this
    obtain ⟨b, hb⟩ := prime_pow_dvd_sq_ceil p hpp (2 * r) h_div
    rw [show (2 * r + 1) / 2 = r from by omega] at hb
    rw [hb]
    push_cast
    exact dvd_mul_right _ _
  classical
  set S_y := univ.filter (fun y : ZMod (p^(n - 2 * r)) =>
    y ^ 2 = (u : ZMod (p^(n - 2 * r))))
  set f : ZMod (p^(n - 2 * r)) × ℕ → ZMod (p ^ n) := fun ⟨y, k⟩ =>
    (p : ZMod (p ^ n)) ^ r * ↑(y.val) +
      ↑k * (p : ZMod (p ^ n)) ^ (n - r) with hf_def
  have h_eq : univ.filter (fun x : ZMod (p ^ n) =>
      x ^ 2 = ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n))) =
      (S_y ×ˢ Finset.range (p ^ r)).image f := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_product, mem_range]
    constructor
    · -- x is a solution → x is in image
      intro hx
      have hdvd_val : p ^ r ∣ x.val := by
        obtain ⟨z, hx_div⟩ := hdvd x hx
        have h_eq : x.val = (p ^ r * z.val) % p ^ n := by
          rw [hx_div]
          have : (p : ZMod (p ^ n)) ^ r = ↑(p ^ r) := by push_cast; rfl
          rw [this, ZMod.val_mul, ZMod.val_natCast]
          have h_mod : z.val = z.val % (p ^ n) := (Nat.mod_eq_of_lt z.val_lt).symm
          nth_rw 1 [h_mod]
          exact (Nat.mul_mod (p ^ r) z.val (p ^ n)).symm
        rw [h_eq]
        have h_dvd : p ^ r ∣ p ^ n := pow_dvd_pow _ (by omega)
        rw [Nat.dvd_mod_iff h_dvd]
        exact dvd_mul_right _ _
      obtain ⟨y', hy'⟩ := hdvd_val
      have hdvd_int : (p : ℤ) ^ n ∣ (x.val : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u := by
        have h0 : (((x.val : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) = 0 := by
          push_cast
          rw [ZMod.natCast_zmod_val]
          rw [hx]
          push_cast
          ring
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
      have h_subst : (x.val : ℤ) ^ 2 = (p : ℤ) ^ (2 * r) * (y' : ℤ) ^ 2 := by
        rw [hy']
        push_cast
        ring
      rw [h_subst] at hdvd_int
      have key : (p : ℤ) ^ (2 * r) * (y' : ℤ) ^ 2 - (p : ℤ) ^ (2 * r) * u =
          (p : ℤ) ^ (2 * r) * ((y' : ℤ) ^ 2 - u) := by ring
      rw [key] at hdvd_int
      have hpne : (p : ℤ) ^ (2 * r) ≠ 0 := pow_ne_zero _ (Nat.prime_iff_prime_int.mp hp.out).ne_zero
      have hnsplit : (p : ℤ) ^ n = (p : ℤ) ^ (2 * r) * (p : ℤ) ^ (n - 2 * r) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [hnsplit, mul_dvd_mul_iff_left hpne] at hdvd_int
      have hy_sq : (↑y' : ZMod (p^(n - 2 * r))) ^ 2 = ↑u := by
        have h_eq : (((y' : ℤ) ^ 2 - u : ℤ) : ZMod (p^(n - 2 * r))) = 0 := by
          rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
        have h_eq' : (↑y' : ZMod (p^(n - 2 * r))) ^ 2 - ↑u = 0 := by
          push_cast at h_eq
          exact h_eq
        exact sub_eq_zero.mp h_eq'
      let y0 : ZMod (p^(n - 2 * r)) := ↑y'
      let k : ℕ := (y' / p^(n - 2 * r)) % p^r
      refine ⟨⟨y0, k⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
      · -- y0 in S_y
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hy_sq⟩
      · -- k in range
        exact Nat.mod_lt _ (pow_pos (Nat.Prime.pos hp.out) _)
      · -- f(y0, k) = x
        rw [hf_def]
        dsimp
        set A := p ^ (n - 2 * r)
        set B := p ^ r
        set C := p ^ (n - r)
        set D := p ^ n
        have hAB : A * B = C := by
          dsimp [A, B, C]
          rw [← pow_add]
          congr 1
          omega
        have hBC : B * C = D := by
          dsimp [B, C, D]
          rw [← pow_add]
          congr 1
          omega
        have h1 := Nat.div_add_mod y' A
        have h2 := Nat.div_add_mod (y' / A) B
        have h_subst : y' = A * (B * ((y' / A) / B) + (y' / A) % B) + y' % A := by
          nth_rw 1 [← h1]
          rw [h2]
        have h_mul : B * y' = B * A * B * ((y' / A) / B) +
            B * A * ((y' / A) % B) + B * (y' % A) := by
          have h_eq : B * y' =
              B * (A * (B * ((y' / A) / B) + (y' / A) % B) + y' % A) := by
            conv_rhs => rw [← h_subst]
          rw [h_eq]
          ring
        rw [mul_comm B A, hAB] at h_mul
        rw [mul_comm C B, hBC] at h_mul
        have h_zmod : ((B * y' : ℕ) : ZMod (p^n)) =
            ((D * ((y' / A) / B) + C * k + B * (y' % A) : ℕ) : ZMod (p^n)) := by
          rw [h_mul]
        have h_D : ((D * ((y' / A) / B) : ℕ) : ZMod (p^n)) = 0 := by
          dsimp [D]
          rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
        rw [Nat.cast_add, Nat.cast_add] at h_zmod
        rw [h_D, zero_add] at h_zmod
        rw [← hy'] at h_zmod
        simp only [ZMod.natCast_val, ZMod.cast_id] at h_zmod
        rw [h_zmod]
        conv_lhs =>
          arg 1
          arg 2
          arg 1
          arg 1
          change (y' : ZMod A)
        rw [ZMod.val_natCast]
        dsimp [A, B, C]
        push_cast
        ring
    · -- x is in image → x is a solution
      rintro ⟨⟨y, k⟩, ⟨⟨hy_y, hy_k⟩, rfl⟩⟩
      have hy_sq' : y ^ 2 = (u : ZMod (p^(n - 2 * r))) := (Finset.mem_filter.mp hy_y).2
      have hdvd : (p : ℤ) ^ (n - 2 * r) ∣ (y.val : ℤ) ^ 2 - u := by
        have h0 : (((y.val : ℤ) ^ 2 - u : ℤ) : ZMod (p^(n - 2 * r))) = 0 := by
          push_cast
          rw [ZMod.natCast_zmod_val]
          exact sub_eq_zero.mpr hy_sq'
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow] at h0
      obtain ⟨m, hm⟩ := hdvd
      have h_eq_int' : (y.val : ℤ) ^ 2 =
          u + (p : ℤ) ^ (n - 2 * r) * m := by linarith
      have : ((p : ZMod (p ^ n)) ^ r * ↑(y.val) +
          ↑k * (p : ZMod (p ^ n)) ^ (n - r)) ^ 2 =
          (p : ZMod (p ^ n)) ^ (2 * r) * (↑(y.val) : ZMod (p ^ n)) ^ 2 +
          2 * (p : ZMod (p ^ n)) ^ n * ↑(y.val) * ↑k +
          ↑k ^ 2 * (p : ZMod (p ^ n)) ^ (2 * n - 2 * r) := by
        have h_pow_add : (p : ZMod (p ^ n)) ^ r *
            (p : ZMod (p ^ n)) ^ (n - r) = (p : ZMod (p ^ n)) ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        have h_expand : ((p : ZMod (p ^ n)) ^ r * ↑(y.val) +
            ↑k * (p : ZMod (p ^ n)) ^ (n - r)) ^ 2 =
          (p : ZMod (p ^ n)) ^ (2 * r) * (↑(y.val) : ZMod (p ^ n)) ^ 2 +
          2 * ((p : ZMod (p ^ n)) ^ r * (p : ZMod (p ^ n)) ^ (n - r)) * ↑(y.val) * ↑k +
          ↑k ^ 2 * (p : ZMod (p ^ n)) ^ (2 * (n - r)) := by ring
        rw [h_expand, h_pow_add]
        have : 2 * (n - r) = 2 * n - 2 * r := by omega
        rw [this]
      rw [this]
      have hpn : (p : ZMod (p ^ n)) ^ n = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      simp only [hpn, zero_mul, mul_zero, add_zero]
      have hp2n : (p : ZMod (p ^ n)) ^ (2 * n - 2 * r) = 0 := by
        have : 2 * n - 2 * r = n + (n - 2 * r) := by omega
        rw [this, pow_add, hpn, zero_mul]
      rw [hp2n, mul_zero, add_zero]
      have h_val_sq : ((y.val : ℤ) : ZMod (p^n)) ^ 2 =
          ((u + (p : ℤ) ^ (n - 2 * r) * m : ℤ) : ZMod (p^n)) := by
        rw [← h_eq_int']
        push_cast; rfl
      push_cast at h_val_sq
      rw [h_val_sq]
      have h_expand : (p : ZMod (p ^ n)) ^ (2 * r) *
          ((u : ZMod (p ^ n)) +
            (p : ZMod (p ^ n)) ^ (n - 2 * r) * (m : ZMod (p ^ n))) =
          (p : ZMod (p ^ n)) ^ (2 * r) * (u : ZMod (p ^ n)) +
            (p : ZMod (p ^ n)) ^ (2 * r) *
              (p : ZMod (p ^ n)) ^ (n - 2 * r) * (m : ZMod (p ^ n)) := by ring
      rw [h_expand]
      have h_combine : (p : ZMod (p ^ n)) ^ (2 * r) *
          (p : ZMod (p ^ n)) ^ (n - 2 * r) = (p : ZMod (p ^ n)) ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [h_combine, hpn, zero_mul, add_zero]
      push_cast; rfl
  unfold cardSqrts
  rw [h_eq]
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_range]
  · -- f is injective on domain
    rintro ⟨y1, k1⟩ hy1 ⟨y2, k2⟩ hy2 hf_eq
    obtain ⟨hy1_y, hy1_k⟩ := Finset.mem_product.mp hy1
    obtain ⟨hy2_y, hy2_k⟩ := Finset.mem_product.mp hy2
    obtain ⟨_, hy1_sq⟩ := Finset.mem_filter.mp hy1_y
    obtain ⟨_, hy2_sq⟩ := Finset.mem_filter.mp hy2_y
    have hk1 : k1 < p ^ r := Finset.mem_range.mp hy1_k
    have hk2 : k2 < p ^ r := Finset.mem_range.mp hy2_k
    dsimp [f] at hf_eq
    have h_add1 : r + (n - 2 * r) = n - r := by omega
    have h_sub : (p ^ r - 1) * p ^ (n - r) = p ^ n - p ^ (n - r) := by
      rw [Nat.sub_mul, one_mul, ← pow_add]
      have h_add2 : r + (n - r) = n := by omega
      rw [h_add2]
    have h_le : p ^ (n - r) ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2_lt1 : p ^ r * y1.val < p ^ (n - r) := by
      have hy1_lt : y1.val < p ^ (n - 2 * r) := y1.val_lt
      have h2 := Nat.mul_lt_mul_of_pos_left hy1_lt (pow_pos (Nat.Prime.pos hp.out) r)
      rw [← pow_add, h_add1] at h2
      exact h2
    have h2_lt2 : p ^ r * y2.val < p ^ (n - r) := by
      have hy2_lt : y2.val < p ^ (n - 2 * r) := y2.val_lt
      have h2 := Nat.mul_lt_mul_of_pos_left hy2_lt (pow_pos (Nat.Prime.pos hp.out) r)
      rw [← pow_add, h_add1] at h2
      exact h2
    have h_lt1 : p ^ r * y1.val + k1 * p ^ (n - r) < p ^ n := by
      have hk1_le : k1 ≤ p ^ r - 1 := Nat.le_sub_one_of_lt hk1
      have h1 : k1 * p ^ (n - r) ≤ (p ^ r - 1) * p ^ (n - r) := Nat.mul_le_mul_right _ hk1_le
      rw [h_sub] at h1
      calc p ^ r * y1.val + k1 * p ^ (n - r)
        _ < p ^ (n - r) + k1 * p ^ (n - r) := Nat.add_lt_add_right h2_lt1 _
        _ ≤ p ^ (n - r) + (p ^ n - p ^ (n - r)) := Nat.add_le_add_left h1 _
        _ = p ^ n := Nat.add_sub_cancel' h_le
    have h_lt2 : p ^ r * y2.val + k2 * p ^ (n - r) < p ^ n := by
      have hk2_le : k2 ≤ p ^ r - 1 := Nat.le_sub_one_of_lt hk2
      have h1 : k2 * p ^ (n - r) ≤ (p ^ r - 1) * p ^ (n - r) := Nat.mul_le_mul_right _ hk2_le
      rw [h_sub] at h1
      calc p ^ r * y2.val + k2 * p ^ (n - r)
        _ < p ^ (n - r) + k2 * p ^ (n - r) := Nat.add_lt_add_right h2_lt2 _
        _ ≤ p ^ (n - r) + (p ^ n - p ^ (n - r)) := Nat.add_le_add_left h1 _
        _ = p ^ n := Nat.add_sub_cancel' h_le
    have h_eq1 : (↑(p ^ r * y1.val + k1 * p ^ (n - r)) : ZMod (p ^ n)) =
        ↑p ^ r * ↑y1.val + ↑k1 * ↑p ^ (n - r) := by
      push_cast
      rfl
    have h_eq2 : (↑(p ^ r * y2.val + k2 * p ^ (n - r)) : ZMod (p ^ n)) =
        ↑p ^ r * ↑y2.val + ↑k2 * ↑p ^ (n - r) := by
      push_cast
      rfl
    have h_val1 : (↑(p ^ r * y1.val + k1 * p ^ (n - r)) : ZMod (p ^ n)).val =
        p ^ r * y1.val + k1 * p ^ (n - r) :=
      ZMod.val_natCast_of_lt h_lt1
    have h_val2 : (↑(p ^ r * y2.val + k2 * p ^ (n - r)) : ZMod (p ^ n)).val =
        p ^ r * y2.val + k2 * p ^ (n - r) :=
      ZMod.val_natCast_of_lt h_lt2
    rw [← h_eq1, ← h_eq2] at hf_eq
    have hf_eq_val := congr_arg ZMod.val hf_eq
    rw [h_val1, h_val2] at hf_eq_val
    have h_mod1 : (p ^ r * y1.val + k1 * p ^ (n - r)) % p ^ (n - r) = p ^ r * y1.val := by
      rw [mul_comm k1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2_lt1]
    have h_mod2 : (p ^ r * y2.val + k2 * p ^ (n - r)) % p ^ (n - r) = p ^ r * y2.val := by
      rw [mul_comm k2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2_lt2]
    have h_mod_eq : p ^ r * y1.val = p ^ r * y2.val := by
      rw [← h_mod1, ← h_mod2, hf_eq_val]
    have hy_eq : y1.val = y2.val := by
      have hp_pos : 0 < p ^ r := pow_pos hp.out.pos r
      exact Nat.eq_of_mul_eq_mul_left hp_pos h_mod_eq
    have hy_eq' : y1 = y2 := by
      have hp_pow_pos : 0 < p ^ (n - 2 * r) := pow_pos hp.out.pos (n - 2 * r)
      haveI : NeZero (p ^ (n - 2 * r)) := ⟨hp_pow_pos.ne'⟩
      exact ZMod.val_injective _ hy_eq
    have hk_eq : k1 = k2 := by
      have h_subst : p ^ r * y1.val + k1 * p ^ (n - r) = p ^ r * y1.val + k2 * p ^ (n - r) := by
        rw [← h_mod_eq] at hf_eq_val
        exact hf_eq_val
      have h_cancel := Nat.add_left_cancel h_subst
      have hp_pow_pos : 0 < p ^ (n - r) := pow_pos hp.out.pos (n - r)
      exact Nat.eq_of_mul_eq_mul_right hp_pow_pos h_cancel
    exact Prod.ext hy_eq' hk_eq

/-- When `c = p^{2r} · u` with `p ∤ u`, `p` odd, and `2r < n`, the number of
square roots is `2p^r` when `u` is a quadratic residue modulo `p`, and zero otherwise. -/
theorem cardSqrts_prime_pow_even_val (hp2 : p ≠ 2) (n r : ℕ)
    (u : ℤ) (hr : 2 * r < n) (hu : ¬ (p : ℤ) ∣ u) :
    cardSqrts (p ^ n) ((p ^ (2 * r) * u : ℤ) : ZMod (p ^ n)) =
      if legendreSym p u = 1 then 2 * p ^ r else 0 := by
  rw [cardSqrts_prime_pow_even_val_reduction p n r u hr]
  rw [cardSqrts_prime_pow_coprime p hp2 (n - 2 * r) (by omega) u hu]
  split_ifs <;> ring

end OddPrimePower

end QuadraticOrder
