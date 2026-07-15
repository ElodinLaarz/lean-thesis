import QuadraticOrder.Prime
import QuadraticOrder.Defs.Setup

/-!
# The unique prime above a conductor prime

**Thesis.** Remark 3.2.3's load-bearing consequence, never isolated in the
thesis (ERRATA E6.10): for `p ∣ f` there is a UNIQUE prime ideal of `O_d`
containing `p`.  This is the standing hypothesis under which all of
§3.2/§3.3 operates.

**Human-readable companion.** `proofs/prop-3-2-1.md` (statement, proof, and
the promotion of Remark 3.2.3 to a lemma).

**This file states/proves:**

* `existsUnique_isPrime_mem_of_dvd_conductor` — uniqueness of the prime above
  `p ∣ f`

**Proof strategy.** From `p ∣ f` we obtain `p² ∣ d`.  Choose the repeated
root `A` of the defining polynomial modulo `p`: `A = 0` for odd `p`,
and `A = (d²-d)/4` for `p = 2`. Evaluation at `A` gives a surjective map
`O_d → ZMod p`; its kernel is the maximal ideal `(p, tau-A)`. If another
prime contains `p`, primality and `(tau-A)² ∈ (p)` force it to contain
`tau-A`, hence to equal that maximal ideal. This is the quotient argument
of the companion proof made explicit, and it deliberately avoids
Kummer–Dedekind, which excludes conductor primes (PLAN §3.1).

**Status.** WP-A proved. Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-! ### Arithmetic and coordinate helpers

The bundled setup does not store the redundant fact that `d` is congruent
to zero or one modulo four.  The first helper derives it from the fundamental
discriminant and conductor decomposition. -/

private lemma setup_disc [ConductorPrimeSetup d D f p] :
    d % 4 = 0 ∨ d % 4 = 1 := by
  have hf_sq : (f : ZMod 4) ^ 2 = 0 ∨ (f : ZMod 4) ^ 2 = 1 := by
    generalize hx : (f : ZMod 4) = x
    fin_cases x <;> decide
  have hD : (D : ZMod 4) = 0 ∨ (D : ZMod 4) = 1 := by
    rcases ConductorPrimeSetup.D_fund
      (d := d) (D := D) (f := f) (p := p) with hD1 | hD0
    · right
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub D 1 4).2
      have hdiv : (4 : ℤ) ∣ D - 1 :=
        Int.dvd_of_emod_eq_zero (by omega)
      simpa only [neg_sub] using (dvd_neg.mpr hdiv)
    · left
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.dvd_of_emod_eq_zero hD0.1
  have hdcast : (d : ZMod 4) = 0 ∨ (d : ZMod 4) = 1 := by
    rw [ConductorPrimeSetup.d_eq
      (d := d) (D := D) (f := f) (p := p)]
    push_cast
    rcases hD with hD | hD <;> rcases hf_sq with hf | hf
    · left; rw [hD, hf]; ring
    · left; rw [hD, hf]; ring
    · left; rw [hD, hf]; ring
    · right; rw [hD, hf]; ring
  rcases hdcast with hd0 | hd1
  · left
    exact Int.emod_eq_zero_of_dvd
      ((ZMod.intCast_zmod_eq_zero_iff_dvd d 4).mp hd0)
  · right
    have hdvd' : (4 : ℤ) ∣ 1 - d :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub d 1 4).mp hd1
    have hdvd : (4 : ℤ) ∣ d - 1 := by
      simpa only [neg_sub] using (dvd_neg.mpr hdvd')
    have hrem : (d - 1) % 4 = 0 := Int.emod_eq_zero_of_dvd hdvd
    omega

private lemma setup_p_sq_dvd_d [ConductorPrimeSetup d D f p] :
    (p : ℤ) ^ 2 ∣ d := by
  obtain ⟨k, hk⟩ :=
    ConductorPrimeSetup.p_dvd_f (d := d) (D := D) (f := f) (p := p)
  refine ⟨D * (k : ℤ) ^ 2, ?_⟩
  rw [ConductorPrimeSetup.d_eq
    (d := d) (D := D) (f := f) (p := p), hk]
  push_cast
  ring

private lemma exists_coords (x : QuadraticOrder d) :
    ∃ a b : ℤ, x = a • (1 : QuadraticOrder d) + b • tau := by
  -- Reduce a representative polynomial to degree at most one.
  obtain ⟨g, hg, rfl⟩ := (basis (d := d)).exists_eq_aeval x
  have hg' : g.natDegree ≤ 1 := by
    rw [basis_dim] at hg
    omega
  refine ⟨g.coeff 0, g.coeff 1, ?_⟩
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hg']
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  simp only [if_neg (by omega : (0 : ℕ) ≠ 1),
    if_neg (by omega : (1 : ℕ) ≠ 0), if_pos trivial,
    show (basis (d := d)).gen = tau from rfl]
  simp only [algebraMap_int_eq, zsmul_eq_mul, zero_add, add_zero]
  have hcast (z : ℤ) :
      (Int.castRingHom (QuadraticOrder d)) z = (z : QuadraticOrder d) := rfl
  rw [hcast, hcast]
  ring

/-- For a prime `p` dividing the conductor there is exactly one prime ideal of
`O_d` containing `p` (Remark 3.2.3's consequence, promoted; ERRATA E6.10).

The unique `P` is the radical of `(p)`; every `p`-power-index ideal is
`P`-primary (`isPrimary_of_idealIndex_prime_pow`). -/
theorem existsUnique_isPrime_mem_of_dvd_conductor
    [ConductorPrimeSetup d D f p] :
    ∃! P : Ideal (QuadraticOrder d), P.IsPrime ∧ (p : QuadraticOrder d) ∈ P := by
  letI : Fact p.Prime :=
    ⟨ConductorPrimeSetup.p_prime (d := d) (D := D) (f := f) (p := p)⟩
  -- Companion proof, Corollary 6: `p ∣ f` gives `p² ∣ d`, hence `p ∣ d`.
  have hp2dvd : (p : ℤ) ^ 2 ∣ d :=
    setup_p_sq_dvd_d (d := d) (D := D) (f := f) (p := p)
  have hpd : (p : ℤ) ∣ d :=
    dvd_trans (dvd_pow_self (p : ℤ) (by omega)) hp2dvd
  let q : ℤ := (d ^ 2 - d) / 4
  let A : ℤ := if p = 2 then q else 0
  -- The chosen `A` is a root of the defining polynomial modulo `p`.
  have hpA : (p : ℤ) ∣ normEval d A := by
    by_cases hp2 : p = 2
    · subst p
      simp only [A, if_pos rfl]
      have h2d : (2 : ℤ) ∣ d := hpd
      have hconsec : (2 : ℤ) ∣ q * (q + 1) :=
        Int.two_dvd_mul_add_one q
      have hdq : (2 : ℤ) ∣ d * q := dvd_mul_of_dvd_left h2d q
      rw [show normEval d q = q * (q + 1) - d * q by
        simp only [normEval, q]; ring]
      exact dvd_sub hconsec hdq
    · simp only [A, hp2, if_false]
      rw [show normEval d 0 = q by simp [normEval, q]]
      have hdisc := setup_disc (d := d) (D := D) (f := f) (p := p)
      have hpoly := polyMod_eq_X_sq_of_p_dvd_d hp2 hdisc hpd
      have hzero := congrArg (Polynomial.coeff · 0) hpoly
      simp only [polyMod_coeff_zero, Polynomial.coeff_X_pow] at hzero
      have hqzero : (q : ZMod p) = 0 := by simpa [q] using hzero
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd q p).mp hqzero
  -- The repeated-root condition also gives `p ∣ d-2A`.
  have hpLinear : (p : ℤ) ∣ d - 2 * A := by
    by_cases hp2 : p = 2
    · subst p
      simp only [A, if_pos rfl]
      exact dvd_sub hpd (dvd_mul_of_dvd_left (by norm_num) q)
    · simp only [A, hp2, if_false, mul_zero, sub_zero]
      exact hpd
  have hroot :
      Polynomial.eval₂ (Int.castRingHom (ZMod p))
        (A : ZMod p) (poly d) = 0 := by
    have hcast : (normEval d A : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpA
    simpa [poly, normEval] using hcast
  -- Evaluation at the repeated root is onto the residue field.
  let φ : QuadraticOrder d →+* ZMod p :=
    AdjoinRoot.lift (Int.castRingHom (ZMod p)) (A : ZMod p) hroot
  have hφtau : φ (tau (d := d)) = (A : ZMod p) :=
    AdjoinRoot.lift_root hroot
  have hφsurj : Function.Surjective φ := by
    intro z
    refine ⟨(z.val : QuadraticOrder d), ?_⟩
    change φ (z.val : QuadraticOrder d) = z
    rw [map_natCast, ZMod.natCast_zmod_val]
  let J : Ideal (QuadraticOrder d) :=
    Ideal.span {(p : QuadraticOrder d), tau - (A : QuadraticOrder d)}
  -- Coordinate reduction identifies the kernel with `(p, tau-A)`.
  have hJker : J = RingHom.ker φ := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro x (hx | hx)
      · subst x
        change φ (p : QuadraticOrder d) = 0
        rw [map_natCast, CharP.cast_eq_zero]
      · simp only [Set.mem_singleton_iff] at hx
        subst x
        change φ (tau - (A : QuadraticOrder d)) = 0
        rw [map_sub, hφtau, map_intCast]
        exact sub_self _
    · intro x hx
      obtain ⟨a, b, hab⟩ := exists_coords (d := d) x
      have hmod : ((a + b * A : ℤ) : ZMod p) = 0 := by
        have hx' : φ x = 0 := hx
        rw [hab, map_add, map_zsmul, map_one, map_zsmul, hφtau] at hx'
        simpa [zsmul_eq_mul] using hx'
      have hpcoeff : (p : ℤ) ∣ a + b * A :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
      obtain ⟨k, hk⟩ := hpcoeff
      apply Ideal.mem_span_pair.mpr
      refine ⟨(k : QuadraticOrder d), (b : QuadraticOrder d), ?_⟩
      rw [hab]
      simp only [zsmul_eq_mul]
      have hk' := congrArg (fun z : ℤ => (z : QuadraticOrder d)) hk
      push_cast at hk'
      linear_combination -hk'
  have hJmax : J.IsMaximal := by
    rw [hJker]
    exact RingHom.ker_isMaximal_of_surjective φ hφsurj
  -- The double-root identity places `(tau-A)²` in `(p)`.
  have hsquare :
      (tau (d := d) - (A : QuadraticOrder d)) ^ 2 ∈
        Ideal.span {(p : QuadraticOrder d)} := by
    obtain ⟨r, hr⟩ := hpLinear
    obtain ⟨s, hs⟩ := hpA
    have heq :
        (tau (d := d) - (A : QuadraticOrder d)) ^ 2 =
          (d - 2 * A) • (tau - (A : QuadraticOrder d)) -
            normEval d A • (1 : QuadraticOrder d) := by
      have htau := tau_minimal_poly (d := d)
      simp only [normEval, zsmul_eq_mul] at htau ⊢
      push_cast at htau ⊢
      linear_combination htau
    rw [heq, hr, hs]
    apply Ideal.sub_mem
    · rw [zsmul_eq_mul]
      push_cast
      rw [mul_assoc]
      exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_singleton _))
    · rw [zsmul_eq_mul]
      push_cast
      rw [mul_assoc]
      exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_singleton _))
  refine ⟨J, ⟨hJmax.isPrime,
    Ideal.subset_span (Set.mem_insert _ _)⟩, ?_⟩
  intro P hP
  -- Any competing prime contains `tau-A` because it contains its square.
  have htauP : tau (d := d) - (A : QuadraticOrder d) ∈ P := by
    apply hP.1.mem_of_pow_mem 2
    have hspanP : Ideal.span {(p : QuadraticOrder d)} ≤ P := by
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      simpa [hx] using hP.2
    exact hspanP hsquare
  have hJP : J ≤ P := by
    apply Ideal.span_le.mpr
    rintro x (hx | hx)
    · simpa [hx] using hP.2
    · simp only [Set.mem_singleton_iff] at hx
      simpa [hx] using htauP
  -- Maximality of `J` turns this containment into equality.
  exact (hJmax.eq_of_le hP.1.ne_top hJP).symm

end QuadraticOrder
