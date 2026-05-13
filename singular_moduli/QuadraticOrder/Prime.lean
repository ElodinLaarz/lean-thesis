import QuadraticOrder.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Layer 2a: Polynomial reduction of `poly d` mod `p`

This file is the entry point for the prime-classification (split / inert /
ramified) of rational primes in `QuadraticOrder d`. The classification is
governed by the Kronecker / Legendre symbol `(d / p)` of the discriminant.

This file lays the polynomial-level scaffolding: reduction of `poly d` mod
`p`, its degree, its coefficients, and the discriminant identity
`disc = d` (under the valid-discriminant hypothesis `d ≡ 0 ∨ 1 (mod 4)`).

Subsequent PRs will use this scaffolding to prove the split/inert/ramified
characterisation via the factorisation of `polyMod d p` over `ZMod p`.
-/

open Polynomial

namespace QuadraticOrder

variable (d : ℤ) (p : ℕ)

/-- Reduction of the defining polynomial `poly d` modulo `p`, as a
polynomial in `(ZMod p)[X]`. -/
noncomputable def polyMod : (ZMod p)[X] :=
  (poly d).map (Int.castRingHom (ZMod p))

/-- Explicit form: `polyMod d p = X² - d·X + ((d² - d)/4)` over `ZMod p`. -/
lemma polyMod_eq :
    polyMod d p = X ^ 2 - C ((d : ZMod p)) * X
      + C (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  unfold polyMod poly
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X]

/-- The mod-`p` reduction is monic. -/
lemma polyMod_monic : (polyMod d p).Monic :=
  (poly_monic d).map _

variable {d p}

/-- The mod-`p` reduction has degree 2 (requires `p` prime so `ZMod p` is
nontrivial). -/
lemma polyMod_natDegree [Fact p.Prime] : (polyMod d p).natDegree = 2 := by
  unfold polyMod
  rw [(poly_monic d).natDegree_map]
  unfold poly
  compute_degree!

/-- Coefficient of `X²` in `polyMod d p` is `1`. -/
@[simp] lemma polyMod_coeff_two : (polyMod d p).coeff 2 = 1 := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp [Polynomial.coeff_X_pow,
        Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]

/-- Coefficient of `X` in `polyMod d p` is `-d (mod p)`. -/
@[simp] lemma polyMod_coeff_one :
    (polyMod d p).coeff 1 = -(d : ZMod p) := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp [Polynomial.coeff_X_pow,
        Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]

/-- Constant coefficient of `polyMod d p` is `(d² - d)/4 (mod p)`. -/
@[simp] lemma polyMod_coeff_zero :
    (polyMod d p).coeff 0 = (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  unfold polyMod
  rw [Polynomial.coeff_map]
  unfold poly
  simp [Polynomial.coeff_X_pow,
        Mathlib.Tactic.ComputeDegree.coeff_intCast_ite]

/-- Discriminant identity: when `d ≡ 0 ∨ 1 (mod 4)`, the (coefficient-level)
discriminant of the monic-quadratic form of `polyMod d p` equals `d` in
`ZMod p`. This is the key bridge connecting `poly d`'s splitting behaviour
to the Kronecker symbol `(d / p)`. -/
lemma polyMod_discrim_eq (hd : d % 4 = 0 ∨ d % 4 = 1) :
    discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p)
      = (d : ZMod p) := by
  unfold discrim
  have h4dvd : (4 : ℤ) ∣ d ^ 2 - d := by
    have hdd : d ^ 2 - d = d * (d - 1) := by ring
    rw [hdd]
    rcases hd with h | h
    · exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
    · exact Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero (by omega)) _
  have hcancel : (4 : ℤ) * ((d ^ 2 - d) / 4) = d ^ 2 - d :=
    Int.mul_ediv_cancel' h4dvd
  have key : (-d) ^ 2 - 4 * ((d ^ 2 - d) / 4) = d := by
    nlinarith [hcancel]
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) key
  push_cast at hcast
  convert hcast using 1
  ring

/-- Evaluation of `polyMod d p` at `x ∈ ZMod p`: a closed-form expansion.

This reduces evaluation to a quadratic expression in `x` over `ZMod p`. -/
lemma polyMod_eval (x : ZMod p) :
    (polyMod d p).eval x = x ^ 2 - (d : ZMod p) * x + (((d ^ 2 - d) / 4 : ℤ) : ZMod p) := by
  rw [polyMod_eq]
  simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X]

/-- For `p` an odd prime and `d ≡ 0 ∨ 1 (mod 4)`, `polyMod d p` has a root
in `ZMod p` iff `d` is a quadratic residue mod `p` (i.e. `IsSquare (d : ZMod p)`).

This is the polynomial-level bridge connecting `poly d`'s splitting behaviour
to the Kronecker / Legendre symbol `(d / p)`. -/
theorem polyMod_exists_root_iff_isSquare_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ IsSquare (d : ZMod p) := by
  -- Establish `NeZero (2 : ZMod p)` from `p` prime and `p ≠ 2`.
  have hp_prime : p.Prime := Fact.out
  have hp_two_ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
        CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd
    -- p ∣ 2 with p prime forces p ≤ 2, and combined with p ≥ 2 yields p = 2.
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpge : 2 ≤ p := hp_prime.two_le
    exact hp2 (le_antisymm hple hpge)
  have hne2 : NeZero (2 : ZMod p) := ⟨hp_two_ne⟩
  -- Bridge `polyMod` evaluation to standard quadratic form `a*(x*x) + b*x + c = 0`.
  have hquad_iff : ∀ x : ZMod p,
      (polyMod d p).eval x = 0 ↔
        (1 : ZMod p) * (x * x) + (-(d : ZMod p)) * x +
          (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    intro x
    rw [polyMod_eval]
    constructor <;> (intro h; linear_combination h)
  -- Restate the existential using the quadratic form.
  simp_rw [hquad_iff]
  -- Now apply the discriminant characterisation.
  have h1ne : (1 : ZMod p) ≠ 0 := one_ne_zero
  constructor
  · -- Forward: a root gives a square root of the discriminant, which is `d`.
    rintro ⟨x, hx⟩
    have hdsq := discrim_eq_sq_of_quadratic_eq_zero hx
    -- `discrim 1 (-d) ((d^2-d)/4) = (2*1*x + (-d))^2`
    rw [polyMod_discrim_eq hd] at hdsq
    refine ⟨2 * 1 * x + (-(d : ZMod p)), ?_⟩
    linear_combination hdsq
  · -- Reverse: a square `d = s*s` gives a discriminant-square, then `exists_quadratic_eq_zero`.
    rintro ⟨s, hs⟩
    have hdisc_sq : ∃ t : ZMod p,
        discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = t * t := by
      refine ⟨s, ?_⟩
      rw [polyMod_discrim_eq hd, hs]
    exact exists_quadratic_eq_zero h1ne hdisc_sq

/-- `polyMod d p` has a root in `ZMod p` iff the Legendre symbol `(d/p)` is
not `-1`. Equivalently, `d` is either zero (ramified case) or a quadratic
residue (split case) mod `p`. -/
theorem polyMod_exists_root_iff_legendreSym_ne_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ legendreSym p d ≠ -1 := by
  rw [polyMod_exists_root_iff_isSquare_d hp2 hd, Ne, legendreSym.eq_neg_one_iff,
      not_not]

/-- `polyMod d p` has no root in `ZMod p` iff `(d/p) = -1` — the inert case. -/
theorem polyMod_no_root_iff_legendreSym_eq_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (¬ ∃ x : ZMod p, (polyMod d p).eval x = 0) ↔ legendreSym p d = -1 := by
  rw [polyMod_exists_root_iff_legendreSym_ne_neg_one hp2 hd, not_not]

/-- The ramified case: `(d/p) = 0 ↔ p ∣ d`. -/
theorem legendreSym_eq_zero_iff_dvd [Fact p.Prime] :
    legendreSym p d = 0 ↔ (p : ℤ) ∣ d := by
  rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- A monic-quadratic polynomial in `(ZMod p)[X]` splits iff it has a root.
For `polyMod d p` this is the bridge from `polyMod_exists_root_iff_isSquare_d`
to the `Polynomial.Splits` predicate. -/
theorem polyMod_splits_iff_exists_root [Fact p.Prime] :
    (polyMod d p).Splits ↔ ∃ x : ZMod p, (polyMod d p).eval x = 0 := by
  constructor
  · intro hs
    refine hs.exists_eval_eq_zero ?_
    rw [Polynomial.degree_eq_natDegree (polyMod_monic d p).ne_zero, polyMod_natDegree]
    decide
  · rintro ⟨x, hx⟩
    exact Polynomial.Splits.of_natDegree_eq_two polyMod_natDegree hx

/-- `polyMod d p` splits in `(ZMod p)[X]` iff the Legendre symbol `(d/p)` is
not `-1`. This combines `polyMod_splits_iff_exists_root` with the previously
proved `polyMod_exists_root_iff_legendreSym_ne_neg_one`. -/
theorem polyMod_splits_iff_legendreSym_ne_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (polyMod d p).Splits ↔ legendreSym p d ≠ -1 := by
  rw [polyMod_splits_iff_exists_root,
      polyMod_exists_root_iff_legendreSym_ne_neg_one hp2 hd]

/-- The ramified case at the polynomial level: when `p` is an odd prime
dividing `d` (with `d ≡ 0 ∨ 1 (mod 4)`), the reduction `polyMod d p` is
identically `X²` in `(ZMod p)[X]`. In particular it has the unique root 0
with multiplicity 2, witnessing the ramified behaviour of `(p)` in
`QuadraticOrder d`. -/
theorem polyMod_eq_X_sq_of_p_dvd_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    polyMod d p = X ^ 2 := by
  rw [polyMod_eq]
  -- Show both the linear and constant coefficients are 0 in ZMod p.
  have hd_zmod : (d : ZMod p) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h4dvd : (4 : ℤ) ∣ d ^ 2 - d := by
    have hdd : d ^ 2 - d = d * (d - 1) := by ring
    rw [hdd]
    rcases hd with h | h
    · exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
    · exact Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero (by omega)) _
  have hp_dvd_q : (p : ℤ) ∣ (d ^ 2 - d) / 4 := by
    -- 4 * ((d²-d)/4) = d² - d (by hcancel), and p ∣ d² - d = d*(d-1).
    -- Then p prime, p ∤ 4, so p ∣ (d²-d)/4.
    have hp_dvd_sub : (p : ℤ) ∣ 4 * ((d ^ 2 - d) / 4) := by
      rw [Int.mul_ediv_cancel' h4dvd]
      exact dvd_sub (dvd_pow hpd (by norm_num)) hpd
    have hp_prime_int : Prime (p : ℤ) :=
      Nat.prime_iff_prime_int.mp (Fact.out (p := p.Prime))
    have hp_not_dvd_4 : ¬ (p : ℤ) ∣ 4 := by
      intro hdvd4
      have hp_prime : p.Prime := Fact.out
      have hp_le : (p : ℤ) ≤ 4 := Int.le_of_dvd (by norm_num) hdvd4
      have hpnat_le : p ≤ 4 := by exact_mod_cast hp_le
      have hpnat_ge : 2 ≤ p := hp_prime.two_le
      interval_cases p
      · exact hp2 rfl
      · norm_num at hdvd4
      · exact absurd hp_prime (by decide)
    exact (hp_prime_int.dvd_mul.mp hp_dvd_sub).resolve_left hp_not_dvd_4
  have hq_zmod : (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [hd_zmod, hq_zmod]
  simp

end QuadraticOrder
