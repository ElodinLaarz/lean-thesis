import QuadraticOrder.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree

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

/-- The split case at the polynomial level: when `p` is an odd prime, `d ≡ 0 ∨ 1
(mod 4)`, and the Legendre symbol `(d/p) = 1` (so `d` is a non-zero quadratic
residue mod `p`), `polyMod d p` has two distinct roots in `ZMod p`. These two
roots witness the splitting `(p) = P₁ · P₂` in `QuadraticOrder d`. -/
theorem polyMod_exists_two_distinct_roots_of_legendreSym_eq_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (h_split : legendreSym p d = 1) :
    ∃ r s : ZMod p, r ≠ s ∧
      (polyMod d p).eval r = 0 ∧ (polyMod d p).eval s = 0 := by
  -- Establish `(2 : ZMod p) ≠ 0` from `p` prime and `p ≠ 2` (same pattern as
  -- `polyMod_exists_root_iff_isSquare_d`).
  have hp_prime : p.Prime := Fact.out
  have hp_two_ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
        CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hdvd
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpge : 2 ≤ p := hp_prime.two_le
    exact hp2 (le_antisymm hple hpge)
  have hne2 : NeZero (2 : ZMod p) := ⟨hp_two_ne⟩
  -- From `(d/p) = 1`: `d ≠ 0 mod p` and `d` is a square mod p.
  have hd_ne_zero : (d : ZMod p) ≠ 0 := by
    intro hd0
    have : legendreSym p d = 0 := (legendreSym.eq_zero_iff p d).mpr hd0
    rw [this] at h_split
    exact absurd h_split (by decide)
  have hsq : IsSquare (d : ZMod p) := (legendreSym.eq_one_iff p hd_ne_zero).mp h_split
  obtain ⟨t, ht⟩ := hsq
  -- `ht : (d : ZMod p) = t * t`
  -- Therefore `t ≠ 0` (else `d = 0 mod p`).
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    apply hd_ne_zero
    rw [ht, ht0, mul_zero]
  -- The discriminant equals `t * t`.
  have hdiscr : discrim (1 : ZMod p) (-(d : ZMod p)) (((d ^ 2 - d) / 4 : ℤ) : ZMod p)
      = t * t := by
    rw [polyMod_discrim_eq hd]; exact ht
  -- Bridge `polyMod` evaluation to the standard quadratic form used by
  -- `quadratic_eq_zero_iff`.
  have hquad_iff : ∀ x : ZMod p,
      (polyMod d p).eval x = 0 ↔
        (1 : ZMod p) * (x * x) + (-(d : ZMod p)) * x +
          (((d ^ 2 - d) / 4 : ℤ) : ZMod p) = 0 := by
    intro x
    rw [polyMod_eval]
    constructor <;> (intro h; linear_combination h)
  -- The two roots from `quadratic_eq_zero_iff` are `(d + t)/2` and `(d - t)/2`.
  refine ⟨((d : ZMod p) + t) / 2, ((d : ZMod p) - t) / 2, ?_, ?_, ?_⟩
  · -- Distinctness: if `r = s` then `t = 0`.
    intro hrs
    apply ht_ne_zero
    -- From `(d+t)/2 = (d-t)/2`, multiply by `2`: `d + t = d - t`, so `2t = 0`.
    have h2t : (2 : ZMod p) * t = 0 := by
      have hmul : 2 * (((d : ZMod p) + t) / 2) = 2 * (((d : ZMod p) - t) / 2) :=
        congrArg (fun x => 2 * x) hrs
      rw [mul_div_cancel₀ _ hp_two_ne, mul_div_cancel₀ _ hp_two_ne] at hmul
      linear_combination hmul
    rcases mul_eq_zero.mp h2t with h | h
    · exact absurd h hp_two_ne
    · exact h
  · -- `((d+t)/2)` is a root.
    rw [hquad_iff]
    rw [quadratic_eq_zero_iff one_ne_zero hdiscr]
    left
    ring
  · -- `((d-t)/2)` is a root.
    rw [hquad_iff]
    rw [quadratic_eq_zero_iff one_ne_zero hdiscr]
    right
    ring

/-- The structural bridge: `QuadraticOrder d / (p)` is ring-equivalent to
`(ZMod p)[X] / (polyMod d p)`. This is the key isomorphism connecting
ideal-theoretic properties of `(p)` in `QuadraticOrder d` to polynomial-level
properties of `polyMod d p` in `(ZMod p)[X]`. It is the foundation on which
the inert/split/ramified ideal-theoretic characterisations are built. -/
noncomputable def quadraticOrderModP_equiv_polyModQuot
    (d : ℤ) (p : ℕ) [Fact p.Prime] :
    (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) ≃+*
      ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) := by
  -- Step 1: rewrite `(p) ⊆ QuadraticOrder d` as the image under
  -- `algebraMap ℤ (QuadraticOrder d) = AdjoinRoot.of (poly d)` of `(p) ⊆ ℤ`.
  have h_span_eq : Ideal.span {(p : QuadraticOrder d)} =
      Ideal.map (AdjoinRoot.of (poly d)) (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  -- Step 2: the polynomial in the target ideal — after transport through
  -- `Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)` — coincides with
  -- `polyMod d p`. Uses `Polynomial.map_map` and
  -- `Int.quotientSpanNatEquivZMod_comp_Quotient_mk`.
  have h_poly_eq :
      (poly d).map ((Int.quotientSpanNatEquivZMod p : _ →+* _).comp
        (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))) = polyMod d p := by
    rw [Int.quotientSpanNatEquivZMod_comp_Quotient_mk]
    rfl
  have h_map_eq :
      (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p) : _ →+* _)
        ((poly d).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))) =
        polyMod d p := by
    change (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p))
        ((poly d).map (Ideal.Quotient.mk _)) = polyMod d p
    rw [Polynomial.mapEquiv_apply, Polynomial.map_map, h_poly_eq]
  have h_map_span :
      Ideal.map (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p) : _ →+* _)
          (Ideal.span {(poly d).map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))}) =
        Ideal.span {polyMod d p} := by
    rw [Ideal.map_span, Set.image_singleton, h_map_eq]
  -- Step 3: compose `Ideal.quotEquivOfEq` with `AdjoinRoot.quotEquivQuotMap`
  -- and `Ideal.quotientEquiv` (the latter transports the polynomial quotient
  -- along the ring equiv `ℤ/(p) ≃+* ZMod p`).
  exact
    (Ideal.quotEquivOfEq h_span_eq).trans <|
      (AdjoinRoot.quotEquivQuotMap (poly d) (Ideal.span {(p : ℤ)})).toRingEquiv.trans <|
        Ideal.quotientEquiv _ (Ideal.span {polyMod d p})
          (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)) h_map_span.symm

/-- The ideal `(p)` in `QuadraticOrder d` is maximal iff `polyMod d p` is
irreducible in `(ZMod p)[X]`. This is the ideal-theoretic inert
characterisation: `(p)` is maximal — equivalently, `(p)` does not factor in
`QuadraticOrder d` — exactly when its mod-`p` polynomial form is irreducible
over `ZMod p`.

Combined with `polyMod_splits_iff_legendreSym_ne_neg_one` (and the field
structure on `(ZMod p)[X] / (irreducible)`), this connects the Legendre
symbol `(d/p) = -1` characterisation to the ring-theoretic notion that
`(p)` remains prime in `QuadraticOrder d`. -/
theorem span_p_isMaximal_iff_irreducible_polyMod
    (d : ℤ) (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : QuadraticOrder d)}).IsMaximal ↔ Irreducible (polyMod d p) := by
  constructor
  · intro hMax
    -- Transport maximality through the ring equiv to get maximality of
    -- `Ideal.span {polyMod d p}` in `(ZMod p)[X]`.
    have hField :
        IsField (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hMax
    have hField' :
        IsField ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) :=
      (quadraticOrderModP_equiv_polyModQuot d p).symm.toMulEquiv.isField hField
    have hMax' : (Ideal.span {polyMod d p}).IsMaximal :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hField'
    -- IsMaximal → IsPrime → Prime → Irreducible (using `polyMod` is nonzero).
    have hne : (polyMod d p) ≠ 0 := (polyMod_monic d p).ne_zero
    have hPrime : Prime (polyMod d p) :=
      (Ideal.span_singleton_prime hne).mp hMax'.isPrime
    exact hPrime.irreducible
  · intro hIrred
    -- `(ZMod p)[X]` is a PID, so irreducible generates a maximal ideal.
    have hMax' : (Ideal.span {polyMod d p}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hIrred
    have hField' :
        IsField ((ZMod p)[X] ⧸ Ideal.span {polyMod d p}) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hMax'
    -- Transport `IsField` back through the ring equiv.
    have hField :
        IsField (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) :=
      (quadraticOrderModP_equiv_polyModQuot d p).toMulEquiv.isField hField'
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hField

/-- `polyMod d p` is irreducible in `(ZMod p)[X]` iff the Legendre symbol
`(d/p) = -1`. Combines the monic-degree-two irreducibility characterisation
with the polynomial-level Legendre bridge already established. -/
theorem polyMod_irreducible_iff_legendreSym_eq_neg_one
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    Irreducible (polyMod d p) ↔ legendreSym p d = -1 := by
  have hne : (polyMod d p) ≠ 0 := (polyMod_monic d p).ne_zero
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three
        (polyMod_monic d p)
        (by rw [polyMod_natDegree]) (by rw [polyMod_natDegree]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  simp_rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def]
  rw [← not_exists, polyMod_no_root_iff_legendreSym_eq_neg_one hp2 hd]

/-- **Issue #7's inert iff at the ideal level**: the ideal `(p)` is maximal
in `QuadraticOrder d` (i.e. `p` is "inert") iff the Legendre symbol
`(d/p) = -1`. Direct composition of `span_p_isMaximal_iff_irreducible_polyMod`
with `polyMod_irreducible_iff_legendreSym_eq_neg_one`. -/
theorem prime_inert_iff
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (Ideal.span {(p : QuadraticOrder d)}).IsMaximal ↔ legendreSym p d = -1 := by
  rw [span_p_isMaximal_iff_irreducible_polyMod,
      polyMod_irreducible_iff_legendreSym_eq_neg_one hp2 hd]

/-- **Ramified-case quotient isomorphism**: when `p ∣ d` (with the
discriminant hypothesis `d ≡ 0 ∨ 1 (mod 4)` and `p ≠ 2`), the quotient
`QuadraticOrder d / (p)` is isomorphic to `(ZMod p)[X] / (X²)`. This makes
the dual-numbers / non-reduced structure of the ramified branch explicit:
the image of `X` in this quotient is nilpotent of order 2, witnessing that
`(p)` is not a radical ideal in `QuadraticOrder d`. -/
noncomputable def quadraticOrderModP_equiv_X_sq_quot
    (d : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    (QuadraticOrder d ⧸ Ideal.span {(p : QuadraticOrder d)}) ≃+*
      ((ZMod p)[X] ⧸ Ideal.span {(X ^ 2 : (ZMod p)[X])}) :=
  (quadraticOrderModP_equiv_polyModQuot d p).trans <|
    Ideal.quotEquivOfEq <| by rw [polyMod_eq_X_sq_of_p_dvd_d hp2 hd hpd]

/-- **Ramification witness**: when `p ∣ d` (with `p ≠ 2`, `d ≡ 0 ∨ 1 (mod 4)`),
`τ²` lies in `(p) ⊆ QuadraticOrder d`. Combined with `τ ∉ (p)` (which holds
generally because `τ` is a Z-basis element), this exhibits `τ + (p)` as a
nonzero nilpotent of order 2 in `QuadraticOrder d / (p)` — the algebraic
fingerprint of ramification of `p` in `QuadraticOrder d`. -/
theorem tau_sq_mem_span_p_of_p_dvd_d
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : d % 4 = 0 ∨ d % 4 = 1)
    (hpd : (p : ℤ) ∣ d) :
    (tau (d := d)) ^ 2 ∈ Ideal.span {(p : QuadraticOrder d)} := by
  -- Extract `p ∣ (d²-d)/4` from the already-proved `polyMod_eq_X_sq_of_p_dvd_d`:
  -- the constant coefficient of `polyMod d p = X^2` is zero in `ZMod p`, and
  -- the constant coefficient is `((d²-d)/4 : ℤ) : ZMod p`.
  have hp_dvd_q : (p : ℤ) ∣ (d ^ 2 - d) / 4 := by
    have hpoly := polyMod_eq_X_sq_of_p_dvd_d hp2 hd hpd
    have h0 := congr_arg (Polynomial.coeff · 0) hpoly
    simp only [polyMod_coeff_zero, Polynomial.coeff_X_pow] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  -- From `tau_minimal_poly`: `τ² = d • τ - ((d²-d)/4) • 1`.
  have htau : (tau (d := d)) ^ 2 =
      d • tau - ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) := by
    have h := tau_minimal_poly (d := d)
    linear_combination h
  rw [htau]
  -- Show each summand is in the ideal.
  apply Ideal.sub_mem
  · -- `d • τ ∈ (p)`: rewrite `d = p * k`, then `d • τ = (p : QO d) * (k • τ)`.
    obtain ⟨k, hk⟩ := hpd
    have hstep : (d : ℤ) • (tau (d := d)) =
        (p : QuadraticOrder d) * (k • tau) := by
      rw [hk, zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [hstep]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · -- `((d²-d)/4) • 1 ∈ (p)`: same idea with the divisibility `p ∣ (d²-d)/4`.
    obtain ⟨m, hm⟩ := hp_dvd_q
    have hstep : ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) =
        (p : QuadraticOrder d) * (m • (1 : QuadraticOrder d)) := by
      rw [hm, zsmul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [hstep]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- `τ` is not in the ideal `(p)` of `QuadraticOrder d` for any prime `p`.
This holds because `τ` is the second `ℤ`-basis element of `QuadraticOrder d`
(the first being `1`), so its `τ`-coordinate is `1`, which is not a multiple
of `p ≥ 2`.

Together with `tau_sq_mem_span_p_of_p_dvd_d`, this shows that when `p ∣ d`,
the image of `τ` in `QuadraticOrder d / (p)` is a nonzero element with
`τ² = 0` — a genuine order-2 nilpotent witnessing ramification. -/
theorem tau_not_mem_span_p [Fact p.Prime] :
    tau (d := d) ∉ Ideal.span {(p : QuadraticOrder d)} := by
  intro hmem
  -- Unfold span membership: get `α` with `α * (p : QO d) = τ`.
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hmem
  -- Rewrite as `(p : ℕ) • α = τ` via commutativity + `nsmul_eq_mul`.
  have hsmul : (p : ℕ) • α = tau (d := d) := by
    rw [nsmul_eq_mul, ← mul_comm α, hα]
  -- The basis dimension is 2 (degree of `poly d`).
  have hdim : (basis (d := d)).dim = 2 := by
    change (poly d).natDegree = 2
    unfold poly
    compute_degree!
  -- Index `1 : Fin basis.dim` (requires `1 < 2`).
  let i1 : Fin (basis (d := d)).dim := ⟨1, by rw [hdim]; decide⟩
  -- Compute `repr τ` at index `1`. Use `powerBasisAux'_repr_apply_to_fun`:
  -- `(basis.basis.repr τ) 1 = (modByMonicHom (poly_monic d) τ).coeff 1`.
  -- Since `τ = mk (poly d) X` and `X %ₘ poly d = X` (degree 1 < 2), this is `1`.
  have hrepr_tau : ((basis (d := d)).basis.repr (tau (d := d))) i1 = 1 := by
    change ((AdjoinRoot.powerBasisAux' (poly_monic d)).repr (tau (d := d))) i1 = 1
    rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    -- Goal: `((modByMonicHom (poly_monic d)) τ).coeff ↑i1 = 1`
    have htau_eq : (tau (d := d)) = AdjoinRoot.mk (poly d) Polynomial.X := by
      unfold tau; rw [AdjoinRoot.mk_X]
    rw [htau_eq, AdjoinRoot.modByMonicHom_mk]
    -- Goal: `(Polynomial.X %ₘ poly d).coeff ↑i1 = 1`
    have hX_mod : Polynomial.X %ₘ poly d = (Polynomial.X : ℤ[X]) := by
      rw [Polynomial.modByMonic_eq_self_iff (poly_monic d)]
      -- degree X = 1 < 2 = degree (poly d)
      have hpoly_nd : (poly d).natDegree = 2 := by
        unfold poly
        compute_degree!
      have hpoly_deg : (poly d).degree = 2 := by
        rw [Polynomial.degree_eq_natDegree (poly_monic d).ne_zero, hpoly_nd]
        rfl
      rw [hpoly_deg, Polynomial.degree_X]
      decide
    rw [hX_mod]
    change (Polynomial.X : ℤ[X]).coeff 1 = 1
    exact Polynomial.coeff_X_one
  -- Now apply `repr` to `hsmul : (p : ℕ) • α = τ` and project at index `i1`.
  have hlhs : ((basis (d := d)).basis.repr ((p : ℕ) • α)) i1 = 1 := by
    rw [hsmul]; exact hrepr_tau
  -- Linearity: `repr` is a `LinearEquiv ℤ`, so it preserves nsmul. After
  -- pushing the smul through the LinearEquiv and the Finsupp evaluation,
  -- and converting nsmul on ℤ to natCast multiplication, we get
  -- `(p : ℤ) * ((basis.basis.repr α) i1) = 1`.
  rw [map_nsmul, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at hlhs
  -- `hlhs : (p : ℤ) * ((basis.basis.repr α) i1) = 1`.
  have hdvd : (p : ℤ) ∣ 1 := ⟨_, hlhs.symm⟩
  have hp_ge_two : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp_int_ge_two : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp_ge_two
  have hp_pos : (0 : ℤ) < (p : ℤ) := by linarith
  have hple : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
  linarith

end QuadraticOrder
