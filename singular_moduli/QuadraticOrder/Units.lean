import QuadraticOrder.Norm
import QuadraticOrder.Defs.Setup

/-!
# Units of imaginary quadratic orders

**Thesis.** §1.2 (`w_i = #O_{d_i}^×`) and §2.1 — the unit counts
`w ∈ {2, 4, 6}` (with `w = 4` iff `d = −4`, `w = 6` iff `d = −3`) normalize
every `J(d₁,d₂)` exponent in Chapter 2.

**Human-readable companion.** `proofs/infra-units.md`.

**This file states/proves:**

* `units_eq_one_or_neg_one` — `O_d^× = {±1}` for `d < −4`
* `card_units_eq_two` — `#O_d^× = 2` for `d < −4`

**Proof strategy.** The norm form is positive definite for `d < 0`
(completed square — see `proofs/infra-units.md` for the exact identity), a
unit has norm-form value `1`, and for `d < −4` the only lattice points of
norm `1` are `±1`.  Mathlib's torsion-unit theory (`NumberField.Units`)
applies only to maximal orders and is not used.

**Status.** WP-A proved. Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d : ℤ}

/-! ### Coordinates and the norm of a unit

These private lemmas implement the preliminaries and Lemmas 1–2 of the
human-readable proof.  Keeping them here makes the two public declarations
read as the short lattice-point argument appearing in that proof. -/

private lemma exists_coords (x : QuadraticOrder d) :
    ∃ a b : ℤ, x = a • (1 : QuadraticOrder d) + b • tau := by
  -- The power basis says that every element is represented by a polynomial
  -- of degree below two.
  obtain ⟨f, hf, rfl⟩ := (basis (d := d)).exists_eq_aeval x
  have hf' : f.natDegree ≤ 1 := by
    rw [basis_dim] at hf
    omega
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf']
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

private lemma coords_eq {a b c e : ℤ}
    (h : a • (1 : QuadraticOrder d) + b • tau = c • 1 + e • tau) :
    a = c ∧ b = e := by
  -- Rewrite both sides in the actual power basis before applying its
  -- coordinate map.  The coefficients at indices zero and one are unique.
  have h' :
      a • (basis (d := d)).basis ⟨0, by simp⟩ +
          b • (basis (d := d)).basis ⟨1, by simp⟩ =
        c • (basis (d := d)).basis ⟨0, by simp⟩ +
          e • (basis (d := d)).basis ⟨1, by simp⟩ := by
    simpa [PowerBasis.coe_basis] using h
  constructor
  · have hzero := congrArg
      (fun x => ((basis (d := d)).basis.repr x) ⟨0, by simp⟩) h'
    simp only [map_add, LinearEquiv.map_smul] at hzero
    rw [(basis (d := d)).basis.repr_self,
      (basis (d := d)).basis.repr_self] at hzero
    simpa using hzero
  · have hone := congrArg
      (fun x => ((basis (d := d)).basis.repr x) ⟨1, by simp⟩) h'
    simp only [map_add, LinearEquiv.map_smul] at hone
    rw [(basis (d := d)).basis.repr_self,
      (basis (d := d)).basis.repr_self] at hone
    simpa using hone

private lemma mul_coords (a b c e : ℤ) :
    (a • (1 : QuadraticOrder d) + b • tau) *
        (c • 1 + e • tau) =
      (a * c - ((d ^ 2 - d) / 4) * (b * e)) • 1 +
        (a * e + b * c + d * b * e) • tau := by
  -- Reduce the product with the defining relation
  -- `tau² - d*tau + (d²-d)/4 = 0`.
  have htau := tau_minimal_poly (d := d)
  simp only [zsmul_eq_mul] at htau ⊢
  push_cast at htau ⊢
  linear_combination ((b : QuadraticOrder d) * e) * htau

private lemma four_mul_normForm
    (hdisc : d % 4 = 0 ∨ d % 4 = 1) (a b : ℤ) :
    4 * normForm d a b = (2 * a + d * b) ^ 2 - d * b ^ 2 := by
  -- The discriminant congruence is used exactly here, to replace integer
  -- division by the equality `4 * ((d²-d)/4) = d²-d`.
  have hq := Int.ediv_mul_cancel (dvd_four_of_valid_disc hdisc)
  simp only [normForm]
  nlinarith

private lemma normForm_nonneg (hd : d < 0)
    (hdisc : d % 4 = 0 ∨ d % 4 = 1) (a b : ℤ) :
    0 ≤ normForm d a b := by
  -- Companion proof, Lemma 1: both terms in the completed square are
  -- nonnegative because `-d > 0`.
  have hfour := four_mul_normForm hdisc a b
  have hdneg : 0 ≤ -d := by omega
  have hprod : 0 ≤ (-d) * b ^ 2 := mul_nonneg hdneg (sq_nonneg b)
  nlinarith [sq_nonneg (2 * a + d * b)]

private lemma normForm_eq_one_of_unit (hd : d < 0)
    (hdisc : d % 4 = 0 ∨ d % 4 = 1)
    (u : (QuadraticOrder d)ˣ) (a b : ℤ)
    (hu : (u : QuadraticOrder d) = a • 1 + b • tau) :
    normForm d a b = 1 := by
  -- Companion proof, Lemma 2: write the inverse in the same basis.
  obtain ⟨c, e, hinv⟩ := exists_coords (d := d) (↑u⁻¹)
  have hcoords :
      (a * c - ((d ^ 2 - d) / 4) * (b * e)) •
          (1 : QuadraticOrder d) +
          (a * e + b * c + d * b * e) • tau =
        (1 : ℤ) • 1 + (0 : ℤ) • tau := by
    calc
      _ = (a • (1 : QuadraticOrder d) + b • tau) *
          (c • 1 + e • tau) := (mul_coords a b c e).symm
      _ = (u : QuadraticOrder d) * (↑u⁻¹ : QuadraticOrder d) := by
        rw [hu, hinv]
      _ = 1 := Units.mul_inv u
      _ = (1 : ℤ) • 1 + (0 : ℤ) • tau := by simp
  obtain ⟨hconst, htau⟩ := coords_eq hcoords
  -- Coordinate uniqueness turns `u * u⁻¹ = 1` into the input needed for
  -- the already-proved multiplicativity formula.
  have hmul := normForm_mul (d := d) a b c e
  rw [hconst, htau] at hmul
  have hprod : normForm d a b * normForm d c e = 1 := by
    simpa [normForm] using hmul.symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with hone | hneg
  · exact hone
  · have := normForm_nonneg hd hdisc a b
    omega

/-- For `d < −4` (and `d` a genuine discriminant) the only units of `O_d` are
`±1`.  The excluded discriminants: `d = −4` has `w = 4` (the Gaussian units)
and `d = −3` has `w = 6` (the Eisenstein units). -/
theorem units_eq_one_or_neg_one (hd : d < -4) (hdisc : d % 4 = 0 ∨ d % 4 = 1)
    (u : (QuadraticOrder d)ˣ) : u = 1 ∨ u = -1 := by
  -- Companion proof, part 1: choose the unique coordinates of the unit.
  obtain ⟨a, b, hu⟩ := exists_coords (d := d) (u : QuadraticOrder d)
  have hnorm := normForm_eq_one_of_unit (by omega) hdisc u a b hu
  have hfour := four_mul_normForm hdisc a b
  rw [hnorm] at hfour
  -- If `b ≠ 0`, then `(-d)b² ≥ 5`, already larger than the total four.
  have hb : b = 0 := by
    by_contra hb
    have hb2 : 1 ≤ b ^ 2 := by nlinarith [sq_pos_of_ne_zero hb]
    have hd5 : 5 ≤ -d := by omega
    have hd0 : 0 ≤ -d := by omega
    have hprod : 5 ≤ (-d) * b ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb2 hd0]
    nlinarith [sq_nonneg (2 * a + d * b)]
  -- With `b = 0`, norm one says `a² = 1`; lift the two possibilities
  -- back from ring elements to units.
  have ha2 : a ^ 2 = 1 := by simpa [normForm, hb] using hnorm
  rcases (sq_eq_one_iff.mp ha2) with ha | ha
  · left
    apply Units.ext
    rw [hu, hb, ha]
    simp
  · right
    apply Units.ext
    rw [hu, hb, ha]
    simp

/-- For `d < −4`: `#O_d^× = 2`. -/
theorem card_units_eq_two (hd : d < -4) (hdisc : d % 4 = 0 ∨ d % 4 = 1) :
    Nat.card (QuadraticOrder d)ˣ = 2 := by
  -- Exhibit the two units and use the classification above for exhaustivity.
  rw [Nat.card_eq_two_iff]
  refine ⟨1, -1, ?_, ?_⟩
  · intro h
    have hcoe := congrArg (fun v : (QuadraticOrder d)ˣ =>
      (v : QuadraticOrder d)) h
    have hcoords := coords_eq (d := d) (a := 1) (b := 0)
      (c := -1) (e := 0) (by simpa using hcoe)
    omega
  · apply Set.eq_univ_of_forall
    intro u
    simpa using units_eq_one_or_neg_one hd hdisc u

end QuadraticOrder
