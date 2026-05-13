import Mathlib.RingTheory.AdjoinRoot

open scoped Polynomial

/-- The defining polynomial of `QuadraticOrder d`. -/
noncomputable def poly (d : ℤ) : ℤ[X] :=
  Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X + Polynomial.C ((d ^ 2 - d) / 4)

/--
`QuadraticOrder d` is the quadratic `ℤ`-algebra
`ℤ[x] / (x^2 - d * x + (d^2 - d) / 4)`, where the constant term is formed
using Euclidean division in `ℤ`.

For integers `d` with `d ≡ 0, 1 (mod 4)`, this ring coincides with the
(imaginary) quadratic order of discriminant `d` in the quadratic field
`ℚ(√d)`. When `d` does not satisfy these congruence conditions, this
definition should simply be understood as this explicit quadratic
quotient ring over `ℤ`.
-/
abbrev QuadraticOrder (d : ℤ) : Type :=
  AdjoinRoot (poly d)

namespace QuadraticOrder

/-! ### Defining polynomial

We define `poly` before the `variable` command so the auto-binder does not
add a second implicit `d` to its signature. -/

/-- The defining polynomial is monic of degree 2. -/
lemma poly_monic (d : ℤ) : (poly d).Monic := by
  have heq : poly d =
      Polynomial.X ^ 2 -
      (Polynomial.C d * Polynomial.X - Polynomial.C ((d ^ 2 - d) / 4)) := by
    unfold poly; ring
  rw [heq]
  apply Polynomial.monic_X_pow_sub
  apply (Polynomial.degree_sub_le _ _).trans_lt
  apply max_lt
  · exact (Polynomial.degree_C_mul_X_le d).trans_lt (by norm_cast)
  · exact Polynomial.degree_C_le.trans_lt (by norm_cast)

variable {d : ℤ}

/-- The element `τ` corresponding to `(d + √d)/2` in the order. -/
noncomputable def tau : QuadraticOrder d :=
  AdjoinRoot.root _

/-! ### Layer 1: Basic algebraic properties -/


/-- `τ` is a root of the defining polynomial `X² - dX + (d²-d)/4`.

Proof sketch: `aeval τ (poly d) = mk (poly d) (poly d) = 0` by
`AdjoinRoot.aeval_eq` and `AdjoinRoot.mk_self`. -/
lemma tau_minimal_poly :
    tau ^ 2 - d • tau + ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 := by
  have h : Polynomial.aeval (tau (d := d)) (poly d) = 0 := by
    unfold tau
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  simp only [poly, map_sub, map_add, map_mul, map_pow,
             Polynomial.aeval_X, Polynomial.aeval_C,
             Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  exact h

/-- `QuadraticOrder d` has a `ℤ`-module power basis `{1, τ}` of rank 2. -/
noncomputable def basis : PowerBasis ℤ (QuadraticOrder d) :=
  AdjoinRoot.powerBasis' (poly_monic d)

/-- `QuadraticOrder d` is a free `ℤ`-module (of rank 2). -/
instance : Module.Free ℤ (QuadraticOrder d) :=
  (poly_monic d).free_adjoinRoot

/-- `QuadraticOrder d` is a finite `ℤ`-module. -/
instance : Module.Finite ℤ (QuadraticOrder d) :=
  (poly_monic d).finite_adjoinRoot

/-! ### Norm form -/

/-- The norm form on `QuadraticOrder d`: the norm of `a + b·τ` is
`a² + d·a·b + ((d²-d)/4)·b²`.

Derivation: N(a + bτ) = (a + bτ)(a + b(d - τ)), using the fact that
`τ` and `d - τ` are the two roots of `X² - dX + (d²-d)/4`.
Expanding: a² + ab(d - τ) + abτ + b²τ(d - τ) = a² + abd + b²·τ(d-τ).
Since τ² - dτ + (d²-d)/4 = 0, we have τ(d - τ) = (d²-d)/4, giving the formula. -/
noncomputable def normForm (d a b : ℤ) : ℤ :=
  a ^ 2 + d * a * b + ((d ^ 2 - d) / 4) * b ^ 2

/-- The norm form is multiplicative: N(αβ) = N(α)·N(β).

This follows from the ring-identity that holds for any integers a, b, c, e, d,
and any integer q substituted for (d²-d)/4. -/
theorem normForm_mul (a b c e : ℤ) :
    normForm d (a * c - ((d ^ 2 - d) / 4) * (b * e)) (a * e + b * c + d * b * e) =
    normForm d a b * normForm d c e := by
  simp only [normForm]
  set q := (d ^ 2 - d) / 4
  ring

/-! ### Conjugate and norm involution

The element `tauConj := d • 1 - tau` is the "Galois conjugate" of `tau`: it is
the other root of `poly d`. Together with `tau`, it satisfies the standard
Vieta relations, and exhibits `normForm` as a multiplicative norm via the
factorisation `(a + b·τ)(a + b·τ̄) = N(a, b)`. -/

/-- The Galois conjugate of `tau`: the other root of `poly d`. -/
noncomputable def tauConj : QuadraticOrder d := d • (1 : QuadraticOrder d) - tau

/-- Vieta: the sum of the roots of `poly d` equals `d`. -/
lemma tau_add_tauConj : tau + tauConj = d • (1 : QuadraticOrder d) := by
  unfold tauConj
  ring

/-- Vieta: the product of the roots of `poly d` equals `(d^2 - d) / 4`. -/
lemma tau_mul_tauConj :
    tau * tauConj = ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) := by
  unfold tauConj
  have h := tau_minimal_poly (d := d)
  -- `tau * (d • 1 - tau) = d • tau - tau^2`, and `tau^2 = d • tau - q • 1`.
  linear_combination -h

/-- The conjugate `tauConj` is also a root of the defining polynomial `poly d`. -/
lemma tauConj_minimal_poly :
    tauConj ^ 2 - d • tauConj + ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 := by
  unfold tauConj
  have h := tau_minimal_poly (d := d)
  linear_combination h

/-- `τ` is a root of the defining polynomial `poly d` in `QuadraticOrder d`. -/
@[simp] lemma poly_aeval_tau :
    Polynomial.aeval (tau (d := d)) (poly d) = 0 := by
  unfold tau
  rw [AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

/-- The Galois conjugate `tauConj` is also a root of `poly d`. -/
@[simp] lemma poly_aeval_tauConj :
    Polynomial.aeval (tauConj (d := d)) (poly d) = 0 := by
  have h := tauConj_minimal_poly (d := d)
  simp only [poly, map_sub, map_add, map_mul, map_pow,
             Polynomial.aeval_X, Polynomial.aeval_C,
             Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact h

/-- The norm involution: `(a + b·τ)(a + b·τ̄) = N(a, b)`. This exhibits the
conjugate as the involution under which `normForm` is the multiplicative norm. -/
lemma normForm_eq_mul_conj (a b : ℤ) :
    (a • (1 : QuadraticOrder d) + b • tau)
      * (a • (1 : QuadraticOrder d) + b • tauConj)
    = (normForm d a b) • (1 : QuadraticOrder d) := by
  have hsum : tau + tauConj = d • (1 : QuadraticOrder d) := tau_add_tauConj
  have hprod : tau * tauConj = ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) :=
    tau_mul_tauConj
  simp only [normForm, zsmul_eq_mul] at hsum hprod ⊢
  push_cast
  linear_combination
    ((b : QuadraticOrder d) * (a : QuadraticOrder d)) * hsum
      + ((b : QuadraticOrder d) ^ 2) * hprod

/-! ### Discriminant: `(τ - τ̄)²` -/

/-- The difference of the two roots: `τ - τ̄ = 2 • τ - d • 1`. -/
lemma tau_sub_tauConj : tau - tauConj = 2 • tau - d • (1 : QuadraticOrder d) := by
  unfold tauConj
  abel

/-- General discriminant identity: `(τ - τ̄)² = (d² - 4·⌊(d²-d)/4⌋) • 1`. The
right-hand-side equals `d • 1` when `d ≡ 0` or `d ≡ 1 (mod 4)` (the values
for which `poly d` has integer coefficients matching the discriminant of the
quadratic field). For general `d`, the difference is the Euclidean remainder
`(d² - d) mod 4`. -/
lemma tau_sub_tauConj_sq :
    (tau - tauConj) ^ 2
      = (d ^ 2 - 4 * ((d ^ 2 - d) / 4) : ℤ) • (1 : QuadraticOrder d) := by
  have h := tau_minimal_poly (d := d)
  rw [tau_sub_tauConj]
  -- (2 • τ - d • 1)^2 = 4 • τ² - 4d • τ + d² • 1
  -- substitute τ² = d • τ - q • 1, giving d² • 1 - 4q • 1 = (d² - 4q) • 1
  linear_combination (4 : QuadraticOrder d) * h

/-- Under the valid-discriminant hypothesis `d ≡ 0 ∨ d ≡ 1 (mod 4)`, the
discriminant equals `d` exactly: `(τ - τ̄)² = d • 1`. This is the case used
throughout the thesis (the only `d` for which `QuadraticOrder d` coincides
with the quadratic order of discriminant `d`). -/
lemma tau_sub_tauConj_sq_of_valid_disc
    (hd : d % 4 = 0 ∨ d % 4 = 1) :
    (tau - tauConj) ^ 2 = d • (1 : QuadraticOrder d) := by
  rw [tau_sub_tauConj_sq]
  congr 1
  -- reduce to: d^2 - 4 * ((d^2 - d) / 4) = d
  -- equivalently: 4 ∣ (d^2 - d), so 4 * ((d^2-d)/4) = d^2 - d
  have h4dvd : (4 : ℤ) ∣ d ^ 2 - d := by
    have hdd : d ^ 2 - d = d * (d - 1) := by ring
    rw [hdd]
    rcases hd with h | h
    · exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
    · have h1 : (4 : ℤ) ∣ (d - 1) := by
        have : (d - 1) % 4 = 0 := by omega
        exact Int.dvd_of_emod_eq_zero this
      exact Dvd.dvd.mul_left h1 _
  have hcancel : (4 : ℤ) * ((d ^ 2 - d) / 4) = d ^ 2 - d :=
    Int.mul_ediv_cancel' h4dvd
  linarith

end QuadraticOrder
