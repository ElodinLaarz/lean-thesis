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
    simp only [tau, poly, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
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
`a² + d·a·b - ((d²-d)/4)·b²`.

Derivation: N(a + bτ) = (a + bτ)(a + b(d - τ)), using the fact that
`τ` and `d - τ` are the two roots of `X² - dX + (d²-d)/4`. -/
noncomputable def normForm (d a b : ℤ) : ℤ :=
  a ^ 2 + d * a * b - ((d ^ 2 - d) / 4) * b ^ 2

/-- The norm form is multiplicative.

TODO: provide a proof of this fact (currently assumed as an axiom and
      should be moved to a dedicated TODO file or proved in a later layer). -/
theorem normForm_mul (a b c e : ℤ) :
    normForm d (a * c - ((d ^ 2 - d) / 4) * (b * e)) (a * e + b * c + d * b * e) =
    normForm d a b * normForm d c e

end QuadraticOrder
