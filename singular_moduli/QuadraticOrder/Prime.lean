import QuadraticOrder.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

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

end QuadraticOrder
