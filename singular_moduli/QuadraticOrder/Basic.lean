import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

/--
`QuadraticOrder d` represents the imaginary quadratic order of discriminant `d`,
realized concretely as `ℤ[x] / (x^2 - dx + (d^2 - d)/4)`.
-/
def QuadraticOrder (d : ℤ) : Type :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X + Polynomial.C ((d ^ 2 - d) / 4))

namespace QuadraticOrder

variable {d : ℤ}

-- Because AdjoinRoot provides a commutative ring structure, we can derive it.
noncomputable instance : CommRing (QuadraticOrder d) :=
  AdjoinRoot.commRing (Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X + Polynomial.C ((d ^ 2 - d) / 4))

/-- The element `τ` corresponding to `(d + √d)/2` in the order. -/
noncomputable def tau (d : ℤ) : QuadraticOrder d :=
  AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X + Polynomial.C ((d ^ 2 - d) / 4))

-- Note: The basis and norm definitions will follow.

/-- The norm of an ideal in a quadratic order is the index [O : a]. -/
noncomputable def idealNorm (a : Ideal (QuadraticOrder d)) : ℕ :=
  -- This requires O/a to be a Fintype, which we might need to instantiate or assume.
  letI : Fintype (QuadraticOrder d ⧸ a) := sorry
  Fintype.card (QuadraticOrder d ⧸ a)

end QuadraticOrder
