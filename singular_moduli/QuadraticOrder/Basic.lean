import Mathlib.RingTheory.AdjoinRoot

/--
`QuadraticOrder d` represents the imaginary quadratic order of discriminant `d`.
For `d` such that `d ≡ 0, 1 (mod 4)`, this is realized concretely as
`ℤ[x] / (x^2 - dx + (d^2 - d)/4)`.
-/
abbrev QuadraticOrder (d : ℤ) : Type :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X +
              Polynomial.C ((d ^ 2 - d) / 4))

namespace QuadraticOrder

variable {d : ℤ}

/-- The element `τ` corresponding to `(d + √d)/2` in the order. -/
noncomputable def tau : QuadraticOrder d :=
  AdjoinRoot.root _

end QuadraticOrder
