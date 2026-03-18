import Mathlib.RingTheory.AdjoinRoot

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
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d * Polynomial.X +
              Polynomial.C ((d ^ 2 - d) / 4))

namespace QuadraticOrder

variable {d : ℤ}

/-- The element `τ` corresponding to `(d + √d)/2` in the order. -/
noncomputable def tau : QuadraticOrder d :=
  AdjoinRoot.root _

end QuadraticOrder
