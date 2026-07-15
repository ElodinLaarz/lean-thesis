import Mathlib.Data.Int.GCD

/-!
# Brute-force ideal enumeration (test harness)

**Thesis.** This is not a thesis result.  It independently checks the corrected
Chapter 3 counts in ERRATA E1, E2, and E5.

**Human-readable companion.** `proofs/notation.md` fixes the order and norm
conventions; `proofs/thm-3-1-2.md` and `proofs/cor-3-1-3.md` identify the
regression rows that the enumerator checks.

**This file defines:** a COMPUTABLE, Mathlib-free mirror of the counting quantities,
used only for regression testing (`Harness/Regression.lean`) and `#eval`
experiments.  It lets every closed-form counting theorem be checked against
explicit enumeration — the same check that exposed the thesis's false cases
(ERRATA E1/E2/E5) — before and after its Lean proof exists.

**Trust model.**  Nothing here is part of the proof development: the harness
is validated against the independently computed tables in `ERRATA.md`
(two prior enumeration methods agree with it on every data point), and the
regression file uses `native_decide`, which trusts the Lean compiler.  The
eventual bridge `idealCountBrute = idealCount` is a WP-H deliverable; until
then the harness is an oracle, not a theorem.

**Method.**  An ideal of index `n` in `O_d = ℤ·1 ⊕ ℤ·τ` is a sublattice with
Hermite-normal-form basis `(a, 0), (b, c)` (columns; `a·c = n`, `0 ≤ b < a`)
closed under multiplication by `τ`; since `1, τ` generate `O_d`, closure under
`τ` suffices.  Using `τ² = d·τ − q`, `q = (d²−d)/4`:

* `τ·a   = (0, a)`,
* `τ·(b + cτ) = (−c·q, b + c·d)`,

and membership of `(X, Y)` in the lattice is `c ∣ Y ∧ a ∣ (X − (Y/c)·b)`.

**Invertibility test.** `I` is invertible iff `I·Ī = N(I)·O_d` (the standard
proper-ideal criterion for quadratic orders; see
`proofs/infra-invertibility.md`).  The product lattice is computed from the
four generator products and their `τ`-multiples, reduced to Hermite form by
integer column reduction (`euc`, fuel-bounded Euclid).

All arithmetic uses `Int.ediv`/`Int.emod` (Euclidean convention) so the
divisor-positive cases agree with the mathematical floor convention.

**Proof strategy.** Enumerate the unique Hermite-normal-form representative of
each index-`n` sublattice, test closure under multiplication by `τ`, and test
invertibility by multiplying with the conjugate lattice.  The regression file
compares the resulting finite lists with independently established tables.

**Status.** WP-0 test oracle; no theorem in the formal development depends on
its output.
-/

namespace QuadraticOrder.Harness

/-- `q(d) = (d² − d)/4`, the constant term of the defining polynomial. -/
def qterm (d : ℤ) : ℤ := (d ^ 2 - d) / 4

/-- Membership of the vector `(X, Y)` (representing `X + Y·τ`) in the lattice
with HNF basis `(a, 0), (b, c)`. -/
def memHNF (a b c X Y : ℤ) : Bool :=
  Y.emod c == 0 && (X - Y.ediv c * b).emod a == 0

/-- Is the HNF lattice `(a, 0), (b, c)` an ideal of `O_d` (closed under
multiplication by `τ`)? -/
def isIdealHNF (d a b c : ℤ) : Bool :=
  memHNF a b c 0 a && memHNF a b c (-(c * qterm d)) (b + c * d)

/-- The HNF parameter triples `(a, b, c)` of the ideals of index `n` in `O_d`. -/
def idealsHNF (d : ℤ) (n : ℕ) : List (ℤ × ℤ × ℤ) :=
  ((List.range n).map (· + 1)).filter (fun a => n % a == 0) |>.flatMap fun a =>
    let c : ℕ := n / a
    (List.range a).filterMap fun (b : ℕ) =>
      if isIdealHNF d (a : ℤ) (b : ℤ) (c : ℤ) then some ((a : ℤ), (b : ℤ), (c : ℤ))
      else none

/-- Brute-force count of ideals of index `n` in `O_d` — the computable mirror
of `QuadraticOrder.idealCount`. -/
def idealCountBrute (d : ℤ) (n : ℕ) : ℕ :=
  (idealsHNF d n).length

/-- Multiplication of `x₁ + y₁τ` and `x₂ + y₂τ` in coordinates, via
`τ² = d·τ − q`. -/
def mulVec (d : ℤ) (v w : ℤ × ℤ) : ℤ × ℤ :=
  (v.1 * w.1 - qterm d * v.2 * w.2, v.1 * w.2 + v.2 * w.1 + d * v.2 * w.2)

/-- Fuel-bounded vector Euclid step: reduces the pair `(v, w)` until `w`'s
`τ`-coordinate vanishes; returns the surviving vector and the freed
`1`-coordinate.  Fuel 1000 vastly exceeds any Euclid chain arising from the
regression vectors. -/
def euc : ℕ → ℤ × ℤ → ℤ × ℤ → (ℤ × ℤ) × ℤ
  | 0, v, w => (v, w.1)
  | fuel + 1, v, w =>
    if w.2 == 0 then (v, w.1)
    else euc fuel w (v.1 - v.2.ediv w.2 * w.1, v.2 - v.2.ediv w.2 * w.2)

/-- Hermite normal form `(a, b, c)` of the lattice spanned by a list of
vectors (basis `(a, 0), (b, c)` with `a, c ≥ 0`, `0 ≤ b < a`). -/
def latticeHNF (vs : List (ℤ × ℤ)) : ℤ × ℤ × ℤ :=
  let res := vs.foldl (fun (acc : (ℤ × ℤ) × List ℤ) u =>
    let r := euc 1000 acc.1 u
    (r.1, r.2 :: acc.2)) ((0, 0), [])
  let a : ℕ := res.2.foldl (fun g x => Nat.gcd g x.natAbs) 0
  let c : ℕ := res.1.2.natAbs
  let b : ℤ := if a = 0 then 0 else res.1.1.emod (a : ℤ)
  ((a : ℤ), b, (c : ℤ))

/-- Invertibility of the ideal with HNF parameters `(a, b, c)` in `O_d`:
checks `I·Ī = N(I)·O_d` with `N(I) = a·c` (conjugation:
`x + yτ ↦ (x + yd) − yτ`). -/
def isInvertibleHNF (d a b c : ℤ) : Bool :=
  let n := a * c
  let g1 : ℤ × ℤ := (a, 0)
  let g2 : ℤ × ℤ := (b, c)
  let c1 : ℤ × ℤ := (a, 0)
  let c2 : ℤ × ℤ := (b + c * d, -c)
  let prods := [mulVec d g1 c1, mulVec d g1 c2, mulVec d g2 c1, mulVec d g2 c2]
  let withTau := prods ++ prods.map (fun v => (-(qterm d) * v.2, v.1 + d * v.2))
  let h := latticeHNF withTau
  h.1 == n && h.2.2 == n && h.2.1.emod n == 0

/-- Brute-force count of INVERTIBLE ideals of index `n` — the computable
mirror of `QuadraticOrder.invertibleIdealCount`. -/
def invertibleIdealCountBrute (d : ℤ) (n : ℕ) : ℕ :=
  ((idealsHNF d n).filter (fun t => isInvertibleHNF d t.1 t.2.1 t.2.2)).length

end QuadraticOrder.Harness
