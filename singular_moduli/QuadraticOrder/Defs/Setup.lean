import QuadraticOrder.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Standing setup for the counting theorems (statement freeze)

**Thesis.** §1.2 (Notation) and the §3.2 standing hypotheses: `d = D·f²` with `D`
a fundamental discriminant, `f` the conductor, `p` a rational prime dividing `f`,
`w = v_p(f)`.

**Human-readable companion.** `proofs/notation.md` — read it first; every
definition here has a prose twin there, and the blueprint chapter
`blueprint/src/results/notation.tex` is generated from the same source.

**This file defines** (definitions only — no theorems, no proofs):

* `IsDiscriminant d` — `d < 0` and `d ≡ 0, 1 (mod 4)`
* `IsFundamentalDiscriminant D` — `D` is a fundamental discriminant
* `ConductorPrimeSetup d D f p` — the bundled standing hypotheses of §3.2/§3.3,
  used as an instance-implicit `[ConductorPrimeSetup d D f p]` so that every
  counting statement carries ONE bracket instead of six hypotheses
  (the Carleson `ProofData` pattern; see `WORKPLAN.md`, working agreement 1)
* `valD4 d p` — the quantity the thesis writes `v_p(d/4)`, with the convention
  of `ERRATA.md` E6.8 made explicit: `v_p(d)` for odd `p`, `v₂(d) − 2` for `p = 2`
* `epsilonEven m` — the thesis's parity flag `ε` (`1` if `m` is even, else `0`;
  note the REVERSED-parity trap, ERRATA E6: this is `1 - m % 2`, not `m % 2`)
* `kroneckerAtPrime D p` — the splitting symbol making statements `p`-uniform:
  `legendreSym p D` for odd `p`; for `p = 2` it is `1 / −1 / 0` according to
  `D ≡ 1 (mod 8)` / `D ≡ 5 (mod 8)` / `4 ∣ D`.  (Mathlib has no Kronecker
  symbol; this is the two-argument fragment the project needs.)
* `normEval d a` — `g(a) = a² − d·a + (d²−d)/4 = N(τ − a)`, the integer whose
  `p`-adic valuation drives Lemmas 3.2.7/3.2.8

**Divergence from thesis.** The thesis leaves the §3.2 standing hypotheses
implicit in later lemmas (ERRATA E6.2); here they are carried explicitly by
`ConductorPrimeSetup`.  The thesis's `v_p(d/4)` is not literally a valuation of
an integer when `d ≡ 1 (mod 4)`; `valD4` implements the intended meaning.

**Proof strategy.** This file only packages hypotheses and defines notation.
The structure fields are the prose assumptions in `proofs/notation.md`, and
the auxiliary functions are direct case splits implementing the corrected
conventions, so later theorem statements cannot silently omit them.

**Status.** WP-0 statement freeze. Definitions are final API; changing them
requires a blueprint PR (working agreement 1).
-/

namespace QuadraticOrder

/-- `d` is the discriminant of an imaginary quadratic order:
`d < 0` and `d ≡ 0, 1 (mod 4)`. -/
def IsDiscriminant (d : ℤ) : Prop :=
  d < 0 ∧ (d % 4 = 0 ∨ d % 4 = 1)

/-- `D` is a fundamental discriminant: either `D ≡ 1 (mod 4)` and `D` is
squarefree, or `D = 4m` with `m ≡ 2, 3 (mod 4)` squarefree.

Sign-agnostic (positive fundamental discriminants satisfy it too); the
project's theorems add negativity where they need it. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨
    (D % 4 = 0 ∧ Squarefree (D / 4) ∧ (D / 4 % 4 = 2 ∨ D / 4 % 4 = 3))

/-- Standing setup for the §3.2/§3.3 counting theorems: an imaginary quadratic
discriminant `d = D·f²` (`D` fundamental, `f = cond(d)` the conductor) together
with a rational prime `p ∣ f`.

Every statement about counting ideals of norm `p^m` in `O_d` takes this as an
instance-implicit `[ConductorPrimeSetup d D f p]`.  The thesis's `w` is
`padicValNat p f`; use it inline (there is deliberately no `w` field, so that
statements stay self-contained). -/
class ConductorPrimeSetup (d D : ℤ) (f p : ℕ) : Prop where
  /-- The discriminant is negative (imaginary quadratic). -/
  d_neg : d < 0
  /-- `d = D·f²` — the fundamental-discriminant/conductor decomposition. -/
  d_eq : d = D * (f : ℤ) ^ 2
  /-- `D` is fundamental. -/
  D_fund : IsFundamentalDiscriminant D
  /-- The conductor is positive. -/
  f_pos : 0 < f
  /-- `p` is prime. -/
  p_prime : p.Prime
  /-- `p` divides the conductor — the standing hypothesis of all of §3.2/§3.3. -/
  p_dvd_f : p ∣ f

/-- The quantity the thesis writes `v_p(d/4)` (ERRATA E6.8): `v_p(d)` for odd
`p`, and `v₂(d) − 2` for `p = 2` (where `2 ∣ f` forces `16 ∣ d`, so the
subtraction is exact in the intended regime). -/
def valD4 (d : ℤ) (p : ℕ) : ℕ :=
  if p = 2 then padicValInt 2 d - 2 else padicValInt p d

/-- The thesis's parity flag `ε`: `1` if `m` is even, `0` if `m` is odd.
Beware: this is the REVERSE of the usual parity indicator (ERRATA E6). -/
def epsilonEven (m : ℕ) : ℕ :=
  if Even m then 1 else 0

/-- The splitting symbol of the fundamental discriminant `D` at `p`, making the
counting statements `p`-uniform (ERRATA E4): for odd `p` this is the Legendre
symbol `(D/p)`; for `p = 2` it is `1` if `D ≡ 1 (mod 8)` (split), `−1` if
`D ≡ 5 (mod 8)` (inert), and `0` if `4 ∣ D` (ramified).

This is the `(D/·)` fragment of the Kronecker symbol, which Mathlib lacks;
`WP-I` vendors the full Kronecker symbol, and proving agreement with this
definition is part of that package. -/
noncomputable def kroneckerAtPrime (D : ℤ) (p : ℕ) [Fact p.Prime] : ℤ :=
  if p = 2 then (if D % 8 = 1 then 1 else if D % 8 = 5 then -1 else 0)
  else legendreSym p D

/-- `normEval d a = g(a) = a² − d·a + (d²−d)/4 = N(τ − a)` — the defining
polynomial of `O_d` evaluated at an integer.  Its `p`-adic valuation is the
`ν` of Lemmas 3.2.7/3.2.8. -/
def normEval (d a : ℤ) : ℤ :=
  a ^ 2 - d * a + (d ^ 2 - d) / 4

end QuadraticOrder
