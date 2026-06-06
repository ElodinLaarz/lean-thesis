# Next Steps

A roadmap for the remaining layers of the formalization, with thesis
cross-references and concrete implementation guidance.

## Current state (as of PR #35)

`main` is `sorry`-free. The following layers are complete:

| File | Thesis content | Status |
|------|---------------|--------|
| `Basic.lean` | Order definition, `τ`, conjugate, norm form, discriminant identity, basis helpers | ✅ |
| `Prime.lean` | `polyMod`, split/inert/ramified trichotomy (Prop 3.2.1, Remark 3.2.3) | ✅ |
| `RootCounting.lean` | Lemma 3.2.6 for odd primes; `ZMod 2,4,8` base cases | ✅ partial |

Five stub files remain:

| File | Thesis | Depends on |
|------|--------|-----------|
| `CanonicalForm.lean` (2b) | Lemma 3.2.4 | `Basic`, `Prime` |
| `Localization.lean` (2c) | Lemma 3.2.2, Lemma 3.2.7, Lemma 3.2.8 | `Basic` |
| `IdealCount.lean` (4a) | Theorem 3.1.2 | `CanonicalForm`, `RootCounting` |
| `InvertibleCount.lean` (4b) | Corollary 3.1.3 | `IdealCount`, `Localization` |
| `MaximalCase.lean` (5a) | Proposition 3.1.1 | `InvertibleCount` |

Open gap on already-merged files:

- `RootCounting.lean` is missing the **p = 2 case of Lemma 3.2.6**
  (`cardSqrts_two_pow_coprime` and `cardSqrts_two_pow_even_val`). An
  earlier draft existed on `feat/phase-one-wip` but did not compile
  against current Mathlib and contained `sorry`s; it was discarded and
  needs a fresh attempt.

## Thesis ↔ Lean mapping

| Thesis | Lean | Status |
|--------|------|--------|
| Order `O_d = ℤ[(d+√d)/2]` | `QuadraticOrder d` (`Basic`) | ✅ |
| `τ`, `τ̄`, `τ + τ̄ = d`, `τ τ̄ = (d²-d)/4` | `tau`, `tauConj`, `tau_add_tauConj`, `tau_mul_tauConj` | ✅ |
| `N(a + bτ) = a² + dab + (d²-d)/4 · b²` | `normForm`, `normForm_mul`, `normForm_eq_mul_conj` | ✅ |
| `(τ − τ̄)² = d` (under `d ≡ 0,1 mod 4`) | `tau_sub_tauConj_sq_of_valid_disc` | ✅ |
| Prop 3.2.1 (primes of `O` over `(p)`) | `Prime.polyMod_*` family | ✅ |
| Prime ramified iff `p ∣ d` | `prime_ramified_iff` | ✅ |
| Prime inert iff `(d/p) = -1` | `prime_inert_iff` | ✅ |
| Prime split iff `(d/p) = 1` | `prime_split_iff` | ✅ |
| Lemma 3.2.6 (count √'s mod `p^n`) | `cardSqrts_prime_pow_even_val` (odd `p`) | ✅ partial |
| Lemma 3.2.6 (count √'s mod `2^n`) | not yet | ⛔ |
| Lemma 3.2.4 (canonical form of p-primary ideal) | `CanonicalForm` (stub) | ⛔ |
| Lemma 3.2.2 (localisation containment) | `Localization` (stub) | ⛔ |
| Lemma 3.2.7 (`(p^r(τ-s))O_p ∩ ℤ`) | `Localization` (stub) | ⛔ |
| Lemma 3.2.8 (equality of localisation ideals) | `Localization` (stub) | ⛔ |
| Prop 3.1.1 (ideal count in `O_K`) | `MaximalCase` (stub) | ⛔ |
| Thm 3.1.2 (ideal count in `O_d`) | `IdealCount` (stub) | ⛔ |
| Cor 3.1.3 (invertible-ideal count) | `InvertibleCount` (stub) | ⛔ |

## Next milestone: `CanonicalForm.lean` (Lemma 3.2.4)

The keystone. Once landed, `IdealCount`/`InvertibleCount`/`MaximalCase`
all become reachable.

**Statement.** For `d : ℤ`, a rational prime `p` dividing the conductor,
and a prime ideal `𝔭 ⊆ QuadraticOrder d` over `(p)`: every 𝔭-primary
ideal `a` of additive index `p^m` has the form

```
a = Ideal.span { (p^k : QuadraticOrder d),
                 (p^(m-k) : QuadraticOrder d) * (τ - A • 1) }
```

for a unique `k` with `m/2 ≤ k ≤ m` and a unique `A ∈ ℤ / p^(2k-m)`
with `A² − dA + (d²−d)/4 ≡ 0 (mod p^(2k-m))`. Conversely every such
`(k, A)` gives a 𝔭-primary ideal of index `p^m`.

### Definitions

```lean
noncomputable def canonicalIdeal (d : ℤ) (p k m : ℕ) (A : ℤ) :
    Ideal (QuadraticOrder d) :=
  Ideal.span {(p ^ k : QuadraticOrder d),
              (p ^ (m - k) : QuadraticOrder d) * (tau - (A : QuadraticOrder d))}

def CanonicalAdmissible (d : ℤ) (p k m : ℕ) (A : ℤ) : Prop :=
  (p : ℤ) ^ (2 * k - m) ∣ A ^ 2 - d * A + (d ^ 2 - d) / 4
```

### Theorem signatures (planned)

- `canonicalIdeal_index_eq` — `cardQuot (canonicalIdeal …) = p^m`
- `canonicalIdeal_isPrimary_iff` — `IsPrimary ↔ CanonicalAdmissible`
- `exists_canonical_form` — every primary ideal has this form
- `canonical_form_unique` — `k` and `A mod p^(2k-m)` are determined

Use `Submodule.cardQuot` for the index (not `Ideal.absNorm` — that
requires `IsDedekindDomain`, which non-maximal orders fail).

### Suggested PR sequence

1. **Scaffolding + index lemma** (~150 lines). Defines
   `canonicalIdeal` and `CanonicalAdmissible`, builds the analog of
   `quadraticOrderModP_equiv_polyModQuot` for `p^k`, proves
   `canonicalIdeal_index_eq`.
2. **Primarity iff** (~80 lines). Uses
   `Ideal.isPrimary_of_isMaximal_radical` after showing the radical
   equals `(p, τ-A)` and the latter is maximal (quotient ≃ `ZMod p`).
3. **Existence** (~250 lines, the hard one). Helper lemmas
   `exists_intersect_int` (extract `a ∩ ℤ = (p^k)`) and
   `exists_tau_coeff` (extract `p^(m-k) · (τ-A) ∈ a` via the τ-component
   projection — the basis-repr helpers from PR #35 are essential here).
4. **Uniqueness** (~50 lines). `k` is determined by `a ∩ ℤ`; `A mod
   p^(2k-m)` is determined by subtracting the two τ-component
   generators.

Each PR should keep `main` `sorry`-free; intermediate sorries stay on
work branches only.

### Top risks

- **`AdjoinRoot` quotient algebra at `p^k`.** Generalising
  `quadraticOrderModP_equiv_polyModQuot` (which is for `p`) to `p^k`
  may require an inline `Int.quotientSpanEquivZMod` for prime powers.
- **τ-coefficient extraction in the existence proof.** Relies on
  `basis_repr_apply` and `basis_repr_tau_one` from PR #35. Any
  fragility there will show up here.
- **`Ideal.IsPrimary` import.** Not yet imported anywhere in the
  project. Add it explicitly.

## After `CanonicalForm`

- **`Localization.lean` (Lemma 3.2.2 / 3.2.7 / 3.2.8).** Independent of
  `CanonicalForm` mathematically (only `Basic` needed) but consumed by
  `InvertibleCount`. Smaller; can run in parallel.
- **`IdealCount.lean` (Thm 3.1.2).** Direct corollary of
  `CanonicalForm` + `RootCounting` — sum over `m/2 ≤ k ≤ m` of
  `cardSqrts p^(2k-m) (d/4)`. **Blocked** on the `2^n` case of
  Lemma 3.2.6 for the `p = 2` branches.
- **`InvertibleCount.lean` (Cor 3.1.3).** Filters `IdealCount` by
  invertibility using `Localization`.
- **`MaximalCase.lean` (Prop 3.1.1).** Specialisation of `IdealCount`
  when the conductor is trivial. Mostly bookkeeping once `IdealCount`
  lands.

## Conventions in use

- Sorry-free `main`. Intermediate `sorry`s stay on work branches.
- Small focused PRs (current style: #19–35 are all ≤ ~200 lines).
- Commit-message style:
  `feat(<area>): <short summary>` followed by a paragraph on motivation.
- Lint: 100-char line limit enforced; `compute_degree!`, `omega`,
  `linear_combination` favoured over manual reasoning.

## Pointers

- Thesis PDF: `thesis.pdf` (root).
- Detailed mapping: this file's "Thesis ↔ Lean mapping" table.
- Earlier related PRs: #15 (RootCounting odd-prime case), #19–32
  (Prime layer ramified/inert/split development), #34 (`prime_split_iff`),
  #35 (basis-repr helpers).
