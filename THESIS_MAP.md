# Thesis ↔ Lean map & commenting convention

This is the durable index tying the Lean formalization in `singular_moduli/`
to **`thesis.pdf`** (*Singular Moduli and the Ideal Class Group*, C. Geiger,
2020). Read this alongside the PDF to navigate the code.

For the forward-looking roadmap (what to build next, in what order), see
`NEXT_STEPS.md`. This file is the *reference*: where each thesis statement
lives, and the conventions every source file follows.

---

## File-header convention

Every Lean source file under `QuadraticOrder/` opens with a module docstring
(`/-! … -/`) containing, in order:

1. **`# Title`** — the file's single subject.
2. **`**Thesis.**`** — the exact section + numbered statement it formalizes
   (e.g. "§3.2, Proposition 3.2.1"), with a one-line restatement.
3. **`**This file proves:**`** — a bullet list of the public declarations.
4. **`**Divergence from thesis.**`** — *only when the Lean proof differs from
   the thesis argument.* States what was done instead and why. Omit this
   section entirely when the proof follows the thesis.

One thesis *result* per file (the lemma/proposition + its private helpers).
Definitions and their immediate structural lemmas may share a file.

## Where divergences are flagged

Major reformulations that are **not** in the thesis, called out at their site:

| Lean | Divergence |
|------|-----------|
| `QuadraticOrder/Basic.lean` | `O_d` defined for **all** `d`, not just discriminants; congruence hypothesis introduced only where needed. |
| `QuadraticOrder/Norm.lean` | Norm form *derived* via the conjugate `τ̄` + Vieta, shown multiplicative as `α ↦ α·ᾱ`, rather than stated as a form. |
| `QuadraticOrder/Discriminant.lean` | General identity `(τ−τ̄)² = (d²−4⌊(d²−d)/4⌋)` (Lean-only artifact) collapsing to `d` under `d ≡ 0,1 mod 4`. |
| `QuadraticOrder/Prime/QuotientIso.lean` | **Central reorganisation.** The whole split/inert/ramified trichotomy is transported across one ring iso `O/(p) ≅ 𝔽ₚ[X]/(g)`, replacing the thesis's `ℤ/pᵏ[x]/g(x)` index computations. |

---

## Statement-by-statement map

Legend: ✅ done · ⚠️ partial · ⛔ stub/not started

### Foundations (thesis §1.2, §3.2 preliminaries)

| Thesis | Lean | File | Status |
|--------|------|------|:--:|
| Order `O_d = ℤ[(d+√d)/2]` | `QuadraticOrder d`, `poly`, `tau`, `basis` | `Basic.lean` | ✅ |
| `τ` minimal polynomial | `tau_minimal_poly`, `poly_aeval_tau` | `Basic.lean` | ✅ |
| Norm form `N(a+bτ)` | `normForm`, `normForm_mul`, `normForm_eq_mul_conj` | `Norm.lean` | ✅ |
| Conjugate, Vieta `τ+τ̄=d`, `ττ̄=(d²−d)/4` | `tauConj`, `tau_add_tauConj`, `tau_mul_tauConj` | `Norm.lean` | ✅ |
| `(τ−τ̄)² = d` (for `d ≡ 0,1 mod 4`) | `tau_sub_tauConj_sq_of_valid_disc` | `Discriminant.lean` | ✅ |

### Prime classification (thesis §3.2, Prop 3.2.1, Remark 3.2.3)

| Thesis | Lean | File | Status |
|--------|------|------|:--:|
| Reduced poly `g = polyMod d p`, root ↔ `(d/p)` | `polyMod*`, `polyMod_*_legendreSym_*` | `Prime/PolyMod.lean` | ✅ |
| `O/(p) ≅ 𝔽ₚ[X]/(g)` (proof device) | `quadraticOrderModP_equiv_polyModQuot` | `Prime/QuotientIso.lean` | ✅ |
| Prime **inert** iff `(d/p) = -1` | `prime_inert_iff` | `Prime/Inert.lean` | ✅ |
| Prime **ramified** iff `p ∣ d` | `prime_ramified_iff` | `Prime/Ramified.lean` | ✅ |
| Prime **split** iff `(d/p) = 1` | `prime_split_iff` | `Prime/Split.lean` | ⛔ PR #33 |

### Root counting (thesis §3.2, Lemma 3.2.6)

| Thesis | Lean | File | Status |
|--------|------|------|:--:|
| `#√` of `x² ≡ c (mod pⁿ)`, **odd `p`** | `cardSqrts_prime_pow_even_val` etc. | `RootCounting.lean` | ✅ |
| same, **`p = 2`** | — | `RootCounting.lean` | ⛔ |

### Ideal counting (thesis §3.1, §3.3)

| Thesis | Lean | File | Status |
|--------|------|------|:--:|
| Lemma 3.2.4 (canonical form — keystone) | `canonicalIdeal`, `CanonicalAdmissible`, … | `CanonicalForm.lean` | ⛔ |
| Lemma 3.2.2 / 3.2.7 / 3.2.8 (localisation) | — | `Localization.lean` | ⛔ |
| Proposition 3.1.1 (count in `O_K`, maximal) | — | `MaximalCase.lean` | ⛔ |
| Theorem 3.1.2 (count in `O_d`) | — | `IdealCount.lean` | ⛔ |
| Corollary 3.1.3 (invertible-ideal count) | — | `InvertibleCount.lean` | ⛔ |

---

## Remaining reorg work (after the Basic + Prime pass)

The one-result-per-file split has been applied to the two finished, oversized
files' source (`Basic` → `Basic`/`Norm`/`Discriminant`; `Prime` →
`Prime/{PolyMod,QuotientIso,Inert,Ramified}`). Still to do:

- **`RootCounting.lean` (838 lines)** → split into `RootCounting/`:
  `Defs`, `OddPrimeCoprime` (the ~320-line Hensel lift), `OddPrimeEvenVal`,
  `ZeroCase`, `TwoPower`. Add interior comments to the Hensel-lift proof
  (currently very dense). Plus fill the **`p = 2` gap** (Lemma 3.2.6).
- **Stub files** (`CanonicalForm`, `Localization`, `IdealCount`,
  `InvertibleCount`, `MaximalCase`): already carry headers; will follow the
  convention as they are implemented.
- **`Thermodynamics.lean`**: unrelated to the thesis — should be removed (and
  its `lean_lib` entry dropped from `lakefile.toml`), or moved to a separate
  scratch repo.
- **`README.md`**: currently generic boilerplate; rewrite to describe the
  thesis, the layer structure, and point here.
