# proofs/ — the human-readable proof layer

One Markdown file per result: self-contained statement + complete mathematical proof,
written for a referee who reads no Lean. This directory is the project's **review
surface** — the binding conventions are in [AGENTS.md](../AGENTS.md) §1 and §4
(three-layer rule, doc-first order, structure of each file).

Statements follow the **corrected** forms of [ERRATA.md](../ERRATA.md) where the thesis
is wrong (E1/E2/E4/E5). Each file ends with a Lean correspondence table; the LaTeX twin
of each file lives in `blueprint/src/results/<id>.tex`.

| id | Result | Lean home | Work package |
|----|--------|-----------|--------------|
| `notation` | Notation & standing conventions | `Defs/{Setup,Counting}.lean` | WP-0 (frozen) |
| `prop-3-2-1` | Primes of ℤ[τ] over p; split criterion (Rem 3.2.3) | `Prime/*` | proved / WP-A |
| `lem-3-2-6` | Square-root counts mod p^s (all p, corrected) | `RootCounting*` | odd p proved / WP-B |
| `infra-index` | Index layer: finiteness, CRT multiplicativity, primary bridge | `Index/{Basic,Primary}.lean` | WP-A |
| `infra-units` | Units of imaginary quadratic orders | `Units.lean` | WP-A |
| `lem-3-2-2` | Localization at the unique prime over p | `Localization/Basic.lean` | WP-D |
| `lem-3-2-4` | Normal-form bijection (keystone) | `CanonicalForm{,/Bijection}.lean` | WP-C |
| `lem-3-2-7` | Minimal p-power in a principal local ideal | `Localization/PrincipalMin.lean` | WP-D |
| `lem-3-2-8` | Equality criterion for principal local ideals | `Localization/PrincipalEq.lean` | WP-D |
| `prop-3-1-1` | Ideal counts in the maximal order | `MaximalCase.lean` | WP-E |
| `thm-3-1-2` | **Theorem 3.1.2\*** — all ideals of norm p^m (corrected) | `IdealCount.lean` | WP-F |
| `cor-3-1-3` | **Corollary 3.1.3\*** — invertible ideals (corrected) | `InvertibleCount.lean` | WP-G |
| `infra-invertibility` | Invertible ⇔ locally principal interface | `Index/Invertible.lean` | WP-G |
| `infra-glue` | Counts for arbitrary norm n | `Glue.lean` | WP-H |

Chapter 2 documents (Gross–Zagier, Dorman, Lauter–Viray statements) are added by WP-I
after transcription from `papers/`.
