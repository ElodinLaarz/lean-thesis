# AGENTS.md — how work is written up in this repository

Binding requirements for every contributor (human or agent). The purpose of this project
is not just a green build: **a mathematician must be able to independently verify the
arguments without reading Lean**. Every requirement below serves that goal.

## 1. The three-layer rule

Every mathematical result in this project exists in exactly three synchronized forms:

1. **A Markdown proof document** — `proofs/<id>.md`. Self-contained statement AND full
   mathematical proof (LaTeX math in `$...$`), written for a human referee. This is the
   review surface: someone checking our logic reads this file, not the Lean.
2. **A LaTeX blueprint fragment** — `blueprint/src/results/<id>.tex`. The same statement
   and proof in leanblueprint dialect (`\label`, `\lean{}`, `\uses{}`), in the style of a
   Lauter–Viray-type paper. These fragments assemble into the blueprint document, the
   project's formal write-up.
3. **A Lean file** — under `singular_moduli/QuadraticOrder/`. The machine-checked proof,
   with documentation dense enough that a reader can map every Lean step back to the
   prose argument.

**Doc-first order**: the Markdown/LaTeX proof is written (or updated) BEFORE the Lean
proof work starts. If you discover mid-proof that the prose argument is wrong or
incomplete, fix the prose first, then the Lean. The two must never diverge silently.

## 2. Statement discipline

- Lean statements are **frozen** by WP-0 (see [WORKPLAN.md](WORKPLAN.md), working
  agreement 1). Your job inside a work package is to remove `sorry`s **without changing
  the statements**. A statement change requires: update the proof docs + blueprint, PR
  flagged as a statement change, driver sign-off.
- Ground truth for Chapter 3 statements is **[ERRATA.md](ERRATA.md)**, not the thesis
  text. The thesis contains two proven-false cases (E1, E2) and a wrong regime (E5).
  The regression vectors in `QuadraticOrder/Harness/Regression.lean` fail the build if
  a count drifts — do not weaken or delete them.
- Chapter 2 statements must be transcribed from the source papers in `papers/`
  (the thesis PDF's text layer is damaged — ERRATA E7); quote the original in the
  blueprint fragment.

## 3. Lean documentation requirements

Every Lean file starts with a module docstring (`/-! ... -/`) containing, in order:

1. `# Title` — the file's single subject.
2. `**Thesis.**` — the section + numbered statement it formalizes, with corrections noted.
3. `**Human-readable companion.**` — the `proofs/<id>.md` path.
4. `**This file states/proves:**` — bullet list of public declarations.
5. `**Proof strategy**` — how the Lean proof maps to the prose proof (which prose step
   each main lemma corresponds to; where the Lean route diverges and why).
6. `**Divergence from thesis.**` — only when the Lean formulation differs; say what and why.
7. `**Status.**` — work package + frozen/stub/proved.

Additionally:
- Every public declaration gets a `/-- ... -/` docstring stating its mathematical
  content in prose (not a paraphrase of the Lean syntax).
- Inside proofs, comment every nontrivial step with the corresponding step of the prose
  proof ("-- thesis p. 19: split on k ≤ κ" style). A reader stepping through the proof
  should always know where they are in the paper argument.
- One thesis result per file; case analyses that grow past ~400 lines split into case
  files feeding an assembly file.
- Mathlib style throughout: 100-column limit, naming conventions, `variable` sections.
  The build runs the mathlib standard linter set; keep new files warning-clean.

## 4. Proof-document requirements (`proofs/*.md`)

Structure (in order): H1 title with result label → **Statement** (blockquote) →
**Role in the development** → **Proof** (complete — no "clearly", no waved steps) →
**Remarks** (errata notes, divergences, pitfalls) → **Lean correspondence** (table:
statement ↔ full Lean declaration name ↔ file ↔ status) → **References**.

Self-containedness test: a reader with graduate algebra but no access to the thesis can
verify the proof. Restate the notation you use (or link `proofs/notation.md` for the
standard symbols and restate anything nonstandard).

When a Lean proof lands, update the doc's Lean correspondence status column and flip the
blueprint fragment's `\leanok`. `leanblueprint checkdecls` (CI) verifies every `\lean{}`
name exists.

## 5. Definition of done (every work package)

- [ ] Zero `sorry` in the package's files; statements unchanged.
- [ ] `#print axioms` on each headline shows `[propext, Classical.choice, Quot.sound]`
      (plus declared `Assumptions/` axioms only where the package explicitly allows).
- [ ] Regression vectors pass (`Harness/Regression.lean`, extended if the package adds
      new closed forms — add rows validated against the brute enumerator).
- [ ] `proofs/<id>.md` and `blueprint/src/results/<id>.tex` updated; `\leanok` flipped;
      correspondence tables current.
- [ ] Module docstrings and inline step-comments meet §3.
- [ ] Build green including linter warnings for NEW files; PR into `main` (PR-gated).

## 6. No automated upstream contributions (Mathlib / Lean GitHub repos)

Agents must **not** open pull requests, issues, or review comments on Mathlib or any
other upstream Lean repository (leanprover / leanprover-community). Their contribution
guidelines require the PR — including its description, commentary, and review
responses — to be authored by the human contributor. This is a hard rule regardless of
how upstream-ready a result looks.

When something here is a genuine upstreaming candidate (e.g. the Lemma 3.2.6
square-root counts, flagged in `proofs/lem-3-2-6.md`), record it as a `TODO(upstream):`
line in the relevant Lean file's module docstring or in WORKPLAN.md, with a one-line
justification and the declaration names — and stop there. The human decides if and
when to open the PR and writes it themselves.

## 7. Repository map

| Path | What |
|------|------|
| `proofs/` | Human-readable Markdown proofs (the review surface) |
| `blueprint/src/` | LaTeX blueprint (assembles `results/*.tex`) |
| `singular_moduli/QuadraticOrder/` | Lean sources (`Defs/` = frozen definitions; `Harness/` = test oracle) |
| `papers/` | Source papers (gitignored) — GZ85, Dor88, LV15a/b, Cox, Voight |
| `ERRATA.md` | Corrected statements — Chapter 3 ground truth |
| `WORKPLAN.md` | Work packages, dependencies, milestones |
| `PLAN.md` | Architecture + verified Mathlib audit |
| `docs/proof-map.html` | Interactive dependency/status graph |
