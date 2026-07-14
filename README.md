# lean-thesis

Formalization of *Singular Moduli and the Ideal Class Group*
(C. Geiger, MSc thesis, University of Washington, 2020) in Lean 4 / Mathlib.

## Orientation

- [PLAN.md](PLAN.md) — master plan (2026-07): what exists in Mathlib (verified
  declaration names), what must be built, layered architecture, dependency flow
  diagram, salvage assessment of the existing code, roadmap.
- [WORKPLAN.md](WORKPLAN.md) — the work broken into theorem-sized packages (WP-0 …
  WP-M) with dependencies, interfaces, acceptance criteria, and an assignment sheet.
  **Engineers: claim a package from the issue tracker and read its section first.**
- [docs/proof-map.html](docs/proof-map.html) — interactive dependency graph of every
  result, color-coded by Lean status, with a per-node detail panel and work queue.
- [ERRATA.md](ERRATA.md) — statement corrections found during planning: two cases of
  thesis Thm 3.1.2 are **false as stated** (verified counterexamples) and Cor 3.1.3's
  boundary regime needs fixing. **The formalization targets the corrected statements.**
- [THESIS_MAP.md](THESIS_MAP.md) — reference index tying each thesis statement to its
  Lean file, plus the file-header convention.
- `singular_moduli/` — the Lean code (lake project). Order construction, prime
  trichotomy, and Lemma 3.2.6 (odd p) are done and sorry-free; ideal counting
  (Thm 3.1.2 / Cor 3.1.3) is the current frontier.
- `thesis.pdf` — not tracked (gitignored); the thesis text.

## Status

Planning refresh complete (Phase 0 spike next — see PLAN.md §7). Prior work stands:
nothing built so far is affected by the errata; the p = 2 gap in `RootCounting.lean`
is exactly where the corrected statements land.
