# CLAUDE.md

**Read [AGENTS.md](AGENTS.md) first — it is binding.** It defines the three-layer rule
(Markdown proof + LaTeX blueprint fragment + documented Lean, doc-first), statement
discipline (statements are frozen; ERRATA.md overrides the thesis text), the Lean
documentation requirements, and the per-package definition of done.

Quick orientation:

- Work is organized into work packages — [WORKPLAN.md](WORKPLAN.md); claim the matching
  Forgejo issue (#3–#16) before starting.
- Chapter 3 counting statements follow the CORRECTED forms in [ERRATA.md](ERRATA.md).
  The regression suite `singular_moduli/QuadraticOrder/Harness/Regression.lean` enforces
  the corrected numbers at build time — never adjust a vector to make a proof pass.
- Build: `cd singular_moduli && lake exe cache get && lake build` (Mathlib pin
  v4.28.0). Main is PR-gated; CI must be green.
- The human-readable proof for each result lives in `proofs/<id>.md` — update it
  BEFORE changing any Lean proof.
