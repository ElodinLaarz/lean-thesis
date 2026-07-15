import QuadraticOrder.Localization.Basic
import QuadraticOrder.Localization.PrincipalMin
import QuadraticOrder.Localization.PrincipalEq

/-!
# Localization suite (import hub)

**Thesis.** Lemmas 3.2.2, 3.2.7, and 3.2.8, with the standing hypotheses
made explicit as required by ERRATA E6.2.

**Human-readable companion.** `proofs/lem-3-2-2.md`,
`proofs/lem-3-2-7.md`, and `proofs/lem-3-2-8.md`.

**This file exposes:** one thesis lemma per imported file (THESIS_MAP
convention):

* `Localization/Basic.lean`        — Lemma 3.2.2 (`O_P = ℤ_(p)[τ]`, unit criterion)
* `Localization/PrincipalMin.lean` — Lemma 3.2.7 (contraction of `(p^r(τ−a))·O_P`)
* `Localization/PrincipalEq.lean`  — Lemma 3.2.8 (equality criterion)

**Proof strategy.** This file contains no proof.  It keeps the localization
suite split into referee-sized modules while providing a stable import path.

**Status.** WP-0 import hub; WP-D owns the frozen theorem stubs.
-/
