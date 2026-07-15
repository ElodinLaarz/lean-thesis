import QuadraticOrder.Basic
import QuadraticOrder.Norm
import QuadraticOrder.Discriminant
import QuadraticOrder.Verification
import QuadraticOrder.Defs.Setup
import QuadraticOrder.Defs.Counting
import QuadraticOrder.RootCounting
import QuadraticOrder.RootCounting.TwoPower
import QuadraticOrder.Prime
import QuadraticOrder.Prime.ConductorPrime
import QuadraticOrder.Index.Basic
import QuadraticOrder.Index.Primary
import QuadraticOrder.Index.Invertible
import QuadraticOrder.Units
import QuadraticOrder.CanonicalForm
import QuadraticOrder.CanonicalForm.Bijection
import QuadraticOrder.Localization
import QuadraticOrder.MaximalCase
import QuadraticOrder.IdealCount
import QuadraticOrder.InvertibleCount
import QuadraticOrder.Glue
import QuadraticOrder.Harness.Enumerate
import QuadraticOrder.Harness.Regression

/-!
# Quadratic-order formalization

**Thesis.** This is the import root for the quadratic-order portion of the
thesis, principally Chapters 1 and 3, with the corrections in `ERRATA.md`.

**Human-readable companion.** The review surface is the collection under
`proofs/`; `proofs/README.md` maps each result to its Lean home and blueprint
fragment.

**This file exposes:** every public declaration in the quadratic-order
development, including the frozen statement layer, proof modules, and the
brute-force regression harness.

**Proof strategy.** This file contains no proof.  Its import order records the
development order: definitions, arithmetic engines, order infrastructure,
headline counting results, glue, and finally the independent test oracle.

**Status.** WP-0 import hub.  Frozen statement stubs remain in their owning
work-package files until those packages are completed.
-/
