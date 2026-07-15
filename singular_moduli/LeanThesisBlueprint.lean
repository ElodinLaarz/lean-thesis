import QuadraticOrder

/-!
# Blueprint declaration-check import shim

**Thesis.** This module has no mathematical statement.  It exposes the full
quadratic-order formalization to the repository-root documentation workspace.

**Human-readable companion.** `proofs/README.md` is the index of every result
imported here and its Markdown/LaTeX/Lean correspondence.

**This file exposes:** the public `QuadraticOrder` declarations to
leanblueprint's `checkdecls` executable.

**Proof strategy.** There is no proof: the module is a single import.  The
root Lake workspace needs an owned Lean library because `checkdecls` imports
root libraries, not libraries that appear only as path dependencies.

**Status.** WP-0 documentation infrastructure; no declarations are defined.
-/
