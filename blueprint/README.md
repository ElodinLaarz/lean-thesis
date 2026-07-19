# Blueprint build

The source under `blueprint/src/` is the LaTeX half of the repository's
three-layer proof rule.  From the repository root, after building the Lean
project, run:

```sh
python3 -m pip install -r blueprint/requirements.txt
leanblueprint web
leanblueprint checkdecls
```

The web command requires Graphviz and its development headers.  In a minimal
Linux image it also needs `kpsewhich` (Debian package `texlive-binaries`) so
plasTeX can resolve the result fragments in subdirectories.  A PDF build
additionally requires a TeX distribution and is intentionally not part of the
Forgejo merge gate.  The merge gate builds the web blueprint and checks every
`\lean{}` declaration; it also builds the API documentation through the
nested `singular_moduli/docbuild` project with
`DOCGEN_SRC=file lake build QuadraticOrder:docs`.  The explicit source mode is
required because doc-gen4's default source-link inference assumes GitHub,
whereas this repository is hosted on Forgejo.

The generated sites are build artifacts and are not committed.

`singular_moduli/LeanThesisBlueprint.lean` is a documentation-only import shim.
The actual project remains the nested `singular_moduli` package; the shim gives
the root workspace one Lean library for `checkdecls` to import.

## Printable PDF (`docs/blueprint.pdf`)

A self-contained, end-to-end PDF of the blueprint — every chapter, statement,
and proof — with each `\lean{}` annotation rendered as clickable links into the
Lean sources on the GitHub mirror and `\leanok` as a green "Lean-verified"
badge (statements without the badge are stated in Lean but their proofs may
still be pending). To rebuild:

    cd blueprint && python3 gen_leandecls.py     # refresh decl -> URL map
    cd src && tectonic print.tex                 # or pdflatex/latexmk
    cp print.pdf ../../docs/blueprint.pdf

`gen_leandecls.py` writes `src/macros/leandecls.tex` (committed, so the PDF
builds without a Lean toolchain); regenerate it whenever declarations move or
new `\lean{}` annotations land.
