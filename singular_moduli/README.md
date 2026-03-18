# singular_moduli

`singular_moduli` is a Lean project for working with singular moduli and related objects
in the arithmetic of modular curves and quadratic fields. It provides definitions and
basic theory for quadratic orders and their elements, as a foundation for more advanced
results involving singular moduli.

## QuadraticOrder

The core algebraic structure in this project is the type `QuadraticOrder`.
At a high level, `QuadraticOrder` is intended to model (orders in) quadratic extensions
of `ℚ` (or of more general base rings) together with:

- a representation of elements of the order,
- ring operations (addition, multiplication, etc.),
- basic invariants such as the discriminant,
- standard morphisms and coercions into ambient fields/rings when available.

These constructions are designed to be usable as building blocks in the formalization
of singular moduli and related arithmetic objects.

## Building with `lake`

This project uses `lake`, the Lean 4 build tool.
To work with the repository locally:

1. Make sure you have Lean 4 and `lake` installed.
2. In the `singular_moduli` directory, run:

   ```bash
   lake build
   ```

   This compiles the project and all its dependencies.

3. To run tests (if present), use:

   ```bash
   lake test
   ```

4. To run project executables (if any are defined via `@[main]` or `lake exe` targets),
   use:

   ```bash
   lake exe <target-name>
   ```

## Documentation and CI

This repository is set up to be used with GitHub Actions for continuous integration.
A typical workflow will:

- check that the project builds with `lake build`,
- run tests with `lake test` (if tests are defined),
- optionally build documentation for the project.

If documentation generation is enabled in CI, it usually builds the Lean docs using
`lake` and then publishes the resulting HTML to GitHub Pages. Consult the repository’s
CI workflow files (in `.github/workflows/`) for the exact configuration used here.

For local experimentation with docs, you can generate them with the standard Lean 4
documentation tasks provided by `lake` (if configured in this project).

## Getting started

- Clone the repository and run `lake build` once to fetch and compile dependencies.
- Browse the source files to find the definitions and theorems you need, in particular
  the modules defining `QuadraticOrder` and its basic properties.
- Use this project as a library in other Lean developments by adding it as a dependency
  in your own `lakefile.lean`.
