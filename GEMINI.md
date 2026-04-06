# GEMINI.md - Project Context: lean-thesis

This project, `lean-thesis`, is a formalization of a Master's thesis in the **Lean 4** theorem prover. The primary focus is on the arithmetic of **singular moduli** and **quadratic orders**.

## Project Overview

- **Core Library:** `singular_moduli` (located in the `singular_moduli/` directory).
- **Technologies:** 
  - **Lean 4:** The primary language for formalization.
  - **Mathlib:** Heavily depends on the Lean community mathematical library (specifically version `v4.28.0` as of current configuration).
  - **Lake:** The Lean build tool used for dependency management and compilation.

## Directory Structure

- `singular_moduli/`: The root of the Lean project.
  - `lakefile.toml`: Configuration for the Lean project, including dependencies (Mathlib) and build targets.
  - `QuadraticOrder/`: Contains the core algebraic definitions and properties of quadratic orders.
    - `Basic.lean`: Definitions of the quadratic order ring, the element `τ`, and basic algebraic properties.
    - `CanonicalForm.lean`, `IdealCount.lean`, `InvertibleCount.lean`, etc.: Advanced topics in the theory of quadratic orders.
  - `QuadraticOrder.lean`: Likely a top-level module exports or definitions.

## Building and Running

Commands should be executed within the `singular_moduli/` directory.

- **Build the project:**
  ```bash
  lake build
  ```
- **Update dependencies:**
  ```bash
  lake update
  ```
- **Run tests (if available):**
  ```bash
  lake test
  ```
- **Linting (standard Mathlib-style):**
  The project uses `weak.linter.mathlibStandardSet = true` in `lakefile.toml`.

## Development Conventions

- **Mathematical Style:** The project follows standard formalization patterns found in Mathlib. Most algebraic definitions are `noncomputable`.
- **Naming:** Follows Lean 4 / Mathlib naming conventions (snake_case for theorems/definitions, UpperCamelCase for Types/Classes).
- **Documentation:** Use of `/-- ... -/` docstrings for definitions and theorems is encouraged and present in the codebase.
- **Namespaces:** Definitions are generally scoped within namespaces (e.g., `namespace QuadraticOrder`).

## Key Symbols and Definitions

- `QuadraticOrder d`: The quadratic $\mathbb{Z}$-algebra $\mathbb{Z}[x] / (x^2 - dx + (d^2 - d) / 4)$.
- `tau`: The element $\tau = \frac{d + \sqrt{d}}{2}$ in the quadratic order.
- `normForm`: The multiplicative norm for elements in the quadratic order.

## Current Status

The project is currently in development. The build now completes successfully, but several proofs are still incomplete (contain `sorry`).

- **Incomplete Proofs (`sorry`):**
  - `cardSqrts_prime_pow_coprime`: Lifts roots mod $p$ to mod $p^n$ via Hensel's lemma.
  - `cardSqrts_prime_pow_even_val`: Reduces the case $c = p^{2r} u$ to $u \pmod{p^{n-2r}}$.
  - `cardSqrts_two_pow_coprime`: Counts solutions to $x^2 \equiv u \pmod{2^n}$ for odd $u$ and $n \ge 3$. (Partially formalized, but contains a `sorry` at line 1238 regarding the lifting step).
  - `cardSqrts_two_pow_even_val`: Handles $c = 2^{2r} u$ for $n-2r \ge 3$.
