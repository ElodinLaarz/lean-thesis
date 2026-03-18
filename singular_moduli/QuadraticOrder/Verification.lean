import QuadraticOrder.Basic

/-- Sanity check: `τ` satisfies its minimal polynomial `X² - dX + (d²-d)/4 = 0`. -/
example (d : ℤ) : (QuadraticOrder.tau (d := d)) ^ 2 - d • QuadraticOrder.tau +
    ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 :=
  QuadraticOrder.tau_minimal_poly
