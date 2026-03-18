import QuadraticOrder.Basic

/-!
# Layer 2a: Prime Classification in QuadraticOrder

This file classifies rational primes `p` according to their behaviour in
`QuadraticOrder d`:

* **split**: `p` splits into two distinct prime ideals
* **ramified**: `p` ramifies (one prime ideal squared)
* **inert**: `p` remains prime

The classification depends on the Kronecker symbol `(d / p)`.

## Main results (TODO)

* `prime_split_iff` — `p` splits iff `(d / p) = 1`
* `prime_inert_iff` — `p` is inert iff `(d / p) = -1`
* `prime_ramified_iff` — `p` ramifies iff `p | d(d-1)` (i.e., `(d/p) = 0`)
-/

namespace QuadraticOrder

-- TODO: Layer 2a implementation

end QuadraticOrder
