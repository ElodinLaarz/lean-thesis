import QuadraticOrder.Defs.Counting
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The invertibility interface

**Thesis.** §1.2 calls these the "locally principal (invertible) ideals";
the equivalence of the two notions and the basic invertibility criteria are
used silently throughout §3.

**Human-readable companion.** `proofs/infra-invertibility.md`.

**This file defines/states:**

* `IsLocallyPrincipal I` — principal after localization at every prime
* `isInvertibleIdeal_iff_isLocallyPrincipal` — the interface theorem tying the
  frozen fraction-free definition `IsInvertibleIdeal` (Defs/Counting.lean) to
  the thesis's "locally principal"
* `isInvertibleIdeal_of_coprime_conductor` — ideals of index prime to the
  conductor are invertible

**Proof strategy** (WP-G): standard — invertible ⟹ locally principal by
localizing the equation `I·J = (x)`; conversely a locally principal ideal of a
Noetherian domain is invertible against its "conjugate-like" complement; the
coprime-to-conductor criterion via the localization isomorphism with the
maximal order away from `f` (Mathlib's
`Localization.localRingHom_bijective_of_not_conductor_le` is the germ).
Expect to fill genuine Mathlib gaps here — the `FractionalIdeal`
API is Dedekind-centric; see `proofs/infra-invertibility.md` for the
elementary route that avoids it.

**Status.** WP-G stubs (`sorry`); definitions frozen by WP-0 (they are part of
`A(N)`'s statement in WP-I, so they freeze early).
-/

namespace QuadraticOrder

variable {d : ℤ}

/-- `I` is locally principal: principal after localization at every prime
ideal.  The thesis's working notion of invertibility. -/
def IsLocallyPrincipal (I : Ideal (QuadraticOrder d)) : Prop :=
  ∀ (P : Ideal (QuadraticOrder d)) [P.IsPrime],
    Submodule.IsPrincipal
      (Ideal.map (algebraMap (QuadraticOrder d) (Localization.AtPrime P)) I)

/-- The interface theorem: for a nonzero ideal of the (Noetherian, domain,
when `d` is a genuine discriminant) order `O_d`, invertibility in the
fraction-free sense of `IsInvertibleIdeal` is equivalent to being locally
principal. -/
theorem isInvertibleIdeal_iff_isLocallyPrincipal
    (hd : IsDiscriminant d) {I : Ideal (QuadraticOrder d)} (hI : I ≠ ⊥) :
    IsInvertibleIdeal I ↔ IsLocallyPrincipal I := by
  sorry

/-- An ideal whose index is coprime to the conductor is invertible: away from
the conductor, `O_d` agrees with the maximal order, where every nonzero ideal
is invertible. -/
theorem isInvertibleIdeal_of_coprime_conductor
    {D : ℤ} {f : ℕ} (hD : IsFundamentalDiscriminant D)
    (hdf : d = D * (f : ℤ) ^ 2) (hf : 0 < f)
    {I : Ideal (QuadraticOrder d)} (hne : idealIndex I ≠ 0)
    (hcop : (idealIndex I).Coprime f) :
    IsInvertibleIdeal I := by
  sorry

end QuadraticOrder
