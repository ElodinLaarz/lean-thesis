import QuadraticOrder.Prime.ConductorPrime
import QuadraticOrder.Defs.Counting
import Mathlib.RingTheory.Ideal.IsPrimary

/-!
# Bridge lemma: prime-power index forces primary

**Thesis.** Unstated bridge (ERRATA E6.4a): the thesis counts `P`-primary
ideals via the normal form (Lemma 3.2.4) but the theorem (3.1.2) counts ALL
ideals of index `p^m` — the two agree only because, for `p ∣ f`, an ideal of
index `p^m` is automatically primary for the unique prime `P` above `p`.

**Human-readable companion.** `proofs/infra-index.md` §"Bridge lemma".

**This file states/proves:**

* `isPrimary_of_idealIndex_prime_pow` — index `p^m` (`m ≥ 1`) ⟹ `I.IsPrimary`

**Proof strategy.** Lagrange's theorem in the finite additive quotient gives
`p^m ∈ I`. Thus every prime over `I` contains `p`, so the conductor-prime
theorem identifies every such prime with the unique prime `P` above `p`.
A maximal ideal containing `I` exists and must also equal `P`; consequently
`radical I`, the infimum of all primes over `I`, equals the maximal ideal
`P`. Mathlib's `Ideal.isPrimary_of_isMaximal_radical` finishes the proof.

**Status.** WP-A proved. Statement frozen by WP-0.
-/

namespace QuadraticOrder

variable {d D : ℤ} {f p : ℕ}

/-- For `p ∣ f`: an ideal of index `p^m`, `m ≥ 1`, is primary (for the unique
prime above `p`).  This is what lets Lemma 3.2.4's count of primary ideals
equal Theorem 3.1.2*'s count of all ideals of index `p^m` (ERRATA E6.4a). -/
theorem isPrimary_of_idealIndex_prime_pow
    [ConductorPrimeSetup d D f p]
    {I : Ideal (QuadraticOrder d)} {m : ℕ} (hm : 0 < m)
    (hI : idealIndex I = p ^ m) :
    Ideal.IsPrimary I := by
  letI : Fact p.Prime :=
    ⟨ConductorPrimeSetup.p_prime (d := d) (D := D) (f := f) (p := p)⟩
  have hp_one : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow_one : 1 < p ^ m := one_lt_pow₀ hp_one hm.ne'
  -- The quotient has more than one element, so `I` is proper.
  have hproper : I ≠ ⊤ := by
    intro htop
    subst I
    have htopIndex : idealIndex (⊤ : Ideal (QuadraticOrder d)) = 1 := by
      simp [idealIndex]
    rw [htopIndex] at hI
    omega
  -- Companion proof, Lemma 0(3): the order of the finite additive quotient
  -- annihilates the class of one, hence `p^m ∈ I`.
  have hpowI : (p : QuadraticOrder d) ^ m ∈ I := by
    have hcard := card_nsmul_eq_zero'
      (x := Ideal.Quotient.mk I (1 : QuadraticOrder d))
    change Nat.card (QuadraticOrder d ⧸ I) = p ^ m at hI
    rw [hI] at hcard
    have hmem : ((p ^ m : ℕ) : QuadraticOrder d) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using hcard
    simpa using hmem
  -- Let `P` be the unique prime above the conductor prime `p`.
  obtain ⟨P, hP, hPuniq⟩ :=
    existsUnique_isPrime_mem_of_dvd_conductor
      (d := d) (D := D) (f := f) (p := p)
  -- A maximal ideal above `I` contains `p`, so uniqueness identifies it
  -- with `P`. In particular `P` is maximal and contains `I`.
  obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal I hproper
  have hpM : (p : QuadraticOrder d) ∈ M :=
    hMmax.isPrime.mem_of_pow_mem m (hIM hpowI)
  have hMP : M = P := hPuniq M ⟨hMmax.isPrime, hpM⟩
  have hIP : I ≤ P := hMP ▸ hIM
  have hPmax : P.IsMaximal := hMP ▸ hMmax
  -- Every prime above `I` contains `p` by primality, hence is `P`.
  have hprimes :
      {J : Ideal (QuadraticOrder d) | I ≤ J ∧ J.IsPrime} = {P} := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hIJ, hJprime⟩
      have hpJ : (p : QuadraticOrder d) ∈ J :=
        hJprime.mem_of_pow_mem m (hIJ hpowI)
      exact hPuniq J ⟨hJprime, hpJ⟩
    · intro hJP
      subst J
      exact ⟨hIP, hP.1⟩
  -- The radical is the infimum of those primes, hence the maximal ideal `P`.
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [Ideal.radical_eq_sInf, hprimes, sInf_singleton]
  exact hPmax

end QuadraticOrder
