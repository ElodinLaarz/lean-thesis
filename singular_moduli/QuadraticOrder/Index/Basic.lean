import QuadraticOrder.Defs.Counting
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The index layer: finiteness and multiplicativity

**Thesis.** Not stated — infrastructure the thesis uses silently whenever it
multiplies counts across primes or speaks of "the number of ideals of norm n".

**Human-readable companion.** `proofs/infra-index.md` — full statements,
proofs, and the warning about why Mathlib's `Ideal.absNorm` API cannot be used
here (its multiplicativity is Dedekind-gated, and unrestricted
index-multiplicativity is FALSE for non-invertible ideals of a non-maximal
order).

**This file states/proves:**

* `idealIndex_mul_of_codisjoint` — CRT multiplicativity: `[O : I·J] = [O : I]·[O : J]`
  for comaximal `I, J`
* `finite_setOf_idealIndex_eq` — finitely many ideals of a given index `n ≥ 1`
* `idealCount_multiplicative` — `idealCount d (m·n) = idealCount d m · idealCount d n`
  for coprime `m, n`

**Proof strategy.** The comaximal case uses
`Ideal.quotientMulEquivQuotientProd`
(CRT for the quotient ring); finiteness because an index-`n` ideal contains
`n·O_d`, and the sublattices of `ℤ²` between `n·ℤ²` and `ℤ²` are finite (Smith
normal form: `Submodule.smithNormalFormOfLE` exists in Mathlib);
count-multiplicativity from the bijection `I ↦ (I + m·O, I + n·O)` whose
inverse is intersection — the primary-decomposition bookkeeping is written out
in `proofs/infra-index.md`.

**Status.** WP-A proved. Statements frozen by WP-0.
-/

namespace QuadraticOrder

variable {d : ℤ}

private lemma span_nat_toAddSubgroup (n : ℕ) :
    (Ideal.span {(n : QuadraticOrder d)}).toAddSubgroup =
      (LinearMap.range
        (LinearMap.lsmul ℤ (QuadraticOrder d) (n : ℤ))).toAddSubgroup := by
  ext x
  change x ∈ Ideal.span {(n : QuadraticOrder d)} ↔
    x ∈ LinearMap.range (LinearMap.lsmul ℤ (QuadraticOrder d) (n : ℤ))
  rw [Ideal.mem_span_singleton]
  change (n : QuadraticOrder d) ∣ x ↔
    ∃ y, (n : ℤ) • y = x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [zsmul_eq_mul] using hy.symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa [zsmul_eq_mul] using hy.symm⟩

private lemma idealIndex_span_nat (n : ℕ) (hn : 0 < n) :
    idealIndex (Ideal.span {(n : QuadraticOrder d)}) = n ^ 2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  change Nat.card
      (QuadraticOrder d ⧸ (Ideal.span {(n : QuadraticOrder d)}).toAddSubgroup) = n ^ 2
  rw [Nat.card_congr
    (AddSubgroup.quotientEquivOfEq (span_nat_toAddSubgroup (d := d) n))]
  change Nat.card (ModN (QuadraticOrder d) n) = n ^ 2
  rw [ModN.natCard_eq]
  have hfinrank : Module.finrank ℤ (QuadraticOrder d) = 2 := by
    rw [Module.finrank_eq_card_basis (basis (d := d)).basis]
    simp
  rw [hfinrank]

private lemma span_nat_le_of_idealIndex_eq {I : Ideal (QuadraticOrder d)} {n : ℕ}
    (hI : idealIndex I = n) : Ideal.span {(n : QuadraticOrder d)} ≤ I := by
  rw [Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  have hcard := card_nsmul_eq_zero'
    (x := Ideal.Quotient.mk I (1 : QuadraticOrder d))
  change Nat.card (QuadraticOrder d ⧸ I) = n at hI
  rw [hI] at hcard
  simpa using hcard

private lemma span_nat_sup_eq_top {m n : ℕ} (h : m.Coprime n) :
    Ideal.span {(m : QuadraticOrder d)} ⊔
      Ideal.span {(n : QuadraticOrder d)} = ⊤ := by
  rw [Ideal.sup_eq_top_iff_isCoprime]
  exact h.cast

private lemma idealIndex_mul_of_coprime (I J : Ideal (QuadraticOrder d))
    (h : IsCoprime I J) :
    idealIndex (I * J) = idealIndex I * idealIndex J := by
  unfold idealIndex
  rw [Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J h).toEquiv,
    Nat.card_prod]

private lemma span_nat_mul (m n : ℕ) :
    Ideal.span {(m : QuadraticOrder d)} * Ideal.span {(n : QuadraticOrder d)} =
      Ideal.span {((m * n : ℕ) : QuadraticOrder d)} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  norm_num

private lemma split_mul_eq (I : Ideal (QuadraticOrder d)) {m n : ℕ}
    (h : m.Coprime n)
    (hmnI : Ideal.span {((m * n : ℕ) : QuadraticOrder d)} ≤ I) :
    (I ⊔ Ideal.span {(m : QuadraticOrder d)}) *
        (I ⊔ Ideal.span {(n : QuadraticOrder d)}) = I := by
  let M : Ideal (QuadraticOrder d) := Ideal.span {(m : QuadraticOrder d)}
  let N : Ideal (QuadraticOrder d) := Ideal.span {(n : QuadraticOrder d)}
  have hMN : M ⊔ N = ⊤ := span_nat_sup_eq_top (d := d) h
  have hcop : (I ⊔ M) ⊔ (I ⊔ N) = ⊤ := by
    apply top_unique
    calc
      (⊤ : Ideal (QuadraticOrder d)) = M ⊔ N := hMN.symm
      _ ≤ (I ⊔ M) ⊔ (I ⊔ N) :=
        sup_le_sup (le_sup_right : M ≤ I ⊔ M) (le_sup_right : N ≤ I ⊔ N)
  apply le_antisymm
  · change (I ⊔ M) * (I ⊔ N) ≤ I
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    refine sup_le (sup_le Ideal.mul_le_right Ideal.mul_le_right) ?_
    refine sup_le Ideal.mul_le_left ?_
    rw [span_nat_mul]
    exact hmnI
  · rw [Ideal.mul_eq_inf_of_coprime hcop]
    exact le_inf le_sup_left le_sup_left

private lemma split_index_eq (I : Ideal (QuadraticOrder d)) {m n : ℕ}
    (h : m.Coprime n) (hm : 0 < m) (hn : 0 < n)
    (hI : idealIndex I = m * n) :
    idealIndex (I ⊔ Ideal.span {(m : QuadraticOrder d)}) = m ∧
      idealIndex (I ⊔ Ideal.span {(n : QuadraticOrder d)}) = n := by
  let M : Ideal (QuadraticOrder d) := Ideal.span {(m : QuadraticOrder d)}
  let N : Ideal (QuadraticOrder d) := Ideal.span {(n : QuadraticOrder d)}
  let A : Ideal (QuadraticOrder d) := I ⊔ M
  let B : Ideal (QuadraticOrder d) := I ⊔ N
  have hmnI : Ideal.span {((m * n : ℕ) : QuadraticOrder d)} ≤ I :=
    span_nat_le_of_idealIndex_eq hI
  have hprod : A * B = I := split_mul_eq I h hmnI
  have hcop : A ⊔ B = ⊤ := by
    apply top_unique
    calc
      (⊤ : Ideal (QuadraticOrder d)) = M ⊔ N :=
        (span_nat_sup_eq_top (d := d) h).symm
      _ ≤ A ⊔ B :=
        sup_le_sup (le_sup_right : M ≤ A) (le_sup_right : N ≤ B)
  have hindex : idealIndex A * idealIndex B = m * n := by
    rw [← idealIndex_mul_of_coprime A B
      (Ideal.isCoprime_iff_sup_eq.mpr hcop), hprod, hI]
  have hA_dvd : idealIndex A ∣ m ^ 2 := by
    rw [← idealIndex_span_nat (d := d) m hm]
    change A.toAddSubgroup.index ∣ M.toAddSubgroup.index
    apply AddSubgroup.index_dvd_of_le
    intro x hx
    change x ∈ A
    exact (show M ≤ A from le_sup_right) hx
  have hB_dvd : idealIndex B ∣ n ^ 2 := by
    rw [← idealIndex_span_nat (d := d) n hn]
    change B.toAddSubgroup.index ∣ N.toAddSubgroup.index
    apply AddSubgroup.index_dvd_of_le
    intro x hx
    change x ∈ B
    exact (show N ≤ B from le_sup_right) hx
  have hA_coprime_n : (idealIndex A).Coprime n :=
    (h.pow_left 2).of_dvd_left hA_dvd
  have hB_coprime_m : (idealIndex B).Coprime m :=
    (h.symm.pow_left 2).of_dvd_left hB_dvd
  have hA_mn : idealIndex A ∣ m * n := hindex ▸ dvd_mul_right _ _
  have hB_mn : idealIndex B ∣ n * m := by
    rw [mul_comm, ← hindex]
    exact dvd_mul_left _ _
  have hA_m : idealIndex A ∣ m := hA_coprime_n.dvd_of_dvd_mul_right hA_mn
  have hB_n : idealIndex B ∣ n := hB_coprime_m.dvd_of_dvd_mul_right hB_mn
  have hA_pos : 0 < idealIndex A := by
    exact pos_of_mul_pos_left (hindex.symm ▸ Nat.mul_pos hm hn) (Nat.zero_le _)
  have hB_pos : 0 < idealIndex B := by
    exact pos_of_mul_pos_right (hindex.symm ▸ Nat.mul_pos hm hn) (Nat.zero_le _)
  have hA_le : idealIndex A ≤ m := Nat.le_of_dvd hm hA_m
  have hB_le : idealIndex B ≤ n := Nat.le_of_dvd hn hB_n
  constructor <;> nlinarith

private lemma mul_sup_span_eq_left (A B : Ideal (QuadraticOrder d)) {m n : ℕ}
    (h : m.Coprime n)
    (hmA : Ideal.span {(m : QuadraticOrder d)} ≤ A)
    (hnB : Ideal.span {(n : QuadraticOrder d)} ≤ B) :
    A * B ⊔ Ideal.span {(m : QuadraticOrder d)} = A := by
  let M : Ideal (QuadraticOrder d) := Ideal.span {(m : QuadraticOrder d)}
  let N : Ideal (QuadraticOrder d) := Ideal.span {(n : QuadraticOrder d)}
  have hBM : B ⊔ M = ⊤ := by
    apply top_unique
    calc
      (⊤ : Ideal (QuadraticOrder d)) = N ⊔ M :=
        (span_nat_sup_eq_top (d := d) h).symm.trans (sup_comm _ _)
      _ ≤ B ⊔ M := sup_le_sup hnB le_rfl
  apply le_antisymm
  · exact sup_le Ideal.mul_le_right hmA
  · calc
      A = A * (⊤ : Ideal (QuadraticOrder d)) := by
        rw [← Ideal.one_eq_top, mul_one]
      _ = A * (B ⊔ M) := by rw [hBM]
      _ = A * B ⊔ A * M := Ideal.mul_sup A B M
      _ ≤ A * B ⊔ M := sup_le_sup le_rfl Ideal.mul_le_left

/-- CRT multiplicativity of the index: if `I ⊔ J = ⊤` then
`[O : I·J] = [O : I]·[O : J]`.

Unrestricted multiplicativity (without comaximality) is FALSE in a non-maximal
order — see `proofs/infra-index.md` for a counterexample — which is why the
Dedekind-gated `Ideal.absNorm` API is off-limits (PLAN §4.2). -/
theorem idealIndex_mul_of_codisjoint (I J : Ideal (QuadraticOrder d))
    (h : I ⊔ J = ⊤) :
    idealIndex (I * J) = idealIndex I * idealIndex J := by
  exact idealIndex_mul_of_coprime I J (Ideal.isCoprime_iff_sup_eq.mpr h)

/-- There are finitely many ideals of `O_d` of index `n ≥ 1`: any such ideal
is an intermediate lattice `n·O_d ⊆ I ⊆ O_d`, and `O_d/n·O_d` is finite. -/
theorem finite_setOf_idealIndex_eq (d : ℤ) {n : ℕ} (hn : 0 < n) :
    {I : Ideal (QuadraticOrder d) | idealIndex I = n}.Finite := by
  let K : Ideal (QuadraticOrder d) := Ideal.span {(n : QuadraticOrder d)}
  have hcard : Nat.card (QuadraticOrder d ⧸ K) = n ^ 2 :=
    idealIndex_span_nat (d := d) n hn
  letI : Finite (QuadraticOrder d ⧸ K) :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero 2 hn.ne'))
  let f := fun I : Ideal (QuadraticOrder d) =>
    Ideal.map (Ideal.Quotient.mk K) I
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  · let g := ((↑) : Ideal (QuadraticOrder d ⧸ K) → Set (QuadraticOrder d ⧸ K))
    letI : Finite (Ideal (QuadraticOrder d ⧸ K)) :=
      Finite.of_injective g SetLike.coe_injective
    exact Set.toFinite _
  · intro I hI J hJ hmap
    have hKI : K ≤ I := span_nat_le_of_idealIndex_eq hI
    have hKJ : K ≤ J := span_nat_le_of_idealIndex_eq hJ
    calc
      I = (f I).comap (Ideal.Quotient.mk K) := (Ideal.comap_map_mk hKI).symm
      _ = (f J).comap (Ideal.Quotient.mk K) :=
        congrArg (fun L => Ideal.comap (Ideal.Quotient.mk K) L) hmap
      _ = J := Ideal.comap_map_mk hKJ

set_option maxHeartbeats 400000 in
-- The explicit CRT equivalence below elaborates several nested quotient-ideal
-- maps; the extra budget is for elaboration, not for an unbounded proof search.
/-- The ideal count is multiplicative over coprime indices:
`idealCount d (m·n) = idealCount d m · idealCount d n` for `gcd(m,n) = 1`.

Via the CRT bijection `I ↦ (I + m·O, I + n·O)`; the proof is written out in
`proofs/infra-index.md`. -/
theorem idealCount_multiplicative (d : ℤ) {m n : ℕ} (h : m.Coprime n)
    (hm : 0 < m) (hn : 0 < n) :
    idealCount d (m * n) = idealCount d m * idealCount d n := by
  let split : {I : Ideal (QuadraticOrder d) // idealIndex I = m * n} →
      {I : Ideal (QuadraticOrder d) // idealIndex I = m} ×
        {I : Ideal (QuadraticOrder d) // idealIndex I = n} := fun I => by
    have hs := split_index_eq (d := d) (m := m) (n := n) I.1 h hm hn I.2
    exact (⟨I.1 ⊔ Ideal.span {(m : QuadraticOrder d)}, hs.1⟩,
      ⟨I.1 ⊔ Ideal.span {(n : QuadraticOrder d)}, hs.2⟩)
  let combine :
      {I : Ideal (QuadraticOrder d) // idealIndex I = m} ×
        {I : Ideal (QuadraticOrder d) // idealIndex I = n} →
      {I : Ideal (QuadraticOrder d) // idealIndex I = m * n} := fun AB => by
    let A := AB.1.1
    let B := AB.2.1
    have hmA : Ideal.span {(m : QuadraticOrder d)} ≤ A :=
      span_nat_le_of_idealIndex_eq AB.1.2
    have hnB : Ideal.span {(n : QuadraticOrder d)} ≤ B :=
      span_nat_le_of_idealIndex_eq AB.2.2
    have hAB : A ⊔ B = ⊤ := by
      apply top_unique
      calc
        (⊤ : Ideal (QuadraticOrder d)) =
            Ideal.span {(m : QuadraticOrder d)} ⊔
              Ideal.span {(n : QuadraticOrder d)} :=
          (span_nat_sup_eq_top (d := d) h).symm
        _ ≤ A ⊔ B := sup_le_sup hmA hnB
    exact ⟨A * B, by rw [idealIndex_mul_of_codisjoint A B hAB, AB.1.2, AB.2.2]⟩
  let e : {I : Ideal (QuadraticOrder d) // idealIndex I = m * n} ≃
      {I : Ideal (QuadraticOrder d) // idealIndex I = m} ×
        {I : Ideal (QuadraticOrder d) // idealIndex I = n} := {
    toFun := split
    invFun := combine
    left_inv := by
      intro I
      apply Subtype.ext
      exact split_mul_eq I.1 h (span_nat_le_of_idealIndex_eq I.2)
    right_inv := by
      rintro ⟨A, B⟩
      apply Prod.ext
      · apply Subtype.ext
        change A.1 * B.1 ⊔ Ideal.span {(m : QuadraticOrder d)} = A.1
        exact mul_sup_span_eq_left A.1 B.1 h
          (span_nat_le_of_idealIndex_eq A.2)
          (span_nat_le_of_idealIndex_eq B.2)
      · apply Subtype.ext
        change A.1 * B.1 ⊔ Ideal.span {(n : QuadraticOrder d)} = B.1
        rw [mul_comm]
        exact mul_sup_span_eq_left B.1 A.1 h.symm
          (span_nat_le_of_idealIndex_eq B.2)
          (span_nat_le_of_idealIndex_eq A.2)
    }
  unfold idealCount
  rw [Nat.card_congr e, Nat.card_prod]

end QuadraticOrder
