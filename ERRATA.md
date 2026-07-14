# Errata and statement hygiene for "Singular Moduli and the Ideal Class Group" (Geiger, UW 2020)

Found during formalization planning (July 2026) by close re-reading plus independent
numerical verification. Two independent enumeration methods were used and agree:
(a) enumeration of ideals via the Lemma 3.2.4 normal form `(p^k, p^{m-k}(τ - A))`,
(b) enumeration of Hermite-normal-form sublattices of ℤ² closed under multiplication by τ.

**Status: needs the author's confirmation before being treated as ground truth**, but every
claimed counterexample below was checked by explicit enumeration, and the corrected
formulas are what the Lean blueprint should target. This is exactly the kind of thing the
formalization is for — each correction becomes a `decide`/`#eval` test vector in Lean.

---

## E1. Theorem 3.1.2, 2-adic inert case (D ≡ 5 mod 8), w = v₂(f) ≥ 2 — FALSE as stated

Stated count of ideals of norm 2^m (for v₂(d/4) < m): `2^{w-1+ε} - 1`.
Correct count: `2^{w+ε} - 1` for **all** w ≥ 1 (the stated w = 1 special value `2^{1+ε} - 1`
agrees with this at w = 1; the w ≠ 1 branch is wrong).

Counterexamples (explicit enumeration):

| d    | D  | f | w | m | actual | thesis says |
|------|----|---|---|---|--------|-------------|
| -48  | -3 | 4 | 2 | 3 | 3      | 1           |
| -48  | -3 | 4 | 2 | 4 | 7      | 3           |
| -192 | -3 | 8 | 3 | 5 | 7      | 3           |

Independent corroboration: 16 has 12 representations by the two reduced primitive forms of
discriminant -48, i.e. 6 invertible ideals of norm 16 — already exceeding the stated *total* of 3.

## E2. Theorem 3.1.2, 2 ramified with D ≡ 4 mod 8, m odd — FALSE as stated

Stated: `2^{w+ε} - 1` (= `2^w - 1` for m odd). Correct: `2^{w+1} - 1` for **both** parities of m.

Counterexample: d = -16 (D = -4, f = 2, w = 1), m = 3: the three ideals
`(4, 2τ)`, `(8, τ-2)`, `(8, τ-6)` of ℤ[2i] (hand-verified index-8 ideals) vs. stated 1.
Also m = 5: actual 3 vs. stated 1.

Internal contradiction in the thesis itself: the proof of Cor 3.1.3's ramified case derives
`2^w` *invertible* ideals of norm 2^m in exactly this situation, exceeding the theorem's
stated total `2^w - 1`.

## E3. Root cause of E1/E2 (proof bug, §3.3)

Roots of `x² ≡ d/4 = 2^{2r}u mod 2^{2k-m}` beyond κ are ruled out by testing
`2k - m ∈ {1, 2}`, but Lemma 3.2.6's residue condition is on `s - 2r = (2k-m) - 2r`
(r = w-1 for D odd, r = w for D ≡ 4 mod 8), **not** on `s = 2k - m`. The k = κ+1 term
contributes `2^{w-1+ε}` (inert) resp. `2^w` (D ≡ 4 mod 8, m odd) additional ideals for
*every* w whenever v₂(d/4) < m; the proof's correction term `δ·2^ε` with `δ = [w = 1]`
equals it only at w = 1.

## E4. After E1/E2, the 2-adic display collapses

With the corrections, the entire p = 2 case of Thm 3.1.2 coincides with the p ≠ 2 formulas
evaluated at p = 2:

- ramified (4 | D): `(2^{w+1} - 1)`
- inert (D ≡ 5 mod 8): `(2^{w+ε} - 1)`
- split (D ≡ 1 mod 8): `(2^{w+ε} - 1) + 2^w(m + 1 - 2w - ε)`

**The blueprint should state ONE p-uniform theorem.** The five-case 2-adic display is
unnecessary.

### Corrected Theorem 3.1.2 (target statement)

Let p | f, w = v_p(f), m ≥ 0, ε = 1 if m even else 0. Write v := v_p(d/4), meaning
v_p(d) for odd p and v₂(d) - 2 for p = 2.

- If v ≥ m: `#{a ⊆ O : [O:a] = p^m} = (p^{⌊m/2⌋+1} - 1)/(p - 1)`.
- If v < m:
  - p ramified in O_K (p | D): `(p^{w+1} - 1)/(p - 1)`
  - p inert in O_K:           `(p^{w+ε} - 1)/(p - 1)`
  - p split in O_K:           `(p^{w+ε} - 1)/(p - 1) + p^w(m + 1 - 2w - ε)`

## E5. Corollary 3.1.3 boundary regime — wrong for p = 2 with D odd; missing m > 0 hypothesis

The Thm(≥/<) vs Cor(>/≤) boundary conventions at v_p(d/4) = m are **not** an off-by-one:
each is forced as written for p odd (and p = 2 with 4 | D). Verified: p = 3 split, d = -72,
m = 2: invertible count 2 = (p^w - p^{w-1})(m+1-2w), not p^{m/2} = 3; p = 3 inert, d = -36,
m = 2: 4 = p^w + p^{w-1}; p = 3 ramified, d = -27, m = 3: 3 = p^w. **Do not harmonize the
two conditions.**

But the corollary's assignment of the boundary m = v_p(d/4) is itself false for p = 2 with
D odd (where v₂(d/4) = 2w - 2):

| d    | case      | w | m | actual | formula gives |
|------|-----------|---|---|--------|---------------|
| -48  | 2 inert   | 2 | 2 | 2      | 6 (> total 3!) |
| -112 | 2 split   | 2 | 2 | 2      | -2 (absurd)    |
| -192 | 2 inert   | 3 | 4 | 4      | 12 (> total 7) |

Also m = 0, p = 2, w = 1, D odd: stated branch yields nonsense (split: -1; inert: 3); true
count is 1. The §3.3 proof assumes m > 0 explicitly; the statement doesn't.

### Corrected Corollary 3.1.3 regime (target statement)

Number of **invertible** ideals of norm p^m in O_d (p | f, w = v_p(f), v := v_p(d/4)):

- Trivial branch — iff `m < v` **or** (`m = v` and `v = 2w - 2`, i.e. p = 2 and D odd):
  `p^{m/2}` if m even, `0` if m odd.
- Case branch — iff `m > v` **or** (`m = v ≥ 2w`, i.e. p odd or 4 | D):
  - ramified: `p^w`
  - inert: `p^w + p^{w-1}` if m even, `0` if m odd
  - split: `(p^w - p^{w-1})(m + 1 - 2w)`

This regime also fixes the m = 0 corner automatically (gives 1).

## E6. Statement hygiene (not mathematical errors, but formalization blockers)

1. **Cor 3.1.3 display** reads `#{a ⊆ O : [O:a] = p^m}` — typographically identical to
   Thm 3.1.2's LHS — but means *invertible* ideals; and it omits the case "p inert, m odd: 0"
   (proved in §3.3).
2. **Lemmas 3.2.7 / 3.2.8** rely on unrestated §3.2 standing hypotheses (p | f, hence unique
   prime over p, and O_p = ℤ_(p)[τ] via Lemma 3.2.2 + Remark 3.2.3); both are FALSE for
   split p. Formal versions must carry the hypothesis.
3. **Remark 3.2.3** (split in O ⇔ split in O_K and coprime to f) is asserted without proof
   yet load-bearing. Needs its own blueprint lemma (easy from Prop 3.2.1: for p | f,
   g mod p is the square of a linear polynomial).
4. **Two unstated bridge lemmas** for Thm 3.1.2:
   (a) every ideal of index p^m is automatically p-primary when p | f (unique prime above p);
   (b) Lemma 3.2.4's converse needs "the constructed ideal has minimal integer exactly p^k"
   so (k, [A]) ↔ a is a bijection (no double-counting across k).
5. **Lemma 3.2.6 statement**: first display line prints "2p^r when p = 2" — condition is
   p ≠ 2 (glyph loss). "u is a QR mod p^{s-2r}" for p = 2 means u ≡ 1 mod min(2^{s-2r}, 8).
   State the solution *count* directly rather than via a chosen square root of u.
6. **ε convention**: ε = 0/1 for m odd/even — the *reverse* of the natural parity indicator.
   Consistent in the thesis, but rename in the blueprint (e.g. `ε := 1 - m % 2` or use
   `Even m` case splits).
7. **Name collisions to resolve**: R(n) = Dorman's maximal-order count (§2.3) vs
   R(p^m) = locally-principal count (§3.3); ε(l) Gross-Zagier character (§2.2) vs ε parity
   flag (Thm 3.1.2) vs ε̃ weight (Conj 2.4.3); s = modulus exponent (Lem 3.2.6) vs integer
   shift (Lem 3.2.7).
8. **v_p(d/4) notation**: means v_p(d) for odd p (d/4 isn't an integer when d ≡ 1 mod 4);
   for p = 2, 2 | f forces 16 | d and v₂(d/4) = 2w - 2 + v₂(D).
9. **Minor proof typos**: Cor 3.1.3 split p ≠ 2 m-even final sum's first term prints p^w,
   should be p^{w-1}; trivial-branch sum prints φ(p^{2k-m}), means φ(p^{k-m/2}); sign slips
   in Lemma 3.2.4's two-generator reduction; Prop 3.1.1 holds for any quadratic field
   (imaginary not needed).

## E7. Chapter 2 transcription gaps (PDF text-layer damage — re-transcribe from sources)

The extracted text loses ≠, ∤, ≤, ≥ glyphs and scrambles `cases` environments. Before any
Chapter 2 blueprint node is written, transcribe verbatim from the original papers:

- **[GZ85]**: Thm 1.3 exponent normalization (8/(w₁w₂)) and Cor 1.6 inequalities
  (ℓ ≤ D/4; D ≡ 1 mod 8 ⇒ ℓ < D/8; D₁ ≡ D₂ ≡ 5 mod 8 ⇒ ℓ < D/16 — strictness unclear).
- **[Dor88]**: Thm 1.2 uses 4/(w₁w₂) with compensating 1/(2e) — reconcile normalization
  with GZ85; the genus-character definition block (pp. 6-7) is badly garbled.
- **[LV15b]**: Thm 1.5 = thesis (2.4.1)/(2.4.2) — the r-sum start index, ρ(m)'s condition
  sets, A(N)'s `p ∤ b` / `p³ ∤ b` constraints; and **all of Conj 1.7** (thesis Conj 2.4.3),
  whose two case-functions are unreadable in the text layer, including whether one case
  needs v_p(m) = 2 or ≥ 2. Also §2.1 integrality exponents (4/(w₁w₂) generically vs
  8/(w₁w₂) when some Dᵢ = -4 is the only arithmetically sensible reading).
