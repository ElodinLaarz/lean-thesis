# notation — Notation and standing conventions (thesis §1.2, §3.2 preamble)

This is a **definitions document**: it fixes, once and for all, the notation and standing
conventions used by every Chapter 3 result document in this development. Nothing here is a
theorem; the only mathematical content is a handful of well-definedness checks, spelled out
in full in the "Proof" section. All later documents cite these items by their labels
(N1)–(N13).

## Statement

> Throughout the Chapter 3 development the following notation is in force.
>
> **(N1) Discriminants.** An integer $d$ is a *(quadratic) discriminant* if
> $d \equiv 0$ or $1 \pmod 4$. It is an *imaginary quadratic discriminant* if moreover
> $d < 0$. **Standing convention:** the letter $d$ always denotes an imaginary quadratic
> discriminant, i.e. $d < 0$ and $d \equiv 0, 1 \pmod 4$.
>
> **(N2) Fundamental discriminant and conductor.** A discriminant $D$ is *fundamental* if
> either $D \equiv 1 \pmod 4$ and $D$ is squarefree, or $D = 4m$ with $m$ squarefree and
> $m \equiv 2$ or $3 \pmod 4$. Every imaginary quadratic discriminant $d$ admits a
> **unique** factorization
> $$d = D f^2, \qquad D \text{ fundamental}, \; f \in \mathbb{Z}_{\geq 1};$$
> $f$ is called the *conductor* of $d$ (equivalently, of the order $\mathcal{O}_d$ of (N3)).
> We write $K := \mathbb{Q}(\sqrt{d}) = \mathbb{Q}(\sqrt{D})$ for the associated imaginary
> quadratic field and $\mathcal{O}_K$ for its ring of integers; then
> $D = \operatorname{disc}(K)$ and $\mathcal{O}_K = \mathbb{Z}[\omega]$ with
> $\omega := \frac{D + \sqrt{D}}{2}$.
>
> **(N3) The order $\mathcal{O}_d$.** Set
> $$g(x) := x^2 - d\,x + \frac{d^2 - d}{4} \in \mathbb{Z}[x], \qquad
> \tau := \frac{d + \sqrt{d}}{2} \in \mathbb{C}$$
> (any fixed square root $\sqrt{d}$ with positive imaginary part). Then $g$ is the minimal
> polynomial of $\tau$, $\operatorname{disc}(g) = d$, and we define
> $$\mathcal{O}_d := \mathbb{Z}[\tau] \;\cong\; \mathbb{Z}[x]/(g(x)),$$
> a free $\mathbb{Z}$-module with basis $(1, \tau)$. When the discriminant is clear from
> context we write $\mathcal{O}$ for $\mathcal{O}_d$. With $d = Df^2$ as in (N2) one has
> $\tau = f\omega + \tfrac{Df(f-1)}{2}$ and hence
> $$\mathcal{O}_d = \mathbb{Z}[f\omega] = \mathbb{Z} + f\,\mathcal{O}_K \subseteq \mathcal{O}_K,
> \qquad [\mathcal{O}_K : \mathcal{O}_d] = f .$$
>
> **(N4) Conjugation and the norm form.** Let $\bar{\tau} := d - \tau$ (the other root of
> $g$). The map fixing $\mathbb{Z}$ and sending $\tau \mapsto \bar\tau$ extends to a ring
> involution $\alpha \mapsto \bar{\alpha}$ of $\mathcal{O}_d$ (complex conjugation under any
> embedding into $\mathbb{C}$). Vieta gives
> $$\tau + \bar{\tau} = d, \qquad \tau \bar{\tau} = \frac{d^2 - d}{4},
> \qquad (\tau - \bar\tau)^2 = d.$$
> The *norm* is $N(\alpha) := \alpha \bar{\alpha}$; in coordinates,
> $$N(x + y\tau) = x^2 + d\,xy + \frac{d^2 - d}{4}\,y^2 \qquad (x, y \in \mathbb{Z}),$$
> the homogenization of $g$: for $y \neq 0$, $N(x + y\tau) = y^2\, g(-x/y)$; in particular
> $N(x + \tau) = g(-x)$ and $N(x - \tau) = g(x)$. The norm is multiplicative,
> $N(\alpha\beta) = N(\alpha) N(\beta)$, and (since $d < 0$) positive definite:
> $N(\alpha) > 0$ for all $\alpha \neq 0$.
>
> **(N5) Ideal index — THE norm convention.** For an ideal
> $\mathfrak{a} \subseteq \mathcal{O}_d$ define the *index*
> $$[\mathcal{O}_d : \mathfrak{a}] := \#\bigl(\mathcal{O}_d / \mathfrak{a}\bigr) \in
> \mathbb{Z}_{\geq 1} \cup \{0\},$$
> the cardinality of the quotient as an abelian group, with the convention that the value is
> $0$ when the quotient is infinite (this happens only for $\mathfrak{a} = (0)$). Every
> nonzero ideal has finite index. **The norm of an ideal is by definition its index**:
> $$N(\mathfrak{a}) := [\mathcal{O}_d : \mathfrak{a}]
> \qquad \text{for every nonzero ideal } \mathfrak{a},$$
> *invertible or not*. Whenever a Chapter 3 document says "ideal of norm $n$" it means an
> ideal with $[\mathcal{O}_d : \mathfrak{a}] = n$. For principal ideals the two norms agree:
> $[\mathcal{O}_d : \alpha\mathcal{O}_d] = N(\alpha)$ for $\alpha \neq 0$.
>
> **(N6) Invertible ideals.** An ideal $\mathfrak{a} \subseteq \mathcal{O}_d$ is
> *invertible* if
> $$\exists\, \mathfrak{b} \subseteq \mathcal{O}_d \text{ ideal}, \;
> \exists\, x \in \mathcal{O}_d \setminus \{0\}: \quad
> \mathfrak{a}\,\mathfrak{b} = x\,\mathcal{O}_d .$$
> (This is equivalent to invertibility of $\mathfrak{a}$ as a fractional
> $\mathcal{O}_d$-ideal, and — for these finitely generated ideals of a Noetherian domain —
> to $\mathfrak{a}$ being locally principal; the equivalences are proved in the
> invertibility-interface documents, not here.) The *class group*
> $\operatorname{Cl}(\mathcal{O}_d) = \operatorname{Pic}(\mathcal{O}_d)$ is the group of
> invertible ideals modulo nonzero principal ideals; its order is
> $h_d := \#\operatorname{Cl}(\mathcal{O}_d)$.
>
> **(N7) Counting functions.** For $n \geq 1$:
> $$r_d(n) := \#\{\mathfrak{a} \subseteq \mathcal{O}_d \text{ ideal} :
> [\mathcal{O}_d : \mathfrak{a}] = n\}, \qquad
> R_d(n) := \#\{\mathfrak{a} \subseteq \mathcal{O}_d \text{ ideal} :
> \mathfrak{a} \text{ invertible},\; [\mathcal{O}_d : \mathfrak{a}] = n\}.$$
> Both sets are finite ($\mathbb{Z}^2$ has finitely many additive subgroups of index $n$),
> so $r_d, R_d : \mathbb{Z}_{\geq 1} \to \mathbb{Z}_{\geq 0}$ are well defined.
> $r_d$ counts **all** ideals of norm $n$ (Theorem 3.1.2*), $R_d$ only the invertible ones
> (Corollary 3.1.3*); the thesis writes both counts with the same symbol
> $\#\{\mathfrak{a} \subseteq \mathcal{O} : [\mathcal{O} : \mathfrak{a}] = p^m\}$
> (ERRATA E6.1) — we never do.
>
> **(N8) Standing local setup (the "conductor prime" package).** The Chapter 3 counting
> results all take place under the following hypotheses:
> * $d < 0$ an imaginary quadratic discriminant, $d = D f^2$ with $D$ fundamental (N2);
> * $p$ a rational prime with $p \mid f$;
> * $w := v_p(f) \geq 1$, where $v_p$ denotes the $p$-adic valuation;
> * $m \in \mathbb{Z}_{\geq 0}$ the norm exponent (the target norm is $p^m$).
>
> In Lean the $d, D, f, p$ hypotheses are bundled as the class `ConductorPrimeSetup`
> (fields: $d < 0$, $d = Df^2$, $D$ fundamental, $f \geq 1$, $p$ prime, $p \mid f$);
> $w$ is derived notation, not a field of the bundle ($w = $ `padicValNat p f`, and
> $p \mid f$ with $f \geq 1$ forces $w \geq 1$), and the norm exponent $m$ is a
> separate parameter carried by each statement alongside the bundle.
>
> **(N9) The valuation $v := v_p(d/4)$.** Following ERRATA E6.8 / E4, the symbol
> $v_p(d/4)$ is **notation**, not a literal valuation of the rational number $d/4$:
> $$v := v_p(d/4) := \begin{cases} v_p(d), & p \text{ odd}, \\
> v_2(d) - 2, & p = 2. \end{cases}$$
> This is well defined and $\geq 0$: when $p = 2$ and $2 \mid f$ we have
> $v_2(d) = v_2(D) + 2w \geq 2$, so $4 \mid d$. Explicitly, under (N8),
> $$v = \begin{cases} v_p(D) + 2w \in \{2w,\, 2w + 1\}, & p \text{ odd}, \\
> v_2(D) + 2w - 2 \in \{2w - 2,\, 2w,\, 2w + 1\}, & p = 2, \end{cases}$$
> since $v_p(D) \in \{0, 1\}$ for odd $p$ and $v_2(D) \in \{0, 2, 3\}$ for fundamental $D$.
>
> **(N10) The parity flag $\varepsilon$.** For $m \in \mathbb{Z}_{\geq 0}$,
> $$\varepsilon = \varepsilon(m) := \begin{cases} 1, & m \text{ even}, \\
> 0, & m \text{ odd}. \end{cases}$$
> **Warning (ERRATA E6.6):** this is the *reverse* of the natural parity indicator
> $m \bmod 2$; equivalently $\varepsilon(m) = 1 - (m \bmod 2)$. The convention is the
> thesis's own ("let $\epsilon = 0$ or $1$ if $m$ is odd or even, respectively",
> Thm 3.1.2) and is used consistently there and here.
>
> **(N11) The Kronecker symbol at $p$.** For a fundamental discriminant $D$ and a prime
> $p$ define
> $$\chi_p(D) := \begin{cases}
> \left(\dfrac{D}{p}\right) \text{ (Legendre symbol)}, & p \text{ odd}, \\[2mm]
> 1, & p = 2,\; D \equiv 1 \pmod 8, \\
> -1, & p = 2,\; D \equiv 5 \pmod 8, \\
> 0, & p = 2,\; 4 \mid D.
> \end{cases}$$
> The three $p = 2$ cases are exhaustive for fundamental $D$ (an odd fundamental
> discriminant is $\equiv 1 \pmod 4$, hence $\equiv 1$ or $5 \pmod 8$). $\chi_p(D)$ is the
> Kronecker symbol $\left(\frac{D}{p}\right)$, and it classifies the splitting of $p$ in the
> **maximal** order $\mathcal{O}_K$:
> $$p \text{ splits} \iff \chi_p(D) = 1, \qquad
> p \text{ is inert} \iff \chi_p(D) = -1, \qquad
> p \text{ ramifies} \iff \chi_p(D) = 0 \iff p \mid D.$$
> All corrected Chapter 3 statements are phrased $p$-uniformly through $\chi_p(D)$
> (ERRATA E4); no separate $p = 2$ case displays are used.
>
> **(N12) Square-root and polynomial-root counts.** For $n \geq 1$ and $c \in \mathbb{Z}$,
> $$\mathrm{rc}(c; n) := \#\{x \in \mathbb{Z}/n\mathbb{Z} : x^2 \equiv c \pmod n\}.$$
> This is the quantity computed by Lemma 3.2.6 for $n = p^s$, $c = p^{2r} u$ with
> $p \nmid u$. Distinct from it is the count of roots of the defining polynomial $g$,
> $$\#\{A \in \mathbb{Z}/N\mathbb{Z} : g(A) \equiv 0 \pmod N\} \qquad (N \geq 1),$$
> into which the normal-form bijection (Lemma 3.2.4) converts ideal counting and which
> Lemma 3.2.6 evaluates after completing the square. The two are distinct Lean
> declarations — `cardSqrts` and `rootCountMod` respectively (see the correspondence
> table).
>
> **(N13) Name-collision resolutions (ERRATA E6.7).** The thesis reuses several symbols
> with unrelated meanings. In this development:
>
> | Symbol in thesis | Meanings in thesis | Resolution here |
> |---|---|---|
> | $R(n)$ | Dorman's maximal-order count (§2.3) **and** the locally-principal/invertible count (§3.3) | $R_d(n)$ (N7) is always the invertible-ideal count in $\mathcal{O}_d$; Dorman's count is written $R^{\mathrm{Dor}}(n)$ in Chapter 2 documents |
> | $\varepsilon$ | Gross–Zagier character $\epsilon(\ell)$ (§2.2), parity flag (Thm 3.1.2), weight $\tilde\epsilon$ (Conj 2.4.3) | $\varepsilon(m)$ is always the parity flag (N10); the Gross–Zagier character is written $\epsilon_{\mathrm{GZ}}$ and the Lauter–Viray weight $\tilde\epsilon$ in Chapter 2 documents |
> | $s$ | modulus exponent (Lem 3.2.6) **and** integer shift in $\tau - s$ (Lem 3.2.7) | $s$ is reserved for the modulus exponent of Lemma 3.2.6; the integer shift of Lemma 3.2.7 is renamed $t$ (so that lemma concerns $p^r(\tau - t)$) |

## Role in the development

Every result document in the Chapter 3 batch (`prop-3-1-1`, `thm-3-1-2`, `cor-3-1-3`, the
§3.2 lemma documents, and the bridge lemmas) opens against this notation and cites items
(N1)–(N13) instead of restating them. The norm convention (N5) is the single most
load-bearing choice: it makes the counting statements meaningful for non-invertible ideals,
where index multiplicativity fails (see Remark 3 below) and where Mathlib's Dedekind-gated
`Ideal.absNorm` API is unavailable. Items (N9)–(N11) exist specifically to support the
*corrected*, $p$-uniform statements of Theorem 3.1.2* and Corollary 3.1.3* mandated by
ERRATA E4/E5. This document has no mathematical dependencies.

## Proof

This is a definitions document; there are no theorems to prove. We record the
well-definedness checks that the definitions silently use.

**(N1)/(N3): integrality of $g$.** $\frac{d^2 - d}{4} \in \mathbb{Z}$ iff
$d^2 \equiv d \pmod 4$, i.e. iff $d \equiv 0, 1 \pmod 4$ (squares mod $4$ are $0, 1$; check
the four residues directly). Thus $g \in \mathbb{Z}[x]$ exactly for discriminants, and
$\mathbb{Z}[\tau] = \mathbb{Z} \oplus \mathbb{Z}\tau$ is a ring. Moreover
$\operatorname{disc}(g) = d^2 - 4 \cdot \frac{d^2-d}{4} = d$, and
$\tau = \frac{d + \sqrt d}{2}$, $\bar\tau = \frac{d - \sqrt d}{2}$ are precisely the two
roots of $g$, so $(\tau - \bar\tau)^2 = (\sqrt d)^2 = d$.

**(N2): existence and uniqueness of $(D, f)$.** Let $K = \mathbb{Q}(\sqrt d)$ and
$D := \operatorname{disc}(K)$, a fundamental discriminant. Both $d$ and $D$ equal
$(\text{square}) \times \operatorname{disc}(K)$-type quantities of the same squarefree
kernel: writing $d = 4^a d_0 \cdots$ precisely, $d / D$ is a positive rational whose square
root $f := \sqrt{d/D}$ is a positive integer ([Cox13, §7]; [Ste12, Prop. 6.2.6] as cited in
thesis §2.1). Uniqueness: if $D f^2 = D' f'^2$ with $D, D'$ fundamental, then $D/D'$ is a
square in $\mathbb{Q}^\times$, and two fundamental discriminants differing by a rational
square are equal (their squarefree kernels and $2$-adic parts coincide by the case analysis
in (N2)'s definition).

**(N3): $\mathcal{O}_d = \mathbb{Z} + f \mathcal{O}_K$.**
$\tau - f\omega = \frac{Df^2 + f\sqrt D}{2} - \frac{fD + f\sqrt D}{2} = \frac{Df(f-1)}{2}$,
an integer (if $D$ is odd then $f(f-1)$ is even; if $D$ is even then $2 \mid D$ directly).
Hence $\mathbb{Z}[\tau] = \mathbb{Z}[f\omega] = \mathbb{Z} + f\mathcal{O}_K$, which has
index $f$ in $\mathcal{O}_K = \mathbb{Z} + \mathbb{Z}\omega$.

**(N4): the norm form.** Conjugation is a ring homomorphism because $\bar\tau$ satisfies
the same monic minimal polynomial $g$; it is an involution since
$\overline{\bar\tau} = d - (d - \tau) = \tau$. For the coordinate formula:
$$N(x + y\tau) = (x + y\tau)(x + y\bar\tau)
= x^2 + xy(\tau + \bar\tau) + y^2 \tau\bar\tau
= x^2 + d\,xy + \frac{d^2 - d}{4}\,y^2 .$$
For $y \neq 0$ this equals $y^2\bigl((x/y)^2 + d(x/y) + \frac{d^2-d}{4}\bigr) = y^2 g(-x/y)$.
Multiplicativity is immediate from $N(\alpha) = \alpha\bar\alpha$ and conjugation being a
ring map. Positive definiteness for $d < 0$: the binary form has leading coefficient
$1 > 0$ and discriminant $d^2 - 4\cdot\frac{d^2 - d}{4} = d < 0$.

**(N5): finiteness of the index.** Let $\mathfrak{a} \neq (0)$ and pick
$\alpha \in \mathfrak{a} \setminus \{0\}$. Then
$N(\alpha) = \bar\alpha \cdot \alpha \in \mathfrak{a}$ (as $\bar\alpha \in \mathcal{O}_d$
and $\mathfrak{a}$ is an ideal) and $N(\alpha) > 0$ by (N4). Hence
$\mathfrak{a} \supseteq N(\alpha)\,\mathcal{O}_d$ and
$\#(\mathcal{O}_d/\mathfrak{a}) \leq \#(\mathcal{O}_d / N(\alpha)\mathcal{O}_d)
= N(\alpha)^2 < \infty$. Consistency on principal ideals: multiplication by $\alpha$ on
$\mathcal{O}_d \cong \mathbb{Z}^2$ is an injective linear map whose determinant is
$N(\alpha)$ (compute on the basis $(1, \tau)$ using $\tau^2 = d\tau - \frac{d^2-d}{4}$), and
the index of the image of an injective endomorphism of $\mathbb{Z}^2$ is the absolute value
of its determinant.

**(N7): finiteness of the counted sets.** An ideal of index $n \geq 1$ is in particular an
additive subgroup of $\mathcal{O}_d \cong \mathbb{Z}^2$ of index $n$, and it contains
$n\mathcal{O}_d$; subgroups of index $n$ correspond to subgroups of the finite group
$(\mathbb{Z}/n)^2$, of which there are finitely many.

**(N9): well-definedness of $v$.** For odd $p$, $v_p(d)$ is an honest valuation of the
nonzero integer $d$ (note $d/4 \notin \mathbb{Z}$ when $d \equiv 1 \pmod 4$, which is why
the literal reading fails and the convention is needed — ERRATA E6.8). For $p = 2$ with
$2 \mid f$: $v_2(d) = v_2(D) + 2\,v_2(f) = v_2(D) + 2w \geq 2$, so $4 \mid d$ and
$v = v_2(d) - 2 = v_2(d/4) \geq 0$ is the honest valuation of the integer $d/4$. The
displayed case values follow from $v_2(D) \in \{0, 2, 3\}$: fundamental $D$ is odd, or
$D = 4m$ with $m \equiv 3 \pmod 4$ ($v_2 = 2$), or $D = 4m$ with $m \equiv 2 \pmod 4$, i.e.
$8 \| D$ giving $v_2 = 3$.

**(N11): exhaustiveness and the splitting dictionary.** For fundamental $D$: either
$4 \mid D$ or $D \equiv 1 \pmod 4$, and in the latter case $D \bmod 8 \in \{1, 5\}$. The
splitting classification of $p$ in $\mathcal{O}_K$ by $\chi_p(D)$ is standard
([Cox13, Prop. 5.16 and §7]; in this development it is re-proved as part of the
prime-classification documents via factoring $g \bmod p$, cf. Prop 3.2.1 with $d = D$,
$f = 1$). It is *stated* here only to fix the meaning of "split/inert/ramified in
$\mathcal{O}_K$" appearing in all counting formulas.

$\blacksquare$

## Remarks

**Remark 1 (Divergence from the thesis: $p$-uniformity apparatus).** The thesis states
Theorem 3.1.2 with a separate five-case display for $p = 2$ (thesis p. 13). ERRATA E1–E3
show two of those five cases are false, and ERRATA E4 shows that after correction the
$p = 2$ count coincides with the odd-$p$ formulas. The symbols $\chi_p(D)$ (N11) and
$v = v_p(d/4)$ with its $p = 2$ branch (N9) do not appear in thesis §1.2; they are
introduced here precisely so the corrected results can be stated once, $p$-uniformly. Any
reader comparing against the thesis must use the ERRATA statements, not the thesis display.

**Remark 2 (Divergence from the thesis: $\varepsilon$ promoted and guarded).** In the
thesis, $\epsilon$ is defined only inline in the statement of Thm 3.1.2 and collides with
two other $\epsilon$'s (ERRATA E6.7). We promote it to standing notation (N10) with the
Lean name `epsilonEven` chosen to make the reversed-parity convention (ERRATA E6.6)
impossible to misread: $\varepsilon(m) = 1$ iff $m$ is **even**.

**Remark 3 (The norm convention is not multiplicative).** With $N(\mathfrak{a}) =
[\mathcal{O}_d : \mathfrak{a}]$ as in (N5), multiplicativity
$N(\mathfrak{a}\mathfrak{b}) = N(\mathfrak{a})N(\mathfrak{b})$ holds when $\mathfrak{a}$ or
$\mathfrak{b}$ is invertible, and when $\mathfrak{a} + \mathfrak{b} = \mathcal{O}_d$, but
**fails in general**. Standard example (inside this development's own territory): $d = -12$,
so $D = -3$, $f = 2$, $\mathcal{O}_{-12} = \mathbb{Z}[\sqrt{-3}]$ (here
$\tau = -6 + \sqrt{-3}$), and $\mathfrak{p} = (2, 1 + \sqrt{-3})$. One checks
$\mathfrak{p}^2 = 2\mathfrak{p}$, so
$[\mathcal{O} : \mathfrak{p}^2] = [\mathcal{O} : 2\mathcal{O}]\,[2\mathcal{O} : 2\mathfrak{p}]
= 4 \cdot 2 = 8 \neq 4 = [\mathcal{O} : \mathfrak{p}]^2$; in particular $\mathfrak{p}$ is
not invertible (invertibility would allow cancelling $\mathfrak{p}$ in
$\mathfrak{p}^2 = 2\mathfrak{p}$, giving $\mathfrak{p} = (2)$, contradicting the indices).
This is why the formal index layer defines `idealIndex` as the raw quotient cardinality
(`Nat.card` of $\mathcal{O}_d/\mathfrak{a}$, Mathlib's `Submodule.cardQuot` convention)
and **not** through Mathlib's `Ideal.absNorm` multiplicative API, which is Dedekind-gated
(PLAN §4, item 2).

**Remark 4 (Two counts, one thesis display).** ERRATA E6.1: the displayed set in the
thesis's Cor 3.1.3 is typographically identical to that of Thm 3.1.2 but means *invertible*
ideals. The notation $r_d$ vs $R_d$ (N7) removes the ambiguity permanently; every later
document uses exactly one of the two symbols per statement.

**Remark 5 (On ERRATA E6.8's parenthetical).** E6.8 states the convention adopted in (N9)
and the formula $v_2(d/4) = 2w - 2 + v_2(D)$, both of which are correct and are what we
use. Its parenthetical "$2 \mid f$ forces $16 \mid d$" is slightly too strong: for $D$ odd
and $w = 1$ one has $v_2(d) = 2$ (e.g. $d = -12 = -3 \cdot 2^2$), so only $4 \mid d$ holds
in general — which is all that well-definedness of $v$ requires. For $w \geq 2$ or
$4 \mid D$, $16 \mid d$ does hold.

**Remark 6 (Invertibility: definitional choice).** Thesis §1.2 defines
$\operatorname{Cl}(\mathcal{O}_d)$ via "locally principal (invertible) ideals". We take the
product-principal condition (N6) as the *primitive* definition — it is quantifier-simple
and directly checkable in Lean — and treat "locally principal" and "invertible fractional
ideal" as equivalences to be proved in the invertibility-interface document. Ideals with
index prime to $f$ are always invertible; the interesting counting happens at primes
$p \mid f$, which is exactly the standing setup (N8).

**Remark 7 (The generator of $\mathcal{O}_d$ over $\mathcal{O}_K$).** With $d = Df^2$, the
conductor-$f$ order is generated by
$f\omega = \frac{fD + f\sqrt{D}}{2}$, and $\tau$ differs from it by the integer
$\frac{Df(f-1)}{2}$ (see the (N3) check). The thesis's printed expression
$\mathbb{Z}\bigl[\frac{fD + \sqrt D}{2}\bigr]$ (§1.2, as extracted) appears to have lost an
$f$ on the $\sqrt D$ term — possibly a PDF text-layer artifact rather than a thesis typo;
either way the formula above is the correct one and the one formalized.

**Remark 8 (What is deliberately *not* defined here).** $p$-primary ideals, the normal form
$(p^k, p^{m-k}(\tau - A))$, localization $\mathcal{O}_\mathfrak{p}$, and the bridge
minimality conditions belong to the Lemma 3.2.4/3.2.7 documents. Chapter 2 notation
($J(d_1, d_2)$, $w_i$, genus characters, $A(N)$) is out of scope for this batch and will get
its own notation document after the ERRATA E7 re-transcription.

## Lean correspondence

Target files: `singular_moduli/QuadraticOrder/Defs/Setup.lean` and
`singular_moduli/QuadraticOrder/Defs/Counting.lean`. **Status note:** both `Defs/` files
exist and carry the frozen declarations below (WP-0 statement freeze: definitions are
final API; changing one requires a blueprint PR). The split between `Setup.lean` and
`Counting.lean` follows PLAN §9 (counting functions live in `Counting.lean`). Several
notions also have working precursors from the previous pass (final column).

| Item | Notion | Lean declaration | File | Status |
|---|---|---|---|---|
| N1 | $d$ is an (imaginary quadratic) discriminant | `QuadraticOrder.IsDiscriminant` | `Defs/Setup.lean` | **exists** (statement freeze); precursor: congruence hypotheses inlined in `Discriminant.lean` |
| N2 | $D$ fundamental (and $d = Df^2$, conductor) | `QuadraticOrder.IsFundamentalDiscriminant` | `Defs/Setup.lean` | **exists** (statement freeze) |
| N3 | $\mathcal{O}_d$, $\tau$, $g$ | (context) `QuadraticOrder`, `QuadraticOrder.poly`, `QuadraticOrder.tau`, `QuadraticOrder.basis` | `Basic.lean` | **exists** (previous pass, sorry-free); not part of this batch's frozen list |
| N4 | norm form $N(x + y\tau)$; conjugation | `QuadraticOrder.normForm`, `QuadraticOrder.tauConj` (with `normForm_mul`); one-variable specialization $g(a) = N(\tau - a)$ is `QuadraticOrder.normEval` | `Norm.lean`; `Defs/Setup.lean` (`normEval`) | **exist** (`Norm.lean` items proved; `normEval` statement freeze) |
| N5 | $[\mathcal{O}_d : \mathfrak{a}]$ | `QuadraticOrder.idealIndex` | `Defs/Counting.lean` | **exists** (statement freeze) — defined as `Nat.card` of the quotient (Mathlib's `Submodule.cardQuot` convention), not via `Ideal.absNorm` |
| N6 | invertible ideal | `QuadraticOrder.IsInvertibleIdeal` | `Defs/Counting.lean` | **exists** (statement freeze) |
| N7 | $r_d(n)$ | `QuadraticOrder.idealCount` | `Defs/Counting.lean` | **exists** (statement freeze) |
| N7 | $R_d(n)$ | `QuadraticOrder.invertibleIdealCount` | `Defs/Counting.lean` | **exists** (statement freeze) |
| N8 | standing hypotheses bundle | `QuadraticOrder.ConductorPrimeSetup` | `Defs/Setup.lean` | **exists** (statement freeze); fields `d_neg`, `d_eq`, `D_fund`, `f_pos`, `p_prime`, `p_dvd_f` — no $w$ or $m$ field (see N8) |
| N9 | $v = v_p(d/4)$ | `QuadraticOrder.valD4` | `Defs/Setup.lean` | **exists** (statement freeze) |
| N10 | $\varepsilon(m)$ | `QuadraticOrder.epsilonEven` | `Defs/Setup.lean` | **exists** (statement freeze) |
| N11 | $\chi_p(D)$ | `QuadraticOrder.kroneckerAtPrime` | `Defs/Setup.lean` | **exists** (statement freeze; odd-$p$ branch = Mathlib `legendreSym p D`) |
| N12 | $\mathrm{rc}(c; n)$ | `QuadraticOrder.cardSqrts` | `RootCounting.lean` | **exists**; odd-$p$ API proved, general $p = 2$ case stated in `RootCounting/TwoPower.lean` (proof pending, WP-B) |
| N12 | roots of $g$ mod $N$ | `QuadraticOrder.rootCountMod` | `Defs/Counting.lean` | **exists** (statement freeze) |
| N13 | name-collision conventions | — (blueprint-level convention, no Lean object) | — | n/a |

## References

- C. Geiger, *Singular Moduli and the Ideal Class Group*, UW thesis, 2020 — §1.2
  (notation), §2.1 (conductor, citing [Ste12, Prop. 6.2.6]), §3.1 (statements of
  Prop 3.1.1 / Thm 3.1.2 / Cor 3.1.3), §3.2 preamble (standing hypotheses $p \mid f$,
  $w = v_p(f)$), §3.3 (the $g(x) = (x - d/2)^2 - d/4$ reduction motivating (N9)).
- `ERRATA.md` (repo root): E4 (the $p$-uniform corrected Theorem 3.1.2, source of the
  $v$ and $\chi_p$ conventions), E6.1, E6.6, E6.7, E6.8 (statement hygiene adopted here).
- D. A. Cox, *Primes of the Form $x^2 + ny^2$*, 2nd ed., Wiley, 2013 — §5 (splitting and
  the Legendre/Kronecker dictionary), §7 (orders, conductor,
  $\mathcal{O} = \mathbb{Z} + f\mathcal{O}_K$, class groups of orders).
- W. Stein, *Algebraic Number Theory: A Computational Approach*, 2012 — Prop. 6.2.6
  (conductor), as cited by the thesis.
- K. Lauter, B. Viray, *On singular moduli for arbitrary discriminants*, IMRN 2015 —
  context for why non-invertible ideals must be counted (the sets behind $A(N)$).
- `PLAN.md` §4 (item 2: why the index layer avoids `Ideal.absNorm`), §6.2 (the
  `ConductorPrimeSetup` bundling pattern), §9 (file layout for `Defs/`).
