# Proposition 3.1.1 — Ideal counts in the maximal order

## Statement

**Setting and notation** (restated so that this document is self-contained).

Throughout the development, for a nonsquare integer $d \equiv 0, 1 \pmod 4$ we write:

- $\tau_d := \dfrac{d+\sqrt d}{2}$, a root of
  $g_d(x) := x^2 - dx + \dfrac{d^2-d}{4} \in \mathbb{Z}[x]$ (note
  $\operatorname{disc}(g_d) = d^2 - 4\cdot\frac{d^2-d}{4} = d$);
- $\mathcal{O}_d := \mathbb{Z}[\tau_d] = \mathbb{Z} \oplus \mathbb{Z}\tau_d \cong \mathbb{Z}[x]/(g_d)$,
  the quadratic order of discriminant $d$ in $K = \mathbb{Q}(\sqrt d\,)$;
- $d = D f^2$, where $D$ is the discriminant of $K$ (a *fundamental discriminant*: either
  $D \equiv 1 \pmod 4$ and squarefree, or $D = 4k$ with $k$ squarefree and
  $k \equiv 2, 3 \pmod 4$) and $f \ge 1$ is the *conductor* of $\mathcal{O}_d$; for a prime $p$,
  $w := v_p(f)$;
- for an ideal $\mathfrak{a} \subseteq \mathcal{O}_d$, the *(index-)norm*
  $N(\mathfrak{a}) := [\mathcal{O}_d : \mathfrak{a}]$, the index of $\mathfrak{a}$ as a subgroup
  of the additive group $(\mathcal{O}_d, +)$. It is finite precisely when $\mathfrak{a} \neq 0$
  (Fact 1(2) below), so an ideal of norm $p^m$ is automatically nonzero.

The present result concerns the **maximal-order case ($f = 1$)**: then $d = D$ and
$\mathcal{O}_d = \mathcal{O}_K = \mathbb{Z}[\tau_K]$ with $\tau_K := \frac{D+\sqrt D}{2}$, the
full ring of integers of $K$. (That $\mathbb{Z}\bigl[\frac{D+\sqrt D}{2}\bigr]$ *is* the ring of
integers: for $D \equiv 1 \pmod 4$ it equals the standard
$\mathbb{Z}\bigl[\frac{1+\sqrt D}{2}\bigr]$ because
$\tau_K = \frac{D-1}{2} + \frac{1+\sqrt D}{2}$ with $\frac{D-1}{2} \in \mathbb{Z}$; for $D = 4k$
it equals $\mathbb{Z}[\sqrt k\,]$ because $\tau_K = 2k + \sqrt k$.)

**Splitting terminology.** For a rational prime $p$ we say (standard usage):

- $p$ *splits* in $\mathcal{O}_K$ if $p\mathcal{O}_K = \mathfrak{p}_1\mathfrak{p}_2$ with
  $\mathfrak{p}_1 \neq \mathfrak{p}_2$ prime;
- $p$ is *inert* in $\mathcal{O}_K$ if $p\mathcal{O}_K$ is itself prime;
- $p$ *ramifies* in $\mathcal{O}_K$ if $p\mathcal{O}_K = \mathfrak{p}^2$ for a prime
  $\mathfrak{p}$.

Step 2 of the proof shows exactly one of these occurs, detected by the Kronecker symbol.

**Kronecker symbol at $p$.** For a fundamental discriminant $D$ and a prime $p$, define
$\left(\frac{D}{p}\right)$ by:

- $p$ odd: the Legendre symbol — $0$ if $p \mid D$; $+1$ if $D$ is a nonzero square mod $p$;
  $-1$ otherwise;
- $p = 2$: $0$ if $D$ is even; $+1$ if $D \equiv 1 \pmod 8$; $-1$ if $D \equiv 5 \pmod 8$. (An
  odd fundamental discriminant satisfies $D \equiv 1 \pmod 4$, so these cases are exhaustive.)

> **Proposition 3.1.1** (ideal counts in the maximal order; scope corrected per ERRATA E6.9).
> Let $K$ be a quadratic field — real or imaginary — of discriminant $D$, with ring of integers
> $\mathcal{O}_K$. Let $p$ be a rational prime and $m \ge 0$ an integer. Then
> $$\#\bigl\{\, \mathfrak{a} \subseteq \mathcal{O}_K \text{ ideal} \;:\; N(\mathfrak{a}) = p^m \,\bigr\} \;=\; \sum_{j=0}^{m} \left(\frac{D}{p}\right)^{\!j},$$
> with the convention $0^0 = 1$. Explicitly, the count equals
> $$\begin{cases} m + 1, & \text{if } \left(\frac{D}{p}\right) = 1 \quad (p \text{ split}),\\[2pt] 1, & \text{if } \left(\frac{D}{p}\right) = -1 \text{ and } m \text{ even} \quad (p \text{ inert}), \text{ or } \left(\frac{D}{p}\right) = 0 \quad (p \text{ ramified}),\\[2pt] 0, & \text{if } \left(\frac{D}{p}\right) = -1 \text{ and } m \text{ odd} \quad (p \text{ inert}). \end{cases}$$

## Role in the development

This is the base case of the counting program: it answers, for the maximal order, the question
that Theorem 3.1.2 (all ideals) and Corollary 3.1.3 (invertible ideals) answer for non-maximal
orders at primes dividing the conductor. Downstream, it supplies the local factors at every
prime $p \nmid f$ in the CRT gluing of the full count $\#\{\mathfrak{a} : N(\mathfrak{a}) = n\}$
for arbitrary $n$ (ideals of index coprime to the conductor in $\mathcal{O}_d$ correspond
norm-preservingly to ideals of $\mathcal{O}_K$), and it is the quantity underlying Dorman's
maximal-order count $R^{\mathrm{Dor}}(n)$ in Chapter 2 (the collision-resolved name of document
`notation`, N13; the thesis writes $R(n)$). It uses the standing notation (document `notation`),
the description of the primes of $\mathbb{Z}[\tau]$ above $p$ (Proposition 3.2.1, document
`prop-3-2-1`), and standard Dedekind-domain facts assembled in Fact 1 below.

## Proof

Write $\mathcal{O} := \mathcal{O}_K = \mathbb{Z}[\tau]$, $\tau := \tau_K = \frac{D+\sqrt D}{2}$,
and $g := g_D(x) = x^2 - Dx + \frac{D^2-D}{4}$, so $\mathcal{O} \cong \mathbb{Z}[x]/(g)$. For an
ideal $\mathfrak{c} \subseteq \mathcal{O}$ let $\bar{\mathfrak c}$, $\bar g$, etc. denote
reductions mod $p$.

**Fact 1 (Dedekind toolkit).** $\mathcal{O}_K$ is a Dedekind domain, and:

1. *(Unique factorization)* Every nonzero ideal of $\mathcal{O}_K$ is uniquely a finite product
   of nonzero prime ideals, and $\mathfrak{a} \subseteq \mathfrak{b}$ iff
   $\mathfrak{b} \mid \mathfrak{a}$ ("to contain is to divide"). Nonzero primes are maximal.
   *These are the standard facts about rings of integers; see [Neu99, I.3.3, I.3.5] or [Mar18,
   Ch. 3].*
2. *(Finiteness)* Every nonzero ideal $\mathfrak{a}$ has finite index. Indeed, choose
   $0 \neq \alpha \in \mathfrak{a}$; then $n := |N_{K/\mathbb{Q}}(\alpha)| = |\alpha\bar\alpha|$
   is a nonzero integer lying in $\mathfrak{a}$ (as $\bar\alpha \in \mathcal{O}_K$), so
   $n\mathcal{O} \subseteq \mathfrak{a} \subseteq \mathcal{O}$ and
   $[\mathcal{O} : \mathfrak{a}] \le [\mathcal{O} : n\mathcal{O}] = n^2 < \infty$
   ($\mathcal{O} \cong \mathbb{Z}^2$ as a group).
3. *(Comaximal multiplicativity)* If $\mathfrak{a} + \mathfrak{b} = \mathcal{O}$ then
   $\mathfrak{a}\mathfrak{b} = \mathfrak{a} \cap \mathfrak{b}$ and, by the Chinese remainder
   theorem,
   $\mathcal{O}/\mathfrak{a}\mathfrak{b} \cong \mathcal{O}/\mathfrak{a} \times \mathcal{O}/\mathfrak{b}$;
   hence $N(\mathfrak{a}\mathfrak{b}) = N(\mathfrak{a})N(\mathfrak{b})$. Powers of distinct
   nonzero primes are comaximal: if $\mathfrak{q} \neq \mathfrak{q}'$ are nonzero primes, then
   $\mathfrak{q}^a + \mathfrak{q}'^b$ is contained in no maximal ideal (a maximal ideal
   containing it would divide both $\mathfrak{q}^a$ and $\mathfrak{q}'^b$, hence equal both
   $\mathfrak{q}$ and $\mathfrak{q}'$ by uniqueness of factorization), so it is $\mathcal{O}$.
4. *(Prime-power towers)* For a nonzero prime $\mathfrak{q}$ and $k \ge 0$,
   $N(\mathfrak{q}^k) = N(\mathfrak{q})^k$. Proof: in the filtration
   $\mathcal{O} \supseteq \mathfrak{q} \supseteq \cdots \supseteq \mathfrak{q}^k$, each quotient
   $\mathfrak{q}^i/\mathfrak{q}^{i+1}$ is an $\mathcal{O}/\mathfrak{q}\text{-vector}$ space; its
   subspaces are exactly the ideals $\mathfrak{c}$ with
   $\mathfrak{q}^{i+1} \subseteq \mathfrak{c} \subseteq \mathfrak{q}^i$, and by (1) any such
   $\mathfrak{c}$ divides $\mathfrak{q}^{i+1}$ and is divisible by $\mathfrak{q}^i$, forcing
   $\mathfrak{c} \in \{\mathfrak{q}^i, \mathfrak{q}^{i+1}\}$. Since
   $\mathfrak{q}^{i+1} \subsetneq \mathfrak{q}^i$ (uniqueness of factorization),
   $\mathfrak{q}^i/\mathfrak{q}^{i+1}$ is a *one-dimensional*
   $\mathcal{O}/\mathfrak{q}\text{-vector}$ space, so
   $\#(\mathfrak{q}^i/\mathfrak{q}^{i+1}) = N(\mathfrak{q})$ and
   $N(\mathfrak{q}^k) = \prod_{i=0}^{k-1} \#(\mathfrak{q}^i/\mathfrak{q}^{i+1}) = N(\mathfrak{q})^k$.
5. *(Primes lie over rational primes)* If $\mathfrak{q}$ is a nonzero prime, then
   $\mathfrak{q} \cap \mathbb{Z} = (q)$ for a rational prime $q$ (it is a nonzero prime ideal of
   $\mathbb{Z}$ — nonzero by the integer produced in (2)), and $N(\mathfrak{q}) \in \{q, q^2\}$:
   $\mathcal{O}/\mathfrak{q}$ is a quotient ring of $\mathcal{O}/q\mathcal{O}$, which has order
   $q^2$, and it is a finite integral domain, hence a field of characteristic $q$.

**Step 1 (Primes above $p$, via Proposition 3.2.1).** By Proposition 3.2.1 applied to
$\mathcal{O} = \mathbb{Z}[\tau] \cong \mathbb{Z}[x]/(g)$ with $d = D$: the primes of
$\mathcal{O}$ containing $p$ are exactly the ideals $\mathfrak{p}_i = (p, \, g_i(\tau))$, where
$\bar g = \prod_i \bar g_i$ is the factorization of $\bar g \in \mathbb{F}_p[x]$ into (monic)
irreducibles and $g_i \in \mathbb{Z}[x]$ is any lift of $\bar g_i$. Moreover
$$\mathcal{O}/\mathfrak{p}_i \;\cong\; \mathbb{F}_p[x]\,/\,(\bar g, \bar g_i) \;=\; \mathbb{F}_p[x]/(\bar g_i), \qquad\text{so}\qquad N(\mathfrak{p}_i) = p^{\deg \bar g_i}. \tag{1.a}$$

Since $\bar g$ is a monic quadratic over the field $\mathbb{F}_p$, exactly one of three shapes
occurs, and we claim each shape is detected by the Kronecker symbol:

$$\bar g = \begin{cases} (x-\bar a)(x - \bar b), \ \bar a \neq \bar b & \iff \left(\frac{D}{p}\right) = 1,\\ \text{irreducible} & \iff \left(\frac{D}{p}\right) = -1,\\ (x - \bar a)^2 & \iff \left(\frac{D}{p}\right) = 0. \end{cases} \tag{1.b}$$

*Proof of (1.b) for $p$ odd.* Since $2$ is invertible in $\mathbb{F}_p$, complete the square:
$\bar g(x) = \bigl(x - \tfrac{\bar D}{2}\bigr)^2 - \tfrac{\bar D}{4}$ (using
$\operatorname{disc} g = D$). So $\bar g$ has two distinct roots iff $\bar D$ is a nonzero
square in $\mathbb{F}_p$, a double root iff $\bar D = 0$, and no root (hence is irreducible,
being a quadratic) iff $\bar D$ is a nonsquare — matching the Legendre symbol, which is the
Kronecker symbol at odd $p$.

*Proof of (1.b) for $p = 2$.* Write $c := \frac{D^2 - D}{4} = \frac{D(D-1)}{4}$, the constant
term of $g$; over $\mathbb{F}_2$ the middle coefficient is $\bar D$. Three cases:

- $D$ even (i.e. $\left(\frac{D}{2}\right) = 0$; $D = 4k$): then
  $c = \frac{D}{4}(D-1) \equiv \frac{D}{4} \pmod 2$ since $D - 1$ is odd, and
  $\bar g = x^2 + \bar c = (x + \bar c)^2$ over $\mathbb{F}_2$ — a double root.
- $D \equiv 1 \pmod 8$ (i.e. $\left(\frac{D}{2}\right) = 1$): then $8 \mid D - 1$, so
  $\frac{D-1}{4}$ is even and $c = D\cdot\frac{D-1}{4}$ is even; $\bar D = 1$, so
  $\bar g = x^2 + x = x(x+1)$ — two distinct roots.
- $D \equiv 5 \pmod 8$ (i.e. $\left(\frac{D}{2}\right) = -1$): then $\frac{D-1}{4}$ is odd and
  $D$ is odd, so $c$ is odd; $\bar g = x^2 + x + 1$, which has no root in $\mathbb{F}_2$
  ($\bar g(0) = \bar g(1) = 1$) and is therefore irreducible.

Since for odd $D$ (fundamental $\Rightarrow D \equiv 1 \bmod 4$) the residues $1, 5 \bmod 8$ are
the only possibilities, (1.b) is proved in all cases.

**Step 2 (The splitting trichotomy).** We now show the three shapes in (1.b) realize the three
named splitting behaviors, and record the norms of the primes above $p$. Throughout, if
$\bar h \mid \bar g$ with lift $h$, then $g = h\,\tilde h + p\,r$ for some
$\tilde h, r \in \mathbb{Z}[x]$ (lift the complementary factor; the difference $g - h\tilde h$
reduces to $0$ mod $p$), so that, evaluating at $\tau$ (where $g(\tau) = 0$),
$$h(\tau)\,\tilde h(\tau) = -p\, r(\tau) \in p\,\mathcal{O}. \tag{2.a}$$

**Case $\left(\frac{D}{p}\right) = 1$.** Here $\bar g = (x - \bar a)(x - \bar b)$,
$\bar a \neq \bar b$, and by Step 1 the primes above $p$ are exactly
$\mathfrak{p}_1 = (p, \tau - a)$ and $\mathfrak{p}_2 = (p, \tau - b)$, each of norm $p$ by
(1.a). They are distinct: if $\mathfrak{p}_1 = \mathfrak{p}_2 =: \mathfrak{q}$, then
$(\tau - a) - (\tau - b) = b - a \in \mathfrak{q}$ and $p \in \mathfrak{q}$; but $p \nmid b - a$
in $\mathbb{Z}$ (as $\bar a \neq \bar b$), so $\gcd(b - a, p) = 1$ and $1 \in \mathfrak{q}$, a
contradiction. Finally $p\mathcal{O} = \mathfrak{p}_1\mathfrak{p}_2$: the product is generated
by $p^2$, $p(\tau - a)$, $p(\tau - b)$, and $(\tau - a)(\tau - b)$, the last lying in
$p\mathcal{O}$ by (2.a) with $h = x - a$, $\tilde h = x - b$; hence
$\mathfrak{p}_1\mathfrak{p}_2 \subseteq p\mathcal{O}$, while
$N(\mathfrak{p}_1\mathfrak{p}_2) = N(\mathfrak{p}_1)N(\mathfrak{p}_2) = p^2 = [\mathcal{O} : p\mathcal{O}]$
by Fact 1(3) (distinct maximal ideals are comaximal), so the containment of equal finite indices
is an equality. Thus $p$ **splits**.

**Case $\left(\frac{D}{p}\right) = -1$.** Here $\bar g$ is irreducible, so by Step 1 the unique
prime above $p$ is $(p, g(\tau)) = (p) = p\mathcal{O}$ (as $g(\tau) = 0$), with
$\mathcal{O}/p\mathcal{O} \cong \mathbb{F}_p[x]/(\bar g) \cong \mathbb{F}_{p^2}$ and
$N(p\mathcal{O}) = p^2$. Thus $p$ is **inert**.

**Case $\left(\frac{D}{p}\right) = 0$.** Here $\bar g = (x - \bar a)^2$, so the unique prime
above $p$ is $\mathfrak{p} = (p, \tau - a)$, of norm $p$ by (1.a). Then
$\mathfrak{p}^2 = (p^2, \, p(\tau - a), \, (\tau - a)^2) \subseteq p\mathcal{O}$, using (2.a)
with $h = \tilde h = x - a$; and
$N(\mathfrak{p}^2) = N(\mathfrak{p})^2 = p^2 = [\mathcal{O} : p\mathcal{O}]$ by Fact 1(4), so
again $\mathfrak{p}^2 = p\mathcal{O}$. Thus $p$ **ramifies**.

**Step 3 (Reduction to primes above $p$).** Let $\mathfrak{a} \subseteq \mathcal{O}$ be an ideal
with $N(\mathfrak{a}) = p^m$. Finiteness of the index forces $\mathfrak{a} \neq 0$, so by Fact
1(1) $\mathfrak{a} = \mathfrak{q}_1^{a_1}\cdots \mathfrak{q}_t^{a_t}$ uniquely, with
$\mathfrak{q}_i$ distinct nonzero primes and $a_i \ge 1$. By Fact 1(3)+(4),
$$p^m = N(\mathfrak{a}) = \prod_{i=1}^{t} N(\mathfrak{q}_i)^{a_i},$$
and by Fact 1(5) each $N(\mathfrak{q}_i)$ is a power $q_i^{f_i} > 1$ of the rational prime $q_i$
under $\mathfrak{q}_i$. By uniqueness of prime factorization in $\mathbb{Z}$, every $q_i = p$;
that is, **every prime factor of $\mathfrak{a}$ lies above** $p$. Conversely, any product of
primes above $p$ has norm a power of $p$ by the same computation. By uniqueness of the
factorization, distinct exponent vectors give distinct ideals. So
$$\#\{\mathfrak{a} : N(\mathfrak{a}) = p^m\} = \#\Bigl\{ (a_{\mathfrak{q}})_{\mathfrak{q} \mid p} \in \mathbb{Z}_{\ge 0}^{\{\mathfrak{q} \text{ above } p\}} \;:\; \textstyle\prod_{\mathfrak{q}} N(\mathfrak{q})^{a_{\mathfrak{q}}} = p^m \Bigr\}. \tag{3.a}$$
(For $m = 0$ the only solution is the zero vector, i.e. $\mathfrak{a} = \mathcal{O}$; the count
is $1$, consistent with every case below.)

**Step 4 (Counting in each case).** Combine (3.a) with Steps 1–2:

- *Split* ($\left(\frac{D}{p}\right) = 1$): the primes above $p$ are
  $\mathfrak{p}_1 \neq \mathfrak{p}_2$, both of norm $p$. Condition (3.a) reads $p^{r+s} = p^m$,
  i.e. $r + s = m$ with $r, s \ge 0$: the ideals of norm $p^m$ are exactly
  $\mathfrak{p}_1^{r}\mathfrak{p}_2^{\,m-r}$, $r \in \{0, 1, \dots, m\}$, pairwise distinct —
  that is, $m + 1$ ideals.
- *Inert* ($\left(\frac{D}{p}\right) = -1$): the unique prime above $p$ is $p\mathcal{O}$ of
  norm $p^2$; condition (3.a) reads $p^{2r} = p^m$. If $m = 2r$ is even the unique solution is
  $\mathfrak{a} = (p\mathcal{O})^{m/2} = p^{m/2}\mathcal{O}$ — one ideal; if $m$ is odd there is
  none.
- *Ramified* ($\left(\frac{D}{p}\right) = 0$): the unique prime above $p$ is $\mathfrak{p}$ of
  norm $p$; condition (3.a) reads $p^{r} = p^m$, with unique solution
  $\mathfrak{a} = \mathfrak{p}^m$ — one ideal, for every $m \ge 0$.

**Step 5 (Uniform form).** Let $\chi := \left(\frac{D}{p}\right) \in \{1, -1, 0\}$ and evaluate
$\sum_{j=0}^m \chi^j$ (convention $0^0 = 1$): for $\chi = 1$ the sum is $m + 1$; for $\chi = -1$
it telescopes to $1$ if $m$ is even and $0$ if $m$ is odd; for $\chi = 0$ only the $j = 0$ term
survives, giving $1$. This matches Step 4 in every case.

$\blacksquare$

## Remarks

**Remark 1 (Divergence from the thesis — scope).** The thesis (Prop 3.1.1, p. 11) states the
result for *imaginary* quadratic $K$ only. Per **ERRATA E6.9**, imaginarity is never used — the
proof is pure Dedekind-domain arithmetic plus the splitting trichotomy — so we state and prove
it for an arbitrary quadratic field. (Units, where real and imaginary fields genuinely differ,
never enter: we count ideals, not elements.)

**Remark 2 (Divergence from the thesis — presentation).** The thesis proof invokes the splitting
trichotomy and the norms of the primes without derivation, and does not treat $p = 2$
separately. Here the trichotomy is *derived* from Proposition 3.2.1 (primes of
$\mathbb{Z}[\tau]$ above $p$ correspond to irreducible factors of $\bar g_D$), with the $p = 2$
analysis done explicitly, and the whole statement is packaged $p\text{-uniformly}$ through the
Kronecker symbol at $p$ — as the content plan for the blueprint prescribes. The mathematical
content is unchanged.

**Remark 3 (Invertible = all, in the maximal order).** In a Dedekind domain every nonzero ideal
is invertible, so Proposition 3.1.1 simultaneously counts *all* ideals of norm $p^m$ and
*invertible* ideals of norm $p^m$. In non-maximal orders these counts genuinely differ — that is
precisely the gap between Theorem 3.1.2 and Corollary 3.1.3.

**Remark 4 ($p\text{-independence}$).** Given the splitting type, the count depends only on $m$,
not on $p$ — visible in the formula $\sum_j \chi^j$, where $p$ enters only through
$\chi = \left(\frac{D}{p}\right)$. The thesis highlights (p. 13) that this fails in non-maximal
orders: in Theorem 3.1.2 the counts grow with $p$ (e.g. the ramified count
$\frac{p^{w+1}-1}{p-1}$).

**Remark 5 (Conventions and pitfalls).** (i) The convention $0^0 = 1$ in the uniform sum is
load-bearing for the ramified case; equivalently one may write the count as
$\sum_{c \mid p^m} \chi_D(c)$, where $\chi_D$ is the completely multiplicative extension of
$\left(\frac{D}{\cdot}\right)$ with $\chi_D(1) = 1$. (ii) The case $m = 0$ is included: all
three branches correctly give $1$ (the unit ideal). Contrast Corollary 3.1.3, whose thesis
statement has an $m = 0$ defect (ERRATA E5). (iii) Speaking of an ideal of norm $p^m$
presupposes finite index, which by Fact 1(2) already excludes the zero ideal; no separate
nonzeroness hypothesis is needed. (iv) In the Lean development the norm is the additive-subgroup
index $[\mathcal{O} : \mathfrak{a}]$ (`Submodule.cardQuot` / `AddSubgroup.index`), *not*
Mathlib's bundled multiplicative `Ideal.absNorm` API — the latter is Dedekind-gated and
unavailable for the non-maximal orders treated by the neighboring results, and the development
uses one uniform norm. For $\mathcal{O}_K$ the two agree.

## Lean correspondence

| Statement | Lean declaration | File | Status |
|---|---|---|---|
| Split case: $\left(\frac{D}{p}\right) = 1 \Rightarrow$ count $= m+1$ | `QuadraticOrder.maximalIdealCount_split` | `singular_moduli/QuadraticOrder/MaximalCase.lean` | stated as `sorry` stub (WP-E) |
| Inert case: $\left(\frac{D}{p}\right) = -1 \Rightarrow$ count $=$ `if Even m then 1 else 0` | `QuadraticOrder.maximalIdealCount_inert` | `singular_moduli/QuadraticOrder/MaximalCase.lean` | stated as `sorry` stub (WP-E) |
| Ramified case: $\left(\frac{D}{p}\right) = 0 \Rightarrow$ count $= 1$ | `QuadraticOrder.maximalIdealCount_ramified` | `singular_moduli/QuadraticOrder/MaximalCase.lean` | stated as `sorry` stub (WP-E) |

Current formalization status: `MaximalCase.lean` states all three theorems as `sorry` stubs
(WP-E; statements frozen by WP-0), each with hypotheses `IsFundamentalDiscriminant D` and
`kroneckerAtPrime D p = 1` / `-1` / `0`, counting via `idealCount D (p ^ m)`. The parity split
in the inert case is carried by an if-then-else on `Even m` inside `maximalIdealCount_inert`,
per the blueprint driver's stub specification; the uniform Kronecker-sum form is prose-level
packaging of the three declarations, not a fourth declaration. Prerequisites already formalized
elsewhere in the development: the order $\mathbb{Z}[\tau_d]$, its norm form, and the
split/inert/ramified trichotomy transported across
$\mathcal{O}/(p) \cong \mathbb{F}_p[X]/(\bar g)$
(`QuadraticOrder/Prime/{PolyMod,QuotientIso,Inert,Ramified,Split}.lean` — the formal home of
Proposition 3.2.1's content).

## References

- Thesis: C. Geiger, *Singular Moduli and the Ideal Class Group*, UW 2020 — §3.1, Proposition
  3.1.1 (statement p. 11, proof p. 12); the supporting Proposition 3.2.1 is §3.2, p. 14.
- ERRATA.md, item E6.9 (scope: any quadratic field).
- [Neu99] J. Neukirch, *Algebraic Number Theory*, Springer GMW 322 — Ch. I §3 (Dedekind domains,
  unique factorization, to-contain-is-to-divide), §6 (ideal norm), §8 (splitting in extensions).
- [Mar18] D. Marcus, *Number Fields*, 2nd ed., Springer — Ch. 3, in particular Theorem 25
  (explicit splitting laws in quadratic fields, the classical form of Steps 1–2).
- [Cox13] D. Cox, *Primes of the Form* $x^2 + ny^2$, 2nd ed., Wiley — §5.2–5.3 (orders, maximal
  order of a quadratic field, Kronecker symbol conventions).
