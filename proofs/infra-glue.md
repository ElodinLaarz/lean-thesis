# infra-glue — Glue: counts for arbitrary norm $n$ (beyond the thesis)

This document proves the *glue layer*: the reduction of the ideal-counting problem in an
imaginary quadratic order from arbitrary norm $n$ to the prime-power counts established in
[prop-3-1-1], [thm-3-1-2], and [cor-3-1-3]. **None of the statements below appear in the
thesis** (Geiger, *Singular Moduli and the Ideal Class Group*, UW 2020): the thesis counts
ideals of norm $p^m$ only — in the maximal order for all $p$ (Prop 3.1.1) and in a
non-maximal order for $p \mid f$ (Thm 3.1.2, Cor 3.1.3) — and never assembles a count for
composite norm. The glue is the natural completion of Chapter 3 and the instrument for the
Question 3.0.1 research loop (see "Role in the development").

## Setting and notation

All notation is restated here; no other document is required to parse the statements.

* $d < 0$ is an integer with $d \equiv 0$ or $1 \pmod 4$ (an *imaginary quadratic
  discriminant*). Write $d = D f^2$ where $D$ is the *fundamental discriminant* (either
  $D \equiv 1 \pmod 4$ and squarefree, or $D = 4k$ with $k \equiv 2, 3 \pmod 4$
  squarefree) and $f \geq 1$ is the *conductor* of $d$. This factorization exists and is
  unique.
* $K = \mathbb{Q}(\sqrt{d}) = \mathbb{Q}(\sqrt{D})$ is the imaginary quadratic field of
  discriminant $D$. Set
  $$\tau_d := \frac{d + \sqrt{d}}{2}, \qquad
    \mathcal{O}_d := \mathbb{Z}[\tau_d] = \mathbb{Z} \oplus \mathbb{Z}\,\tau_d,$$
  the order of discriminant $d$ in $K$; $\mathcal{O}_K = \mathcal{O}_D =
  \mathbb{Z}[\tau_D]$ is the maximal order. Since $\sqrt{d} = f\sqrt{D}$ we have
  $\tau_d - f\tau_D = \tfrac{Df^2 - fD}{2} = \tfrac{fD(f-1)}{2} \in \mathbb{Z}$ (one of
  $f-1$, $f$ is even), so
  $$\mathcal{O}_d = \mathbb{Z} + f\,\mathcal{O}_K,$$
  and $f$ is the index $[\mathcal{O}_K : \mathcal{O}_d]$. The *conductor ideal* is
  $\mathfrak{f} := f\mathcal{O}_K$; it is an ideal of both $\mathcal{O}_d$ and
  $\mathcal{O}_K$, and $\mathfrak{f} \subseteq \mathcal{O}_d$.
* For a nonzero ideal $\mathfrak{a} \subseteq \mathcal{O}$ ($\mathcal{O}$ one of
  $\mathcal{O}_d$, $\mathcal{O}_K$), the *norm* of $\mathfrak{a}$ is the ideal index
  $$N(\mathfrak{a}) := [\mathcal{O} : \mathfrak{a}] = \#\bigl(\mathcal{O}/\mathfrak{a}\bigr),$$
  which is finite: if $0 \neq \alpha \in \mathfrak{a}$ then
  $\alpha\bar\alpha \in \mathfrak{a}$ is a nonzero rational integer $M$ (conjugation
  $\sqrt d \mapsto -\sqrt d$ stabilizes $\mathcal{O}$, see below), and
  $M\mathcal{O} \subseteq \mathfrak{a}$ has index $M^2$ in the free rank-$2$
  $\mathbb{Z}$-module $\mathcal{O}$.
* *Conjugation* $x \mapsto \bar x$ is the nontrivial field automorphism of $K$. It is a
  ring automorphism stabilizing $\mathcal{O}_d$ (indeed $\bar\tau_d = d - \tau_d \in
  \mathcal{O}_d$) and $\mathcal{O}_K$; hence for any ideal $\mathfrak{a}$, the conjugate
  $\bar{\mathfrak{a}}$ is an ideal of the same index.
* A nonzero ideal $\mathfrak{a} \subseteq \mathcal{O}_d$ is *invertible* if there is a
  fractional $\mathcal{O}_d$-ideal $\mathfrak{b}$ (a nonzero finitely generated
  $\mathcal{O}_d$-submodule of $K$) with $\mathfrak{a}\mathfrak{b} = \mathcal{O}_d$. In the
  Dedekind domain $\mathcal{O}_K$ every nonzero ideal is invertible.
* Counting functions, for $n \geq 1$:
  $$r_d(n) := \#\{\mathfrak{a} \subseteq \mathcal{O}_d \text{ ideal} : [\mathcal{O}_d : \mathfrak{a}] = n\},
    \qquad
    r_d^{\times}(n) := \#\{\mathfrak{a} \subseteq \mathcal{O}_d \text{ invertible ideal} : [\mathcal{O}_d : \mathfrak{a}] = n\},$$
  and likewise $r_D(n)$, $r_D^{\times}(n)$ in $\mathcal{O}_K$ (where
  $r_D^{\times} = r_D$). These sets are finite — $\mathcal{O}_d \cong \mathbb{Z}^2$ has
  finitely many subgroups of index $n$ ([infra-index]). We avoid the thesis's letter
  $R(\cdot)$, which collides with Dorman's $R(n)$ (ERRATA E6.7).
* $v_p$ is the $p$-adic valuation; $w := v_p(f)$. Following the thesis's convention (with
  the ERRATA E6.8 clarification), for $p \mid f$ we write
  $$v := v_p(d/4) := \begin{cases} v_p(d) & p \text{ odd},\\ v_2(d) - 2 & p = 2 \end{cases}$$
  (when $2 \mid f$ one has $16 \mid d$, so this is a nonnegative integer; in fact
  $v = 2w + v_p(D)$ for odd $p$ and $v = 2w - 2 + v_2(D)$ for $p = 2$).
* $\varepsilon = \varepsilon(m) := 1$ if $m$ is even, $0$ if $m$ is odd. **Warning**
  (ERRATA E6.6): this is the thesis's convention, the reverse of the natural parity
  indicator.
* Splitting trichotomy: a rational prime $p$ is *ramified* in $\mathcal{O}_K$ iff
  $p \mid D$; otherwise $p$ is *split* if $\chi_D(p) = 1$ and *inert* if
  $\chi_D(p) = -1$, where $\chi_D = \left(\frac{D}{\cdot}\right)$ is the Kronecker symbol
  (for odd $p \nmid D$ this is the Legendre symbol $\left(\frac{D}{p}\right)$; for $p = 2
  \nmid D$: split iff $D \equiv 1 \pmod 8$, inert iff $D \equiv 5 \pmod 8$). Throughout,
  "split/inert/ramified" refers to the behavior of $p$ in the **maximal** order.

## Statement

> **Proposition 1 (prime-power factorization of the counts).** Let $d$ be an imaginary
> quadratic discriminant and $n \geq 1$. The map
> $\mathfrak{a} \mapsto (\mathfrak{a}_p)_{p \mid n}$ sending an ideal to its primary
> components (Step 1.2 below) is a bijection
> $$\{\mathfrak{a} \subseteq \mathcal{O}_d : [\mathcal{O}_d : \mathfrak{a}] = n\}
>   \;\longleftrightarrow\;
>   \prod_{p \mid n} \{\mathfrak{b} \subseteq \mathcal{O}_d : [\mathcal{O}_d : \mathfrak{b}] = p^{v_p(n)}\},$$
> under which $\mathfrak{a}$ is invertible if and only if every component is invertible.
> Consequently
> $$r_d(n) = \prod_{p \mid n} r_d\!\left(p^{v_p(n)}\right)
>   \qquad\text{and}\qquad
>   r_d^{\times}(n) = \prod_{p \mid n} r_d^{\times}\!\left(p^{v_p(n)}\right).$$

> **Theorem 2 (conductor-avoiding correspondence).** Let $d = Df^2$ as above and let
> $n \geq 1$ satisfy $\gcd(n, f) = 1$. Then extension and contraction
> $$\mathfrak{a} \longmapsto \mathfrak{a}\mathcal{O}_K, \qquad
>   \mathfrak{A} \longmapsto \mathfrak{A} \cap \mathcal{O}_d$$
> are mutually inverse, index-preserving bijections
> $$\{\mathfrak{a} \subseteq \mathcal{O}_d : [\mathcal{O}_d : \mathfrak{a}] = n\}
>   \;\longleftrightarrow\;
>   \{\mathfrak{A} \subseteq \mathcal{O}_K : [\mathcal{O}_K : \mathfrak{A}] = n\}.$$
> Moreover every ideal of $\mathcal{O}_d$ of index coprime to $f$ is invertible. In
> particular
> $$r_d(n) = r_d^{\times}(n) = r_D(n) = r_D^{\times}(n) \qquad (\gcd(n,f) = 1).$$

> **Theorem 3 (assembled closed form).** Let $d = Df^2$ as above. For a prime $p$ and
> $m \geq 0$ define the local factors $t_p(m)$ and $u_p(m)$ as follows.
>
> *If $p \nmid f$* (maximal behavior; by Theorem 2 total and invertible counts agree):
> $$t_p(m) = u_p(m) = \begin{cases}
>     m + 1 & \text{$p$ split in } \mathcal{O}_K,\\
>     \varepsilon(m) & \text{$p$ inert in } \mathcal{O}_K,\\
>     1 & p \mid D.
>   \end{cases}$$
>
> *If $p \mid f$*, with $w = v_p(f) \geq 1$ and $v = v_p(d/4)$, the **corrected**
> Theorem 3.1.2 (ERRATA E4) gives the total local factor
> $$t_p(m) = \begin{cases}
>     \dfrac{p^{\lfloor m/2\rfloor + 1} - 1}{p - 1} & m \leq v,\\[2ex]
>     \dfrac{p^{w+1} - 1}{p - 1} & m > v, \; p \mid D,\\[2ex]
>     \dfrac{p^{w+\varepsilon(m)} - 1}{p - 1} & m > v, \; p \text{ inert},\\[2ex]
>     \dfrac{p^{w+\varepsilon(m)} - 1}{p - 1} + p^w\,(m + 1 - 2w - \varepsilon(m)) & m > v, \; p \text{ split},
>   \end{cases}$$
> and the **corrected** Corollary 3.1.3 (ERRATA E5) gives the invertible local factor
> $$u_p(m) = \begin{cases}
>     \varepsilon(m)\, p^{m/2} & m < v, \text{ or } \bigl(m = v \text{ and } v = 2w-2\bigr),\\
>     p^w & \bigl(m > v, \text{ or } m = v \geq 2w\bigr), \; p \mid D,\\
>     \varepsilon(m)\,\bigl(p^w + p^{w-1}\bigr) & \bigl(m > v, \text{ or } m = v \geq 2w\bigr), \; p \text{ inert},\\
>     \bigl(p^w - p^{w-1}\bigr)(m + 1 - 2w) & \bigl(m > v, \text{ or } m = v \geq 2w\bigr), \; p \text{ split}
>   \end{cases}$$
> (read $\varepsilon(m)\,p^{m/2}$ as $p^{m/2}$ for $m$ even and $0$ for $m$ odd; the two
> regimes are exhaustive and mutually exclusive: for $p \mid f$ one has
> $v \in \{2w, 2w+1\}$ when $p$ is odd, and $v \in \{2w-2, 2w, 2w+1\}$ when $p = 2$, with
> $v = 2w - 2$ iff $D$ is odd; so at $m = v$ exactly one of $v = 2w-2$, $v \geq 2w$
> holds).
>
> Then for every $n \geq 1$:
> $$r_d(n) = \prod_{p \mid n} t_p\bigl(v_p(n)\bigr),
>   \qquad
>   r_d^{\times}(n) = \prod_{p \mid n} u_p\bigl(v_p(n)\bigr).$$
> (Equivalently, products over all primes: $t_p(0) = u_p(0) = 1$ for every $p$.)

## Role in the development

This is the counting instrument for the **Question 3.0.1 falsification loop** (thesis
§3.0, §3.4; PLAN Phase 4, WORKPLAN WP-H/WP-L). Lauter–Viray's Theorem 2.4.2 expresses
$v_\ell(F(m))$ as a weighted sum of counts $A(m/\ell^r)$ of invertible ideals of
*composite* norm in $\mathcal{O}_{d_1}$, valid only for $\gcd(m, f_1) = 1$; Question 3.0.1
asks for a reformulation of $A(N)$ (display (2.4.2)) valid without that hypothesis, and
any candidate reformulation must be tested numerically against $v_\ell(F(m))$ data — which
requires exact counts of invertible ideals of arbitrary norm $n$, including $n$ meeting
the conductor. Theorem 3 supplies exactly that closed form, turning the prime-power
results [prop-3-1-1], [thm-3-1-2], [cor-3-1-3] into a decidable formula that can be
checked against brute-force lattice enumeration and Sage oracles in seconds. Its proof
consumes the index layer of [infra-index] (finiteness, CRT multiplicativity for comaximal
ideals, Lagrange facts) and nothing else beyond the cited counting results; downstream it
also feeds the formalization of the §3.4 $\mathbb{G}_a/\mathbb{G}_m/\mathbb{P}^1(\mathbb{Z}/p^r)$
observation.

## Proof

Throughout, $\mathcal{O} := \mathcal{O}_d$ and all ideals are nonzero (finite index forces
this). We freely use that $\mathcal{O} \cong \mathbb{Z}^2$ as an additive group.

### Step 0: index preliminaries

These facts belong to the index layer [infra-index]; proofs are included for
self-containedness.

**Fact 0.1.** *If $[\mathcal{O} : \mathfrak{a}] = N < \infty$ then $N \in \mathfrak{a}$;
in particular $N\mathcal{O} \subseteq \mathfrak{a}$.*
Indeed, the additive group $\mathcal{O}/\mathfrak{a}$ has order $N$, so
$N \cdot (1 + \mathfrak{a}) = 0$ by Lagrange, i.e. $N = N \cdot 1 \in \mathfrak{a}$.

**Fact 0.2.** *If $\mathfrak{b} \subseteq \mathfrak{c} \subseteq \mathcal{O}$ with
$[\mathcal{O} : \mathfrak{b}] < \infty$, then $[\mathcal{O} : \mathfrak{c}]$ divides
$[\mathcal{O} : \mathfrak{b}]$* (Lagrange:
$[\mathcal{O} : \mathfrak{b}] = [\mathcal{O} : \mathfrak{c}]\,[\mathfrak{c} : \mathfrak{b}]$).

**Fact 0.3.** *Ideals of coprime finite indices are comaximal.* If
$\gcd([\mathcal{O}:\mathfrak{b}], [\mathcal{O}:\mathfrak{c}]) = 1$, then by Fact 0.2 the
index of $\mathfrak{b} + \mathfrak{c}$ divides both, hence equals $1$.

**Fact 0.4.** *If $\mathfrak{b}, \mathfrak{c}$ have finite indices $N_\mathfrak{b},
N_\mathfrak{c}$, then $[\mathcal{O} : \mathfrak{b}\mathfrak{c}]$ is finite and divides
$N_\mathfrak{b}^2 N_\mathfrak{c}$.* By Fact 0.1, $N_\mathfrak{b} \in \mathfrak{b}$, so
$N_\mathfrak{b}\mathfrak{c} \subseteq \mathfrak{b}\mathfrak{c}$; and
$[\mathcal{O} : N_\mathfrak{b}\mathfrak{c}]
 = [\mathcal{O} : N_\mathfrak{b}\mathcal{O}]\,[N_\mathfrak{b}\mathcal{O} : N_\mathfrak{b}\mathfrak{c}]
 = N_\mathfrak{b}^2\, N_\mathfrak{c}$
(multiplication by $N_\mathfrak{b}$ is injective on $\mathcal{O}$ and carries
$\mathcal{O}/\mathfrak{c}$ isomorphically onto
$N_\mathfrak{b}\mathcal{O}/N_\mathfrak{b}\mathfrak{c}$). Conclude by Fact 0.2.

**Fact 0.5.** *For comaximal $\mathfrak{b}, \mathfrak{c}$:
$\mathfrak{b} \cap \mathfrak{c} = \mathfrak{b}\mathfrak{c}$.* The inclusion $\supseteq$
is generic. For $\subseteq$: write $1 = b + c$ with $b \in \mathfrak{b}$,
$c \in \mathfrak{c}$; then $x \in \mathfrak{b} \cap \mathfrak{c}$ gives
$x = xb + xc \in \mathfrak{c}\mathfrak{b} + \mathfrak{b}\mathfrak{c} =
\mathfrak{b}\mathfrak{c}$.

**Fact 0.6 (CRT).** *If $\mathfrak{b}_1, \dots, \mathfrak{b}_k$ are pairwise comaximal
ideals, the natural map
$\mathcal{O}/\bigcap_i \mathfrak{b}_i \to \prod_i \mathcal{O}/\mathfrak{b}_i$ is a ring
isomorphism.* Standard; surjectivity uses that $\mathfrak{b}_i$ is comaximal with
$\bigcap_{j \neq i} \mathfrak{b}_j$, which follows from pairwise comaximality.

### Part 1: proof of Proposition 1

Let $[\mathcal{O} : \mathfrak{a}] = n$ and put $M := \mathcal{O}/\mathfrak{a}$, a finite
$\mathcal{O}$-module of cardinality $n$.

**Step 1.1 (primary decomposition of $M$ is $\mathcal{O}$-stable).** As a finite abelian
group, $M = \bigoplus_{p \mid n} M_p$, where
$M_p := \{x \in M : p^k x = 0 \text{ for some } k\}$ is the $p$-primary (Sylow)
component, of order $p^{v_p(n)}$ (structure theorem for finite abelian groups). Each
$M_p$ is an $\mathcal{O}$-submodule: multiplication by any $y \in \mathcal{O}$ is an
additive endomorphism $\varphi$ of $M$, and $p^k x = 0$ implies
$p^k \varphi(x) = \varphi(p^k x) = 0$. Hence $M = \bigoplus_p M_p$ is a direct sum of
$\mathcal{O}$-modules and the projections $\pi_p : M \to M_p$ are $\mathcal{O}$-linear.

**Step 1.2 (components).** Define
$$\mathfrak{a}_p := \ker\bigl(\mathcal{O} \twoheadrightarrow M \xrightarrow{\;\pi_p\;} M_p\bigr).$$
This is an ideal containing $\mathfrak{a}$, and since both maps are surjective,
$\mathcal{O}/\mathfrak{a}_p \cong M_p$, so
$[\mathcal{O} : \mathfrak{a}_p] = p^{v_p(n)}$. Moreover
$$\bigcap_{p \mid n} \mathfrak{a}_p
  = \ker\Bigl(\mathcal{O} \to \bigoplus_{p \mid n} M_p = M\Bigr) = \mathfrak{a}.$$

**Step 1.3 (the inverse map).** Conversely, let $(\mathfrak{b}_p)_{p \mid n}$ be ideals
with $[\mathcal{O} : \mathfrak{b}_p] = p^{v_p(n)}$, and set
$\mathfrak{b} := \bigcap_{p} \mathfrak{b}_p$. The $\mathfrak{b}_p$ are pairwise comaximal
(Fact 0.3: prime powers of distinct primes are coprime), so by Fact 0.6
$$\mathcal{O}/\mathfrak{b} \;\cong\; \prod_{p \mid n} \mathcal{O}/\mathfrak{b}_p,$$
whence $[\mathcal{O} : \mathfrak{b}] = \prod_p p^{v_p(n)} = n$. The $p$-primary component
of the right-hand side is exactly the factor $\mathcal{O}/\mathfrak{b}_p$ (a $p$-group,
while the other factors have order prime to $p$), so under the isomorphism the composite
$\mathcal{O} \to \mathcal{O}/\mathfrak{b} \xrightarrow{\pi_p} (\mathcal{O}/\mathfrak{b})_p$
is the natural surjection $\mathcal{O} \to \mathcal{O}/\mathfrak{b}_p$; its kernel is
$\mathfrak{b}_p$. Thus the component construction of Step 1.2 applied to $\mathfrak{b}$
recovers $(\mathfrak{b}_p)_p$. Together with Step 1.2
($\bigcap_p \mathfrak{a}_p = \mathfrak{a}$), the two constructions are mutually inverse
bijections. Taking cardinalities gives
$r_d(n) = \prod_{p \mid n} r_d(p^{v_p(n)})$.

**Step 1.4 (invertibility transfers).** By Fact 0.5 and induction, comaximality gives
$\mathfrak{a} = \bigcap_p \mathfrak{a}_p = \prod_p \mathfrak{a}_p$.

*If every $\mathfrak{a}_p$ is invertible*, say
$\mathfrak{a}_p \mathfrak{c}_p = \mathcal{O}$ with $\mathfrak{c}_p$ fractional, then
$\mathfrak{a} \cdot \prod_p \mathfrak{c}_p = \mathcal{O}$, so $\mathfrak{a}$ is
invertible.

*If $\mathfrak{a}$ is invertible*, say $\mathfrak{a}\mathfrak{c} = \mathcal{O}$, then for
each $p$,
$$\mathfrak{a}_p \cdot \Bigl(\mathfrak{c} \prod_{q \neq p} \mathfrak{a}_q\Bigr)
  = \mathfrak{c}\,\mathfrak{a} = \mathcal{O},$$
so $\mathfrak{a}_p$ is invertible. Hence the bijection of Step 1.3 restricts to a
bijection between invertible ideals of index $n$ and tuples of invertible ideals of the
prescribed prime-power indices, giving
$r_d^{\times}(n) = \prod_{p \mid n} r_d^{\times}(p^{v_p(n)})$. $\blacksquare$

### Part 2: the conductor-avoiding correspondence

Fix $N \geq 1$ with $\gcd(N, f) = 1$ and choose $\alpha, \beta \in \mathbb{Z}$ with
$$1 = \alpha N + \beta f.$$
Recall $f\mathcal{O}_K \subseteq \mathcal{O}_d$.

**Lemma 2.1 (mod-$N$ comparison).** *Let $\gcd(N, f) = 1$. Then:*
1. $\mathcal{O}_d \cap N\mathcal{O}_K = N\mathcal{O}_d$;
2. *the inclusion $\mathcal{O}_d \hookrightarrow \mathcal{O}_K$ induces a ring
   isomorphism $\mathcal{O}_d/N\mathcal{O}_d \xrightarrow{\;\sim\;}
   \mathcal{O}_K/N\mathcal{O}_K$.*

*Proof.* (1) $\supseteq$ is clear. For $\subseteq$, let $x = Ny \in \mathcal{O}_d$ with
$y \in \mathcal{O}_K$. Then
$$y = \alpha N y + \beta f y = \alpha x + \beta (fy),$$
and $\alpha x \in \mathcal{O}_d$, while $fy \in f\mathcal{O}_K \subseteq \mathcal{O}_d$.
So $y \in \mathcal{O}_d$ and $x = Ny \in N\mathcal{O}_d$.

(2) The composite $\mathcal{O}_d \hookrightarrow \mathcal{O}_K \to
\mathcal{O}_K/N\mathcal{O}_K$ is a ring homomorphism with kernel
$\mathcal{O}_d \cap N\mathcal{O}_K = N\mathcal{O}_d$ by (1), so the induced map is
injective. For surjectivity, let $z \in \mathcal{O}_K$; then
$$z = \alpha N z + \beta f z \equiv \beta f z \pmod{N\mathcal{O}_K},$$
and $\beta f z \in \mathcal{O}_d$. (Consistency check: both quotients have cardinality
$N^2$, as quotients of free rank-$2$ $\mathbb{Z}$-modules by $N$-multiples.)
$\blacksquare$

**Lemma 2.2 (extension–contraction).** *Let $\mathfrak{c} \subseteq \mathcal{O}_d$ be an
ideal of finite index $N$ with $\gcd(N, f) = 1$. Then:*
1. $\mathfrak{c}\mathcal{O}_K = \mathfrak{c} + N\mathcal{O}_K$;
2. $\mathfrak{c}\mathcal{O}_K \cap \mathcal{O}_d = \mathfrak{c}$;
3. $[\mathcal{O}_K : \mathfrak{c}\mathcal{O}_K] = N$.

*Proof.* (1) $\supseteq$: $\mathfrak{c} \subseteq \mathfrak{c}\mathcal{O}_K$, and
$N \in \mathfrak{c}$ (Fact 0.1) gives $N\mathcal{O}_K \subseteq \mathfrak{c}\mathcal{O}_K$.
$\subseteq$: a general element of $\mathfrak{c}\mathcal{O}_K$ is a finite sum of products
$cz$ with $c \in \mathfrak{c}$, $z \in \mathcal{O}_K$; and
$$cz = \alpha N (cz) + \beta\, c\,(fz) \in N\mathcal{O}_K + \mathfrak{c},$$
since $fz \in \mathcal{O}_d$ makes $c(fz) \in \mathfrak{c}$.

(2) $\supseteq$ is clear. For $\subseteq$, let
$x \in \mathfrak{c}\mathcal{O}_K \cap \mathcal{O}_d$. By (1), $x = c + Ny$ with
$c \in \mathfrak{c}$, $y \in \mathcal{O}_K$. Then
$Ny = x - c \in \mathcal{O}_d \cap N\mathcal{O}_K = N\mathcal{O}_d$ (Lemma 2.1(1)), so
$Ny \in N\mathcal{O}_d \subseteq \mathfrak{c}$ (Fact 0.1), hence $x \in \mathfrak{c}$.

(3) Under the isomorphism $\varphi : \mathcal{O}_d/N\mathcal{O}_d \to
\mathcal{O}_K/N\mathcal{O}_K$ of Lemma 2.1(2), the image of the ideal
$\mathfrak{c}/N\mathcal{O}_d$ is $(\mathfrak{c} + N\mathcal{O}_K)/N\mathcal{O}_K =
\mathfrak{c}\mathcal{O}_K/N\mathcal{O}_K$ by (1). Since $\varphi$ is an isomorphism of
rings,
$$[\mathcal{O}_K : \mathfrak{c}\mathcal{O}_K]
  = \bigl[\mathcal{O}_K/N\mathcal{O}_K : \mathfrak{c}\mathcal{O}_K/N\mathcal{O}_K\bigr]
  = \bigl[\mathcal{O}_d/N\mathcal{O}_d : \mathfrak{c}/N\mathcal{O}_d\bigr]
  = N. \qquad \blacksquare$$

**Proof of Theorem 2.** Fix $n$ with $\gcd(n, f) = 1$ and let $\varphi$ be the
isomorphism of Lemma 2.1(2) with $N = n$.

*Bijection.* Every ideal of index $n$ in $\mathcal{O}_d$ (resp. $\mathcal{O}_K$) contains
$n\mathcal{O}_d$ (resp. $n\mathcal{O}_K$) by Fact 0.1, so such ideals correspond exactly
to ideals of the quotient ring by $n$ whose own quotient has cardinality $n$. The ring
isomorphism $\varphi$ matches the two collections bijectively, preserving indices. It
remains to identify the abstract bijection with extension/contraction. For
$\mathfrak{a} \subseteq \mathcal{O}_d$ of index $n$, Lemma 2.2(1) shows
$\varphi(\mathfrak{a}/n\mathcal{O}_d) = \mathfrak{a}\mathcal{O}_K/n\mathcal{O}_K$, so the
forward map is $\mathfrak{a} \mapsto \mathfrak{a}\mathcal{O}_K$, with
$[\mathcal{O}_K : \mathfrak{a}\mathcal{O}_K] = n$ by Lemma 2.2(3). For
$\mathfrak{A} \subseteq \mathcal{O}_K$ of index $n$, the preimage of
$\mathfrak{A}/n\mathcal{O}_K$ under
$\mathcal{O}_d \to \mathcal{O}_K/n\mathcal{O}_K$ is
$\{x \in \mathcal{O}_d : x \in \mathfrak{A}\} = \mathfrak{A} \cap \mathcal{O}_d$ (using
$n\mathcal{O}_K \subseteq \mathfrak{A}$), so the inverse map is contraction. Mutual
inversion is Lemma 2.2(2) in one direction and $\varphi \circ \varphi^{-1} = \mathrm{id}$
in the other.

*Invertibility.* Let $\mathfrak{a} \subseteq \mathcal{O}_d$ have index $n$ coprime to
$f$, and let $\mathfrak{A} := \mathfrak{a}\mathcal{O}_K$, of index $n$. In the maximal
order, conjugation gives the standard identity
$$\mathfrak{A}\bar{\mathfrak{A}} = N(\mathfrak{A})\,\mathcal{O}_K = n\mathcal{O}_K$$
([Cox13, Lem. 7.14]; by multiplicativity of both sides in $\mathfrak{A}$ this reduces to
prime ideals, where it is checked case by case: $\mathfrak{p}\bar{\mathfrak{p}} =
p\mathcal{O}_K$ for $p$ split, $\mathfrak{p}\bar{\mathfrak{p}} = \mathfrak{p}^2 =
p^2\mathcal{O}_K$ for $p$ inert, $\mathfrak{p}\bar{\mathfrak{p}} = \mathfrak{p}^2 =
p\mathcal{O}_K$ for $p$ ramified). Now consider
$\mathfrak{c} := \mathfrak{a}\bar{\mathfrak{a}} \subseteq \mathcal{O}_d$. Conjugation is
a ring automorphism of $\mathcal{O}_d$, so $\bar{\mathfrak{a}}$ is an ideal of index $n$;
by Fact 0.4, $[\mathcal{O}_d : \mathfrak{c}]$ is finite and divides $n^3$, hence is
coprime to $f$. Lemma 2.2(2) therefore applies to $\mathfrak{c}$:
$$\mathfrak{a}\bar{\mathfrak{a}}
  = \bigl(\mathfrak{a}\bar{\mathfrak{a}}\,\mathcal{O}_K\bigr) \cap \mathcal{O}_d
  = \bigl(\mathfrak{A}\bar{\mathfrak{A}}\bigr) \cap \mathcal{O}_d
  = n\mathcal{O}_K \cap \mathcal{O}_d
  = n\mathcal{O}_d,$$
using $(\mathfrak{a}\bar{\mathfrak{a}})\mathcal{O}_K =
(\mathfrak{a}\mathcal{O}_K)(\bar{\mathfrak{a}}\mathcal{O}_K) =
\mathfrak{A}\bar{\mathfrak{A}}$ (extension is multiplicative and commutes with
conjugation) and Lemma 2.1(1) in the last step. Thus
$\mathfrak{a} \cdot \bigl(\tfrac{1}{n}\bar{\mathfrak{a}}\bigr) = \mathcal{O}_d$ and
$\mathfrak{a}$ is invertible.

*Counts.* The bijection gives $r_d(n) = r_D(n)$; invertibility of everything in sight
gives $r_d^{\times}(n) = r_d(n)$ and (Dedekind) $r_D^{\times}(n) = r_D(n)$.
$\blacksquare$

### Part 3: proof of Theorem 3

Fix $n \geq 1$ and write $m_p := v_p(n)$.

By Proposition 1,
$$r_d(n) = \prod_{p \mid n} r_d\!\left(p^{m_p}\right), \qquad
  r_d^{\times}(n) = \prod_{p \mid n} r_d^{\times}\!\left(p^{m_p}\right).$$

*Factors at $p \nmid f$.* Here $\gcd(p^{m_p}, f) = 1$, so Theorem 2 gives
$$r_d\!\left(p^{m_p}\right) = r_d^{\times}\!\left(p^{m_p}\right) = r_D\!\left(p^{m_p}\right),$$
and [prop-3-1-1] evaluates $r_D(p^{m})$ as $m+1$ ($p$ split), $\varepsilon(m)$ ($p$
inert: $1$ for $m$ even, $0$ for $m$ odd), and $1$ ($p$ ramified). This is
$t_p(m_p) = u_p(m_p)$ as defined.

*Factors at $p \mid f$.* The corrected Theorem 3.1.2 [thm-3-1-2] (statement as in ERRATA
E4, the $p$-uniform version) evaluates $r_d(p^{m})$ to $t_p(m)$, and the corrected
Corollary 3.1.3 [cor-3-1-3] (regime as in ERRATA E5) evaluates $r_d^{\times}(p^{m})$ to
$u_p(m)$.

*Exhaustiveness of the regimes at $p \mid f$.* For odd $p \mid f$: $v = v_p(D) + 2w$ with
$v_p(D) \in \{0, 1\}$ ($D$ fundamental is squarefree away from $2$), so
$v \in \{2w, 2w+1\}$. For $p = 2 \mid f$: $v = v_2(D) + 2w - 2$ with
$v_2(D) \in \{0, 2, 3\}$ ($D$ odd, or $D = 4k$ with $k \equiv 3 \pmod 4$, or $D = 4k$
with $k \equiv 2 \pmod 4$), so $v \in \{2w-2, 2w, 2w+1\}$, and $v = 2w-2$ iff $D$ is odd.
In particular $v = 2w - 1$ never occurs, so when $m = v$ exactly one of the side
conditions "$v = 2w-2$" and "$v \geq 2w$" holds, and $u_p$ is well defined on all of
$m \geq 0$.

*Trivial exponents.* If $m_p = 0$ the factor is $1$ in every case: for $p \nmid f$,
$t_p(0) = 1$ in all three splitting cases; for $p \mid f$, $m = 0 \leq v$ gives
$t_p(0) = (p^{1} - 1)/(p-1) = 1$, and $u_p(0) = 1$ (either $v > 0$, giving the trivial
branch $\varepsilon(0)p^0 = 1$, or $v = 0$, which forces $p = 2$, $D$ odd, $w = 1$, i.e.
$m = v = 2w - 2$, again the trivial branch). Hence the products may equally be taken over
all primes.

Substituting the factor evaluations into the two products completes the proof.
$\blacksquare$

## Remarks

**Remark 1 (divergence from the thesis).** The entire result is beyond the thesis, which
never states a count for composite norm; this document is the "CRT gluing + maximal-order
import" node of PLAN §5.2. Moreover the local factors at $p \mid f$ are the
**ERRATA-corrected** statements, *not* the thesis's: the thesis's Theorem 3.1.2 is false
in two of its five $2$-adic branches (ERRATA E1, E2, root cause E3; corrected $p$-uniform
statement E4), and the thesis's Corollary 3.1.3 assigns the boundary case
$m = v_p(d/4)$ incorrectly for $p = 2$ with $D$ odd and omits the hypothesis $m > 0$
(ERRATA E5). Also note ERRATA E6.1: the thesis's Corollary 3.1.3 display reads
$\#\{\mathfrak{a} \subseteq \mathcal{O} : [\mathcal{O} : \mathfrak{a}] = p^m\}$ —
typographically identical to Theorem 3.1.2's left-hand side — but counts *invertible*
ideals; our $r_d^{\times}$ vs. $r_d$ notation removes the ambiguity.

**Remark 2 (index is not multiplicative — why the glue uses CRT only).** For
non-invertible ideals of a non-maximal order, $[\mathcal{O} : \mathfrak{a}\mathfrak{b}] =
[\mathcal{O} : \mathfrak{a}][\mathcal{O} : \mathfrak{b}]$ **fails**. Example: $d = -12$
($D = -3$, $f = 2$), $\mathcal{O}_{-12} = \mathbb{Z}[\sqrt{-3}]$, and
$\mathfrak{p} = (2, 1 + \sqrt{-3})$ the unique prime above $2$: then
$[\mathcal{O} : \mathfrak{p}] = 2$ but
$\mathfrak{p}^2 = (4,\, 2 + 2\sqrt{-3},\, -2 + 2\sqrt{-3})$ has index $8$, not $4$
(as a lattice, $\mathfrak{p}^2 = \{x + y\sqrt{-3} : x \equiv y \equiv 0 \bmod 2,\;
x \equiv y \bmod 4\}$). This is exactly why Proposition 1 is proved via comaximal
CRT decomposition and never via norm multiplicativity of products — and why Mathlib's
bundled `Ideal.absNorm` multiplicative API (Dedekind-gated) cannot be used for
$\mathcal{O}_d$, $f > 1$ (PLAN §4, item 2). Multiplicativity *does* hold when at least
one factor is invertible, but the glue does not need this.

**Remark 3 (coprimality in Theorem 2 is necessary).** For $d = -12$, $n = 2$:
$r_{-12}(2) = 1$ (the ideal $\mathfrak{p}$ above; count confirmed by the corrected
Theorem 3.1.2 with $w = 1$, $v = 0 < m = 1$, $2$ inert in $\mathcal{O}_{-3}$,
$\varepsilon(1) = 0$: $(2^{1+0}-1)/(2-1) = 1$), while $r_{-3}(2) = 0$ ($2$ is inert in
$\mathbb{Q}(\sqrt{-3})$, and $m = 1$ is odd). So the correspondence genuinely breaks at
primes dividing the conductor — this failure is the whole subject of Theorem 3.1.2.

**Remark 4 (relation to the classical divisor sum).** For $\gcd(n, f) = 1$, Theorem 2
plus [prop-3-1-1] and multiplicativity give the classical formula
$$r_d(n) = \sum_{c \mid n} \chi_D(c),$$
with $\chi_D$ the Kronecker symbol extended totally multiplicatively: both sides are
multiplicative in $n$ (Proposition 1 for the left side), and at a prime power $p^m$ the
right side is $\sum_{j=0}^{m} \chi_D(p)^j = m+1$, $\varepsilon(m)$, or $1$ according as
$\chi_D(p) = 1, -1, 0$.

**Remark 5 (the intended Lean route).** Lemma 2.1 is a CRT-flavored, fully elementary
argument, well suited to direct formalization on the concrete
$\mathbb{Z}$-basis. It is also precisely where Mathlib's conductor machinery applies: the
conductor of $\mathcal{O}_d \subseteq \mathcal{O}_K$ contains $f\mathcal{O}_K$, and
Mathlib's `conductor`, `Localization.localRingHom_bijective_of_not_conductor_le`
(localization away from the conductor is an isomorphism), and
`comap_map_eq_map_adjoin_of_coprime_conductor` provide the localized form of
Lemmas 2.1–2.2; a per-prime localization proof of Theorem 2 is a viable alternative to
the mod-$N$ argument, at the cost of transporting index computations across
localizations. Similarly, the finite-module Sylow decomposition in Step 1.1 is
`AddCommGroup`-structure-theorem material; the $\mathcal{O}$-stability argument is one
line. Proposition 1 holds verbatim for any commutative ring in which the relevant ideals
have finite index — it is a candidate `ForMathlib/` lemma.

**Remark 6 (conventions).** $\varepsilon(m) = 1$ for $m$ *even* (thesis convention,
reversed from the natural indicator — ERRATA E6.6; the blueprint should prefer
`Even m` case splits in Lean). $v_p(d/4)$ abbreviates $v_p(d)$ for odd $p$ and
$v_2(d) - 2$ for $p = 2$ (ERRATA E6.8). The splitting trichotomy in all displayed
formulas refers to the maximal order $\mathcal{O}_K$; for $p \nmid f$ this agrees with
the behavior in $\mathcal{O}_d$ (thesis Remark 3.2.3), but that agreement is *not* used
here.

**Remark 7 (regression vectors).** The closed form of Theorem 3 reproduces every data
point in the ERRATA tables; e.g. $t_2(3) = 3$ and $t_2(4) = 7$ for $d = -48$;
$t_2(5) = 7$ for $d = -192$; $t_2(3) = 3$ for $d = -16$; $u_2(2) = 2$ for $d = -48$ and
$d = -112$; $u_2(4) = 4$ for $d = -192$; $u_3(2) = 2$ for $d = -72$; $u_3(2) = 4$ for
$d = -36$; $u_3(3) = 3$ for $d = -27$. Composite check: $r_{-12}(6) = t_2(1)\,t_3(1) =
1 \cdot 1 = 1$ (the ideal $\mathfrak{p} \cdot \sqrt{-3}\,\mathcal{O}$). These belong in
`Examples.lean` as `decide`/`#eval` guards.

## Lean correspondence

| Statement | Intended Lean declaration | File | Status |
|---|---|---|---|
| Proposition 1 (total counts) | `QuadraticOrder.idealCount_eq_prod_primeFactors` | `singular_moduli/QuadraticOrder/Glue.lean` | **new stub** — file does not exist yet (WORKPLAN WP-H) |
| Proposition 1 (invertible counts) | `QuadraticOrder.invertibleIdealCount_eq_prod_primeFactors` | `singular_moduli/QuadraticOrder/Glue.lean` | **new stub** — file does not exist yet |
| Theorem 2 | `QuadraticOrder.idealCount_eq_of_coprime_conductor` | `singular_moduli/QuadraticOrder/Glue.lean` | **new stub** — file does not exist yet |
| Theorem 3 | no dedicated declaration: obtained by rewriting `idealCount_eq_prod_primeFactors` / `invertibleIdealCount_eq_prod_primeFactors` with `idealCount_eq_of_coprime_conductor` and the closed forms of [prop-3-1-1], [thm-3-1-2], [cor-3-1-3] | — | derived |

Notes: in the PLAN §9 target layout the file is `SingularModuli/Counting/Glue.lean`; in
the current nested-project layout it is `singular_moduli/QuadraticOrder/Glue.lean`. The
counting functions themselves (`idealCount`, `invertibleIdealCount`, as `Nat.card` of the
relevant sets) are owned by the definitions layer ([notation] / `Defs/Counting.lean` per
WORKPLAN WP-0). None of the declarations above exist in the repository at the time of
writing; nothing here is verified in Lean.

## References

* C. Geiger, *Singular Moduli and the Ideal Class Group*, University of Washington, 2020:
  Question 3.0.1 and §3.1 (Prop 3.1.1, Thm 3.1.2, Cor 3.1.3 — the per-prime inputs);
  §2.4, Thm 2.4.2 and displays (2.4.1)–(2.4.2) (the consumer, $A(N)$); §3.4 (the research
  program this result instruments).
* `ERRATA.md` (repo root): E1–E4 (corrected Theorem 3.1.2, $p$-uniform), E5 (corrected
  Corollary 3.1.3 regime), E6.1/E6.6/E6.7/E6.8 (statement hygiene used here). The
  corrected statements are the ground truth targeted by this document.
* D. A. Cox, *Primes of the Form $x^2 + ny^2$*, 2nd ed., Wiley, 2013: §7A, Lemma 7.14
  ($\mathfrak{A}\bar{\mathfrak{A}} = N(\mathfrak{A})\mathcal{O}_K$); §7C (the
  prime-to-conductor ideal correspondence, Lemma 7.18 through Proposition 7.22 — our
  Theorem 2 is its integral-ideal, fixed-index form with a self-contained proof).
* K. Lauter, B. Viray, *On singular moduli for arbitrary discriminants* ([LV15b]):
  Thm 1.5 and Conj 1.7 (= thesis Thm 2.4.2, Conj 2.4.3) — the formulas the falsification
  loop tests candidate $A(N)$'s against.
* `PLAN.md` §5.2 (the `GLUE` node), §6; `WORKPLAN.md` WP-H (CRT glue work package),
  WP-L.
