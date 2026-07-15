# infra-index — The index layer: ideal index, finiteness, and multiplicativity

**Result class:** infrastructure (layer L0 of the formalization plan). This material is **not
stated in the thesis**; it is used silently throughout thesis §3.1–§3.3. Part (4) is the
unstated bridge lemma recorded as ERRATA E6.4(a). See the Remarks.

## Statement

> **Setting.** Let $d < 0$ be an integer with $d \equiv 0$ or $1 \pmod 4$ (the discriminant of
> an imaginary quadratic order). Let
> $$g(x) := x^2 - dx + \tfrac{d^2-d}{4} \in \mathbb Z[x], \qquad
> \mathcal O = \mathcal O_d := \mathbb Z[x]/(g(x)) = \mathbb Z[\tau], \qquad
> \tau := \tfrac{d+\sqrt d}{2},$$
> so that $\{1, \tau\}$ is a $\mathbb Z$-basis of $\mathcal O$ and $(\mathcal O, +) \cong \mathbb Z^2$.
> Write $d = Df^2$ with $D$ the fundamental discriminant of $K := \mathbb Q(\sqrt d)$ and
> $f \ge 1$ the conductor of $\mathcal O_d$; for a prime $p$ set $w := v_p(f)$, where $v_p$ is
> the $p$-adic valuation. Conjugation is $\overline{a + b\tau} := a + b\bar\tau$ with
> $\bar\tau := d - \tau$, and the norm is $N(\alpha) := \alpha\bar\alpha$, explicitly
> $N(a + b\tau) = a^2 + dab + \tfrac{d^2-d}{4}\,b^2 \in \mathbb Z$, a positive-definite form
> since its discriminant is $d < 0$. "Ideal" always means an ideal of the ring $\mathcal O$.
>
> **Definition (ideal index).** For an ideal $\mathfrak a \subseteq \mathcal O$, the *index*
> (= *norm*) of $\mathfrak a$ is
> $$[\mathcal O : \mathfrak a] := \#\bigl(\mathcal O/\mathfrak a\bigr) \in \mathbb Z_{\ge 0},$$
> the number of elements of the additive quotient group when it is finite, and $0$ when it is
> infinite (the `Nat.card` convention). Equivalently, it is the index of $\mathfrak a$ as an
> additive subgroup of $(\mathcal O, +)$. The thesis writes $N(\mathfrak a)$ for this quantity
> and says "$\mathfrak a$ has norm $p^m$" for $[\mathcal O : \mathfrak a] = p^m$.
>
> **(1) Finiteness** (`finite_setOf_idealIndex_eq`). For every integer $n \ge 1$, the set
> $$\{\mathfrak a \subseteq \mathcal O \text{ ideal} : [\mathcal O : \mathfrak a] = n\}$$
> is finite. (Moreover every nonzero ideal has finite, positive index, and
> $[\mathcal O : \mathfrak a] = 1$ iff $\mathfrak a = \mathcal O$.)
>
> **(2) Comaximal multiplicativity** (`idealIndex_mul_of_codisjoint`). If
> $I, J \subseteq \mathcal O$ are ideals with $I + J = \mathcal O$, then
> $$[\mathcal O : IJ] \;=\; [\mathcal O : I]\,\cdot\,[\mathcal O : J].$$
> **Warning:** without the comaximality hypothesis this is *false* in a non-maximal order —
> see Remark 2. It holds for arbitrary ideals of the *maximal* order, and (elsewhere in this
> development) for invertible ideals of $\mathcal O$; neither extension is used or proved here.
>
> **(3) Prime-power factorization of the count** (`idealCount_multiplicative`). Let $n \ge 1$
> and write $m_p := v_p(n)$. Then the map
> $$\mathfrak a \;\longmapsto\; \bigl(\mathfrak a + p^{m_p}\mathcal O\bigr)_{p \mid n}$$
> is a bijection
> $$\{\mathfrak a : [\mathcal O : \mathfrak a] = n\}
> \;\xrightarrow{\;\sim\;}\;
> \prod_{p \mid n} \{\mathfrak b : [\mathcal O : \mathfrak b] = p^{m_p}\},$$
> with inverse $(\mathfrak b_p)_p \mapsto \prod_p \mathfrak b_p = \bigcap_p \mathfrak b_p$.
> Consequently
> $$\#\{\mathfrak a : [\mathcal O : \mathfrak a] = n\}
> \;=\; \prod_{p \mid n} \#\{\mathfrak a : [\mathcal O : \mathfrak a] = p^{v_p(n)}\},$$
> and the counting function $r(n) := \#\{\mathfrak a : [\mathcal O:\mathfrak a] = n\}$ is
> multiplicative: $r(n_1 n_2) = r(n_1)\, r(n_2)$ whenever $\gcd(n_1, n_2) = 1$.
>
> **(4) Bridge lemma** (ERRATA E6.4(a); `isPrimary_of_idealIndex_prime_pow`). Suppose
> $p \mid f$. Then:
> * $g(x) \equiv (x - A)^2 \pmod p$ for some integer $A$, and $\mathcal O$ has a **unique**
>   prime ideal containing $p$, namely the maximal ideal
>   $\mathfrak P := p\mathcal O + (\tau - A)\mathcal O$, of index $p$;
> * every ideal $\mathfrak a$ with $[\mathcal O : \mathfrak a] = p^m$ for some $m \ge 1$ is
>   $\mathfrak P$-primary. (Recall: an ideal $\mathfrak q \subsetneq \mathcal O$ is *primary*
>   if $xy \in \mathfrak q$ implies $x \in \mathfrak q$ or $y \in \sqrt{\mathfrak q}$; it is
>   *$\mathfrak P$-primary* if moreover $\sqrt{\mathfrak q} = \mathfrak P$.)

## Role in the development

This is the foundation of the entire Chapter 3 counting layer (PLAN.md §4, gap-list items 2,
3, 5). Part (4) closes the gap between the statement of the corrected Theorem 3.1.2 — which
counts *all* ideals of index $p^m$ — and its proof, which enumerates *$\mathfrak P$-primary*
ideals through the normal form of Lemma 3.2.4; without (4) the enumeration would count a
priori only a subset. Part (3) reduces the count of ideals of arbitrary index $n$ to prime
powers, which is how Theorem 3.1.2, Corollary 3.1.3 and Proposition 3.1.1 are glued into a
count for general $n$ (the definition $A(N)$ of thesis (2.4.2) is stated at general $N$).
Part (2) also underwrites the norm identity
$N(\beta) = \prod_{\mathfrak q} [\mathcal O : \beta\mathcal O_{\mathfrak q} \cap \mathcal O]$
used inside the thesis proof of Lemma 3.2.2. It consumes only the order construction
(**notation**) and, for (4), the classification of primes over $p$ (**prop-3-2-1**).

## Proof

Throughout, $\pi_{\mathfrak a} : \mathcal O \to \mathcal O/\mathfrak a$ denotes the quotient
map; we drop the subscript when the ideal is clear.

### Lemma 0 (basic facts)

Let $\mathfrak a \subseteq \mathcal O$ be an ideal.

1. **(Free quotients of $\mathcal O$.)** For an integer $c \ge 1$,
   $[\mathcal O : c\mathcal O] = c^2$.
2. **(Nonzero ideals have finite index.)** If $\mathfrak a \ne 0$ then
   $[\mathcal O : \mathfrak a] \ge 1$ (i.e. the quotient is finite).
3. **(Lagrange.)** If $[\mathcal O : \mathfrak a] = n \ge 1$ then $n \in \mathfrak a$, hence
   $n\mathcal O \subseteq \mathfrak a$.
4. $[\mathcal O : \mathfrak a] = 1$ if and only if $\mathfrak a = \mathcal O$.

*Proof.* (1) In the $\mathbb Z$-basis $\{1, \tau\}$ we have
$\mathcal O/c\mathcal O \cong (\mathbb Z/c)^2$, of order $c^2$.

(2) Pick $\alpha \in \mathfrak a$, $\alpha \ne 0$. Then
$N(\alpha) = \alpha\bar\alpha \in \mathfrak a \cap \mathbb Z$ (it lies in $\mathfrak a$
because $\mathfrak a$ is an ideal and $N(\alpha) = \alpha \cdot \bar\alpha$ with the second
factor in $\mathcal O$), and $N(\alpha) > 0$ because the norm form is positive definite for
$d < 0$. With $c := N(\alpha)$ we get $c\mathcal O \subseteq \mathfrak a$, so
$\mathcal O/\mathfrak a$ is a quotient group of the finite group $\mathcal O/c\mathcal O$ and
is therefore finite (of order dividing $c^2$).

(3) The additive group $\mathcal O/\mathfrak a$ has order $n$, so by Lagrange's theorem
$n \cdot \bar 1 = \bar 0$, i.e. $n = n \cdot 1 \in \mathfrak a$; since $\mathfrak a$ is an
ideal, $n\mathcal O \subseteq \mathfrak a$.

(4) An additive subgroup has index $1$ iff it is the whole group. $\qquad\blacksquare$

### Proof of (1) — finiteness

Fix $n \ge 1$ and let $\mathfrak a$ be any ideal with $[\mathcal O : \mathfrak a] = n$. By
Lemma 0(3), $n\mathcal O \subseteq \mathfrak a \subseteq \mathcal O$. Consider the map
$$\mathfrak a \;\longmapsto\; \mathfrak a / n\mathcal O \subseteq \mathcal O / n\mathcal O.$$
It is injective on the set in question: since $n\mathcal O \subseteq \mathfrak a$, the ideal
is recovered as the preimage $\mathfrak a = \pi_{n\mathcal O}^{-1}(\mathfrak a/n\mathcal O)$.
The target is the set of subsets of $\mathcal O/n\mathcal O \cong (\mathbb Z/n)^2$
(Lemma 0(1)), a finite set of size $2^{\,n^2}$. Hence the set of ideals of index $n$ is
finite. $\qquad\blacksquare$

*Remark on the proof.* Only the fact that $(\mathcal O,+)$ is a finitely generated abelian
group is used; the statement holds for every $d$, with no domain hypothesis. Equivalently one
may argue that an ideal of index $n$ is in particular a sublattice of $\mathbb Z^2$ of index
$n$ containing $n\mathcal O$, and there are finitely many such sublattices — in fact exactly
$\sigma(n) = \sum_{t \mid n} t$ subgroups of $\mathbb Z^2$ of index $n$, by Hermite normal
form. The subset bound above is cruder but is the shortest path in Lean.

### Proof of (2) — comaximal multiplicativity

Assume $I + J = \mathcal O$.

**Step 1: $IJ = I \cap J$.** The inclusion $IJ \subseteq I \cap J$ holds for any two ideals.
Conversely, using comaximality,
$$I \cap J = (I \cap J)\,\mathcal O = (I \cap J)(I + J)
= (I \cap J)I + (I \cap J)J \subseteq JI + IJ = IJ.$$

**Step 2: Chinese Remainder.** The ring homomorphism
$$\varphi : \mathcal O \to \mathcal O/I \times \mathcal O/J, \qquad
x \mapsto (x \bmod I,\; x \bmod J)$$
has kernel $I \cap J$. It is surjective: write $1 = e + h$ with $e \in I$, $h \in J$; given a
target $(a \bmod I, \; b \bmod J)$, the element $x := ah + be$ satisfies
$x \equiv ah \equiv a(1 - e) \equiv a \pmod I$ and
$x \equiv be \equiv b(1 - h) \equiv b \pmod J$. By the first isomorphism theorem,
$$\mathcal O/(I \cap J) \;\cong\; \mathcal O/I \times \mathcal O/J .$$

**Step 3: count.** Combining Steps 1 and 2 and taking cardinalities,
$$[\mathcal O : IJ] = [\mathcal O : I \cap J]
= \#\bigl(\mathcal O/I \times \mathcal O/J\bigr)
= [\mathcal O : I]\,[\mathcal O : J].$$
With the `Nat.card` convention the last equality needs no finiteness hypothesis: the
cardinality of a product is the product of the cardinalities, where an infinite factor
against a nonempty factor yields an infinite (= $0$) product, and quotient rings are
nonempty. $\qquad\blacksquare$

Note that Steps 1–3 are valid in any commutative ring.

### Lemma 0′ (comaximal families)

Let $I_1, \dots, I_k \subseteq \mathcal O$ be pairwise comaximal ideals
($I_i + I_j = \mathcal O$ for $i \ne j$). Then:

1. $I_1 \cdots I_k = I_1 \cap \dots \cap I_k$;
2. the natural map
   $\mathcal O/(I_1 \cdots I_k) \to \prod_{j=1}^{k} \mathcal O/I_j$ is a ring isomorphism;
3. $[\mathcal O : I_1 \cdots I_k] = \prod_{j=1}^{k} [\mathcal O : I_j]$.

*Proof.* First, a standard sub-claim: if $I + J_1 = \mathcal O$ and $I + J_2 = \mathcal O$
then $I + J_1 J_2 = \mathcal O$. Indeed
$$\mathcal O = \mathcal O \cdot \mathcal O = (I + J_1)(I + J_2)
= I^2 + I J_2 + J_1 I + J_1 J_2 \subseteq I + J_1 J_2 .$$
Now induct on $k$; the case $k = 1$ is trivial. For the step, put
$P := I_1 \cdots I_{k-1}$. By the sub-claim iterated, $I_k + P = \mathcal O$. Then item (1)
follows from Step 1 of (2) applied to $(P, I_k)$ together with the inductive hypothesis;
item (2) follows from Step 2 of (2) applied to $(P, I_k)$ composed with the inductive
isomorphism for $P$; and item (3) follows from item (2) by taking cardinalities (or from (2)
by the same induction). $\qquad\blacksquare$

### Proof of (3) — factorization of the count

Fix $n \ge 1$, let $P(n) := \{p \text{ prime} : p \mid n\}$ and $m_p := v_p(n) \ge 1$ for
$p \in P(n)$, so $n = \prod_{p \in P(n)} p^{m_p}$. If $n = 1$ both sides of the bijection are
singletons ($\{\mathcal O\}$ on the left by Lemma 0(4), the empty product on the right), so
assume $n > 1$.

**Preliminaries on the quotient module.** Let $\mathfrak a$ be an ideal with
$[\mathcal O : \mathfrak a] = n$ and set $M := \mathcal O/\mathfrak a$, a finite abelian group
of order $n$ carrying an $\mathcal O$-module structure (it is the quotient ring). For
$p \in P(n)$ define the *$p$-primary component*
$$M_p := \{x \in M : p^j x = 0 \text{ for some } j \ge 0\}.$$
Each $M_p$ is an $\mathcal O$-submodule: it is clearly an additive subgroup, and for
$r \in \mathcal O$, $x \in M_p$ we have $p^j (r x) = r(p^j x) = 0$.

**Fact A (primary decomposition of $M$).** $M = \bigoplus_{p \in P(n)} M_p$ and
$\#M_p = p^{m_p}$.

*Proof.* For $p \in P(n)$ write $n = p^{m_p} n_p'$ with $p \nmid n_p'$. The family
$\{n_p'\}_{p \in P(n)}$ has no common prime divisor: a prime $q \notin P(n)$ divides no
$n_p'$ (as $n_p' \mid n$), and a prime $q \in P(n)$ does not divide $n_q'$. Hence
$\gcd_p(n_p') = 1$ and there are integers $c_p$ with $\sum_p c_p n_p' = 1$. For $x \in M$,
$$x = \sum_{p} c_p\, (n_p' x), \qquad p^{m_p}(n_p' x) = n x = 0$$
(Lagrange: $n = \#M$ annihilates $M$), so $n_p' x \in M_p$ and $M = \sum_p M_p$. For
directness, suppose $x \in M_p \cap \sum_{q \ne p} M_q$. Every element of $M_q$ has
$q$-power order (definition of $M_q$) dividing $n$ (Lagrange), hence order dividing
$q^{m_q}$, and $q^{m_q} \mid n_p'$ for $q \ne p$; so $\sum_{q \ne p} M_q$ is
killed by $n_p'$, while $M_p$ is killed by some $p^{j}$; choosing $u, v$ with
$u p^{j} + v n_p' = 1$ gives $x = u p^{j} x + v n_p' x = 0$. So the sum is direct. Finally,
every prime divisor of $\#M_p$ equals $p$ (by Cauchy's theorem for finite abelian groups, a
prime $q \mid \#M_p$ forces an element of order $q$ in $M_p$, and all orders in $M_p$ are
powers of $p$); since $n = \#M = \prod_p \#M_p$, unique factorization forces
$\#M_p = p^{m_p}$. $\square$

**Fact B (multiplication by $p^{m_p}$).** On $M_p$, multiplication by $p^{m_p}$ is zero; on
$M_q$ with $q \ne p$, it is bijective. Consequently
$$p^{m_p} M = \bigoplus_{q \ne p} M_q, \qquad M / p^{m_p} M \cong M_p .$$

*Proof.* $\#M_p = p^{m_p}$ annihilates $M_p$ by Lagrange. On $M_q$: if
$p^{m_p} x = 0$ with $x \in M_q$, then the order of $x$ divides both $p^{m_p}$ and the
$q$-power $\#M_q$, hence is $1$; so multiplication by $p^{m_p}$ is injective on the finite
group $M_q$, hence bijective. The displayed identities follow by applying multiplication by
$p^{m_p}$ summand-wise in Fact A. $\square$

Now define, for $p \in P(n)$, the *$p$-part*
$$\mathfrak a_p := \mathfrak a + p^{m_p}\mathcal O .$$

**(i) Index of the parts.** The image of $\mathfrak a_p$ in $M = \mathcal O/\mathfrak a$ is
$p^{m_p} M$, and $\mathfrak a \subseteq \mathfrak a_p$, so
$\mathcal O/\mathfrak a_p \cong M / p^{m_p} M \cong M_p$ (Fact B), whence
$[\mathcal O : \mathfrak a_p] = p^{m_p}$.

**(ii) Pairwise comaximality.** For $p \ne q$ in $P(n)$, the integers $p^{m_p}$ and
$q^{m_q}$ are coprime, so $u p^{m_p} + v q^{m_q} = 1$ for some $u, v \in \mathbb Z$, and
$1 \in \mathfrak a_p + \mathfrak a_q$.

**(iii) The parts recover $\mathfrak a$ (injectivity).** By Fact B,
$\mathfrak a_p = \pi^{-1}(p^{m_p} M) = \pi^{-1}\bigl(\bigoplus_{q \ne p} M_q\bigr)$. An
element of $\bigcap_{p \in P(n)} \bigoplus_{q \ne p} M_q$ has all of its components (in the
decomposition of Fact A) equal to zero, so the intersection is $0$ and
$$\bigcap_{p \in P(n)} \mathfrak a_p = \pi^{-1}(0) = \mathfrak a .$$
In particular, $\mathfrak a \mapsto (\mathfrak a_p)_p$ is injective. By (ii) and
Lemma 0′(1), also $\prod_p \mathfrak a_p = \bigcap_p \mathfrak a_p = \mathfrak a$.

**(iv) Surjectivity and the inverse map.** Let $(\mathfrak b_p)_{p \in P(n)}$ be given with
$[\mathcal O : \mathfrak b_p] = p^{m_p}$. By Lemma 0(3), $p^{m_p} \in \mathfrak b_p$; as in
(ii), the $\mathfrak b_p$ are pairwise comaximal. Set
$\mathfrak a := \bigcap_p \mathfrak b_p = \prod_p \mathfrak b_p$ (Lemma 0′(1)). By
Lemma 0′(3),
$$[\mathcal O : \mathfrak a] = \prod_{p} [\mathcal O : \mathfrak b_p]
= \prod_p p^{m_p} = n .$$
It remains to check that the parts of $\mathfrak a$ are the $\mathfrak b_p$, i.e.
$\mathfrak a + p^{m_p}\mathcal O = \mathfrak b_p$. Let
$$\psi : \mathcal O/\mathfrak a \xrightarrow{\ \sim\ } \prod_{q \in P(n)} \mathcal O/\mathfrak b_q$$
be the isomorphism of Lemma 0′(2), induced by $x \mapsto (x \bmod \mathfrak b_q)_q$.

*The image of $\mathfrak b_p/\mathfrak a$ under $\psi$ is
$H_p := 0 \times \prod_{q \ne p} \mathcal O/\mathfrak b_q$.* Indeed, for $x \in \mathcal O$,
the $p$-component of $\psi(x + \mathfrak a)$ vanishes iff $x \in \mathfrak b_p$; this gives
$\psi(\mathfrak b_p/\mathfrak a) \subseteq H_p$, and conversely any $t \in H_p$ is
$\psi(x + \mathfrak a)$ for some $x$ by surjectivity of $\psi$, and then $x \in \mathfrak b_p$
because $t_p = 0$.

*The image of $p^{m_p}(\mathcal O/\mathfrak a)$ under $\psi$ is also $H_p$.* Multiplication
by $p^{m_p}$ acts componentwise on the product; it kills $\mathcal O/\mathfrak b_p$ (a group
of order $p^{m_p}$, Lagrange) and is bijective on each $\mathcal O/\mathfrak b_q$, $q \ne p$
(kernel elements have order dividing both $p^{m_p}$ and $q^{m_q}$, hence trivial; injective
on a finite group implies bijective). So
$p^{m_p} \prod_q \mathcal O/\mathfrak b_q = H_p$, and $\psi$ is $\mathcal O$-linear.

Therefore $p^{m_p}(\mathcal O/\mathfrak a) = \mathfrak b_p/\mathfrak a$ as subgroups of
$\mathcal O/\mathfrak a$; taking preimages under $\pi_{\mathfrak a}$ (both sides contain
$\mathfrak a$),
$$\mathfrak a + p^{m_p}\mathcal O = \mathfrak b_p ,$$
as required. Hence the map of (3) is surjective with the stated inverse.

**(v) Conclusion.** The two sides of the bijection are finite sets by (1), so
$$\#\{\mathfrak a : [\mathcal O:\mathfrak a] = n\}
= \prod_{p \mid n} \#\{\mathfrak b : [\mathcal O:\mathfrak b] = p^{m_p}\} .$$
For the multiplicativity of $r$: if $\gcd(n_1, n_2) = 1$ then every prime divisor of
$n_1 n_2$ divides exactly one of $n_1, n_2$, and $v_p(n_1 n_2)$ equals the corresponding
$v_p(n_i)$; grouping the factors of the product formula for $n_1 n_2$ accordingly gives
$r(n_1 n_2) = r(n_1) r(n_2)$. Finally, for $p \nmid n$ the factor
$\#\{\mathfrak b : [\mathcal O : \mathfrak b] = p^0 = 1\} = \#\{\mathcal O\} = 1$
(Lemma 0(4)), so the product may equivalently be extended over all primes.
$\qquad\blacksquare$

### Proof of (4) — the bridge lemma

Assume $p \mid f$, and recall $w = v_p(f) \ge 1$.

**Step 1: $g \bmod p$ is the square of a linear polynomial.** The discriminant of $g$ is
$d^2 - 4 \cdot \tfrac{d^2 - d}{4} = d = Df^2$.

* If $p$ is odd: $p \mid f$ gives $v_p(d) = v_p(D) + 2w \ge 2$, in particular $p \mid d$.
  Since $2$ is invertible mod $p$, completing the square gives, in $\mathbb F_p[x]$,
  $$g(x) = \Bigl(x - \tfrac d2\Bigr)^2 - \tfrac d4 \equiv \Bigl(x - \tfrac d2\Bigr)^2 \pmod p,$$
  where $\tfrac d2, \tfrac d4$ denote $d \cdot 2^{-1}, d \cdot 4^{-1}$ in $\mathbb F_p$ and
  the constant term vanishes because $p \mid d$. Take $A$ any integer lift of
  $d \cdot 2^{-1} \bmod p$.
* If $p = 2$: $2 \mid f$ gives $v_2(d) = v_2(D) + 2w \ge 2$, so $4 \mid d$ and the linear
  coefficient $-d$ of $g$ is even. Hence in $\mathbb F_2[x]$, with
  $c := \tfrac{d^2-d}{4} \bmod 2$,
  $$g(x) \equiv x^2 + c = (x + c)^2 \pmod 2$$
  (using $c^2 = c$ in $\mathbb F_2$). Take $A := -c \equiv c \pmod 2$.

In both cases $g(x) \equiv (x - A)^2 \pmod p$, so $g \bmod p$ has the single monic
irreducible factor $x - A$.

**Step 2: unique prime over $p$, and it is maximal of index $p$.** By Proposition 3.2.1
(label **prop-3-2-1**: the prime ideals of $\mathcal O = \mathbb Z[x]/(g)$ containing $p$ are
exactly $p\mathcal O + (g_i(\tau))$ for $g_i$ running over the monic irreducible factors of
$g \bmod p$, with $g_i$ any lift), Step 1 gives that the *only* prime of $\mathcal O$
containing $p$ is
$$\mathfrak P := p\mathcal O + (\tau - A)\mathcal O .$$
Moreover
$$\mathcal O/\mathfrak P \cong \mathbb F_p[x]\big/\bigl(g \bmod p,\; x - A\bigr)
= \mathbb F_p[x]/(x - A) \cong \mathbb F_p$$
(the middle equality because $g \equiv (x-A)^2 \in (x - A)$), so $\mathfrak P$ is maximal and
$[\mathcal O : \mathfrak P] = p$.

**Step 3: radical computation.** Let $\mathfrak a$ be an ideal with
$[\mathcal O : \mathfrak a] = p^m$, $m \ge 1$. Since $p^m > 1$, $\mathfrak a$ is proper. By
Lemma 0(3), $p^m \in \mathfrak a$. Let $\mathfrak q$ be any prime ideal with
$\mathfrak q \supseteq \mathfrak a$. Then $p^m \in \mathfrak q$, so $p \in \mathfrak q$
(primality), and by Step 2, $\mathfrak q = \mathfrak P$. The set of primes containing
$\mathfrak a$ is nonempty ($\mathfrak a$ is proper and $\mathcal O$ is Noetherian — a
finitely generated $\mathbb Z$-module — so $\mathfrak a$ lies in some maximal ideal). Since
the radical of an ideal is the intersection of the primes containing it
[AM, Prop. 1.14],
$$\sqrt{\mathfrak a} = \bigcap_{\mathfrak q \supseteq \mathfrak a \text{ prime}} \mathfrak q
= \mathfrak P .$$

**Step 4: maximal radical implies primary.** Suppose $xy \in \mathfrak a$ and
$y \notin \sqrt{\mathfrak a}$; we must show $x \in \mathfrak a$. Pass to
$R := \mathcal O/\mathfrak a$. Its nilradical is
$\sqrt{\mathfrak a}/\mathfrak a = \mathfrak P/\mathfrak a$. Every maximal ideal of $R$
contains the nilradical; but the nilradical $\mathfrak P/\mathfrak a$ is itself maximal
(Step 2), so it is the *unique* maximal ideal of $R$ and $R$ is local with maximal ideal
$\mathfrak P/\mathfrak a$. Now $\bar y \notin \mathfrak P/\mathfrak a$, so $\bar y$ is a unit
of $R$; from $\bar x \bar y = 0$ we get $\bar x = 0$, i.e. $x \in \mathfrak a$. Hence
$\mathfrak a$ is primary, and by Step 3 its radical is $\mathfrak P$: $\mathfrak a$ is
$\mathfrak P$-primary. (This is the standard fact that an ideal whose radical is maximal is
primary [AM, Prop. 4.2]; in Mathlib, `Ideal.isPrimary_of_isMaximal_radical`.)
$\qquad\blacksquare$

## Remarks

**Remark 1 (Divergence from the thesis).** None of (1)–(4) is stated in the thesis; all are
used silently:

* The proof of Theorem 3.1.2 (§3.3) opens by counting ideals via the normal form of
  Lemma 3.2.4, which applies to *$\mathfrak P$-primary* ideals of index $p^m$, whereas the
  theorem's left-hand side is $\#\{\mathfrak a \subseteq \mathcal O : [\mathcal O : \mathfrak a] = p^m\}$,
  over *all* ideals. Part (4) — recorded as ERRATA E6.4(a), "every ideal of index $p^m$ is
  automatically $p$-primary when $p \mid f$" — is exactly the missing bridge. (ERRATA
  E6.4(b), the minimality/no-double-counting bridge for Lemma 3.2.4's converse, belongs to
  the Lemma 3.2.4 document, not here.)
* The proof of Lemma 3.2.2 (§3.2) uses the display
  $\beta\bar\beta = N(\beta) = \prod_{\mathfrak q} [\mathcal O : \beta\mathcal O_{\mathfrak q} \cap \mathcal O]$,
  which presupposes a comaximal (primary) decomposition of $\beta\mathcal O$ and the
  multiplicativity (2) of the index over it.
* The reduction of counting ideals of arbitrary index to prime-power index — needed to wire
  Chapter 3 into $A(N)$ of thesis (2.4.2) and Theorem 2.4.2 — is part (3).

**Remark 2 (WARNING: unrestricted multiplicativity is false; why Mathlib's `Ideal.absNorm`
cannot be used).** For non-invertible ideals of a non-maximal order, the index is **not**
multiplicative. Counterexample: $d = -12$ ($D = -3$, $f = 2$), where
$\mathcal O_{-12} = \mathbb Z[\sqrt{-3}]$ (indeed $\tau = -6 + \sqrt{-3}$). Take the unique
prime over $2$,
$$\mathfrak P = \bigl(2,\ 1 + \sqrt{-3}\bigr), \qquad [\mathcal O : \mathfrak P] = 2 .$$
Since $(1 + \sqrt{-3})^2 = -2 + 2\sqrt{-3} = 2(1 + \sqrt{-3}) - 4$, one computes
$$\mathfrak P^2 = \bigl(4,\ 2 + 2\sqrt{-3}\bigr) = 2\,\mathfrak P,$$
and hence, by the tower formula
$[\mathcal O : 2\mathfrak P] = [\mathcal O : 2\mathcal O]\,[2\mathcal O : 2\mathfrak P]$
with $[2\mathcal O : 2\mathfrak P] = [\mathcal O : \mathfrak P]$ (multiplication by $2$ is
injective),
$$[\mathcal O : \mathfrak P^2] = 4 \cdot 2 = 8 \;\ne\; 4 = [\mathcal O : \mathfrak P]^2 .$$
(Directly: $\mathfrak P^2 = 2\mathfrak P$ has $\mathbb Z$-basis $\{4,\, 2 + 2\sqrt{-3}\}$,
of index $8$; verified by explicit lattice enumeration.) The identity
$\mathfrak P^2 = 2\mathfrak P$ with $\mathfrak P \neq 2\mathcal O$ also witnesses that
$\mathfrak P$ is not invertible.

Consequently Mathlib's bundled ideal-norm API is unusable here *for mathematical reasons,
not engineering ones*: `Ideal.absNorm : Ideal S →*₀ ℕ` is packaged as a monoid-with-zero
homomorphism — multiplicativity is baked into the type — and its construction goes through
`Submodule.cardQuot_mul`, which carries an `[IsDedekindDomain S]` hypothesis. For $f > 1$
the order $\mathcal O_d$ is not integrally closed (its integral closure is
$\mathcal O_K \supsetneq \mathcal O_d$), hence not a Dedekind domain, and — as the
counterexample shows — no multiplicative extension of the index to all ideals exists. The
index layer must therefore be built directly on the raw quotient-cardinality
(`Submodule.cardQuot` / `AddSubgroup.index` / `Nat.card`), with multiplicativity available
only in the comaximal form (2) (and, elsewhere in this development, for invertible ideals).

**Remark 3 (terminology: "$p$-parts" are not always primary ideals).** The decomposition in
(3) is a *Sylow-style coprime decomposition*, not Lasker–Noether primary decomposition: the
$p$-part $\mathfrak a + p^{v_p(n)}\mathcal O$ has $p$-power index but need **not** be a
primary ideal. Example: if $p \nmid f$ splits in $\mathcal O$, say
$p\mathcal O = \mathfrak p_1 \mathfrak p_2$ with $\mathfrak p_1 \neq \mathfrak p_2$, the
ideal $\mathfrak a = \mathfrak p_1\mathfrak p_2$ has index $p^2$ and radical
$\mathfrak p_1 \cap \mathfrak p_2$, which is not prime, so $\mathfrak a$ is not primary.
Part (4) says precisely that at primes $p \mid f$ — where there is a unique prime
$\mathfrak P$ over $p$ — this distinction disappears: $p$-power index *does* imply
$\mathfrak P$-primary. We therefore say "$p$-part" rather than "$p$-primary part" in (3),
diverging from the informal usage in the planning documents.

**Remark 4 (conventions and degenerate cases).** With the `Nat.card` convention
($\#X = 0$ for $X$ infinite): $[\mathcal O : 0] = 0$ (for $d < 0$, $\mathcal O$ is
infinite), and by Lemma 0(2) the zero ideal is the *only* ideal of "index $0$"; statements
(1)–(3) are made for $n \ge 1$ and never touch it. In (2), no finiteness hypothesis is
needed. In (3), $n = 1$ gives the empty product and the singleton $\{\mathcal O\}$ on both
sides.

**Remark 5 (generality and upstreamability).** (2) holds in any commutative ring, verbatim.
(3) and its proof also hold in any commutative ring (the argument uses only Lagrange and
CRT, never the specific ring $\mathcal O$). (1) holds for any ring whose additive group is a
finitely generated abelian group. Only (4) is specific to the quadratic-order setting (via
Proposition 3.2.1). Parts (1)–(3) are `ForMathlib/` candidates.

## Lean correspondence

The definition `idealIndex` already exists as final API (WP-0 statement freeze) in
`QuadraticOrder/Defs/Counting.lean`; the four theorems are stated in
`QuadraticOrder/Index/Basic.lean` and `QuadraticOrder/Index/Primary.lean` in the
`singular_moduli` Lake project and were proved in WP-A without changing their frozen
statements. Names are relative to the `QuadraticOrder` namespace.

| Statement | Lean declaration | File | Status |
|---|---|---|---|
| Definition: $[\mathcal O : \mathfrak a]$ as `Nat.card` of the quotient | `QuadraticOrder.idealIndex` | `QuadraticOrder/Defs/Counting.lean` | defined (WP-0 statement freeze) |
| (1) finiteness of $\{\mathfrak a : [\mathcal O:\mathfrak a] = n\}$, $n \ge 1$ | `QuadraticOrder.finite_setOf_idealIndex_eq` | `QuadraticOrder/Index/Basic.lean` | **Proved** (WP-A; sorry-free). |
| (2) $I + J = \mathcal O \Rightarrow [\mathcal O : IJ] = [\mathcal O:I][\mathcal O:J]$ | `QuadraticOrder.idealIndex_mul_of_codisjoint` | `QuadraticOrder/Index/Basic.lean` | **Proved** (WP-A; sorry-free). |
| (3) $\#\{[\mathcal O:\mathfrak a] = n\} = \prod_p \#\{[\mathcal O:\mathfrak a] = p^{v_p(n)}\}$ (the frozen Lean statement is the equivalent coprime-multiplicativity form `idealCount d (m*n) = idealCount d m * idealCount d n` for coprime `m, n ≥ 1`) | `QuadraticOrder.idealCount_multiplicative` | `QuadraticOrder/Index/Basic.lean` | **Proved** (WP-A; sorry-free). |
| (4) $p \mid f$, $[\mathcal O : \mathfrak a] = p^m$, $m \ge 1$ $\Rightarrow$ $\mathfrak a$ is $\mathfrak P$-primary | `QuadraticOrder.isPrimary_of_idealIndex_prime_pow` | `QuadraticOrder/Index/Primary.lean` | **Proved** (WP-A; sorry-free). |

Implementation notes. `idealIndex` is `Nat.card` of the quotient ring (equal to
`Submodule.cardQuot` and to `AddSubgroup.index` of the coerced additive subgroup), **not**
`Ideal.absNorm` (Remark 2). The frozen Lean statement of (2) phrases comaximality as the
hypothesis `I ⊔ J = ⊤`. The frozen Lean statement of (4) carries the standing hypotheses
as the bundled instance `[ConductorPrimeSetup d D f p]` and concludes `Ideal.IsPrimary I`;
the formal proof first uses `QuadraticOrder.existsUnique_isPrime_mem_of_dvd_conductor`
(`QuadraticOrder/Prime/ConductorPrime.lean`, blueprint node `prop-3-2-1-unique-prime`) to
show that every prime above $\mathfrak a$ equals $\mathfrak P$, and hence identifies
$\sqrt{\mathfrak a}=\mathfrak P$ before applying the primary-ideal criterion.
Useful Mathlib ingredients:
`Ideal.quotientInfEquivQuotientProd` (CRT), `Ideal.mul_eq_inf_of_coprime` (Step 1 of the
proof of (2)), `Nat.card_prod`, `Nat.card_congr`, `Ideal.isPrimary_of_isMaximal_radical` and
`Ideal.radical_eq_sInf` for (4), and `Submodule.smithNormalFormOfLE` as an alternative route
to (1). Lemma 0 and Lemma 0′ will appear as unbundled private helper lemmas; the auxiliary
facts A/B in the proof of (3) correspond to the primary (Sylow) decomposition of a finite
module, for which Mathlib has torsion-submodule machinery
(`Module.IsTorsionBySet`, `Submodule.torsionBy`; also `AddCommGroup.torsion` piecewise) —
the Lean proof may instead follow the equivalent product-ring route
(ideals of $\mathcal O/n\mathcal O \cong \prod_p \mathcal O/p^{m_p}\mathcal O$ are products
of ideals), which avoids Fact A entirely; both are faithful to the proof above, which only
needs Facts A/B for the quotient by each individual ideal.

## References

* C. Geiger, *Singular Moduli and the Ideal Class Group*, UW 2020: §1.2 (notation
  $\mathcal O_d = \mathbb Z[\tau]$, conductor, $d = Df^2$); §3.1 (the counting statements
  whose left-hand sides are $\#\{\mathfrak a : [\mathcal O:\mathfrak a] = p^m\}$); §3.2,
  Proposition 3.2.1 and Lemma 3.2.2 (silent use of (2)); §3.3, opening of the proof of
  Theorem 3.1.2 (silent use of (4)).
* `ERRATA.md` (this repository), item E6.4(a) — the bridge lemma (4); E6.8 for the
  $v_p(d/4)$ bookkeeping conventions used downstream.
* `PLAN.md` (this repository), §4 items 2–3 and 5 (the index layer and bridge lemmas), §3.1
  (verification that Mathlib's `Ideal.absNorm` multiplicative API is Dedekind-gated).
* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*: Prop. 1.10 (CRT),
  Prop. 1.14 (radical = intersection of primes), Prop. 4.2 (maximal radical ⟹ primary).
* D. A. Cox, *Primes of the Form $x^2 + ny^2$*, §7 (orders in imaginary quadratic fields,
  conductor, index/norm of ideals).
