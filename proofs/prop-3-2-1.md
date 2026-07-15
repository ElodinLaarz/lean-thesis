# Proposition 3.2.1 + Remark 3.2.3 — Primes of $\mathbb{Z}[\tau]$ above $p$, and the split criterion

## Setting and notation

Throughout, $d$ is an integer with $d \equiv 0$ or $1 \pmod 4$ (a *quadratic discriminant*), and $d$ is not a perfect square. In the thesis $d < 0$ (imaginary quadratic), but negativity is used nowhere in this document (see Remark R4). Write

$$d = D f^2,$$

where $D$ is the **fundamental discriminant** of the quadratic field $K = \mathbb{Q}(\sqrt d\,)$ — i.e. $D = \operatorname{disc}(K)$; equivalently either $D \equiv 1 \pmod 4$ and $D$ is squarefree, or $D = 4m$ with $m \equiv 2, 3 \pmod 4$ squarefree — and $f \geq 1$ is the **conductor** of $d$. Set

$$\tau = \tau_d := \frac{d + \sqrt d}{2}, \qquad g(X) = g_d(X) := X^2 - dX + \frac{d^2 - d}{4} \in \mathbb{Z}[X].$$

Since $d \equiv 0, 1 \pmod 4$ we have $4 \mid d^2 - d$, so $g$ has integer coefficients; $g$ is the minimal polynomial of $\tau$ over $\mathbb{Q}$ (Vieta: $\tau + \bar\tau = d$ and $\tau\bar\tau = (d^2-d)/4$, where $\bar\tau = (d - \sqrt d)/2$). The **order of discriminant $d$** is

$$\mathcal{O} = \mathcal{O}_d := \mathbb{Z}[\tau] = \mathbb{Z} \oplus \mathbb{Z}\tau \;\cong\; \mathbb{Z}[X]/(g(X)),$$

where the isomorphism $\mathbb{Z}[X]/(g) \to \mathbb{Z}[\tau]$ sends $X \mapsto \tau$: the evaluation map is surjective with kernel containing $(g)$, and since $g$ is monic of degree $2$ the ring $\mathbb{Z}[X]/(g)$ is free of rank $2$ over $\mathbb{Z}$ on the images of $1, X$, which map to the $\mathbb{Z}$-linearly independent elements $1, \tau$ (linear independence uses that $d$ is not a square, so $\sqrt d \notin \mathbb{Q}$). The maximal order of $K$ is $\mathcal{O}_K = \mathcal{O}_D = \mathbb{Z}[\tau_D]$, and $\mathcal{O}_d = \mathbb{Z} + f\mathcal{O}_K$.

For an ideal $\mathfrak{a} \subseteq \mathcal{O}$ of finite index, $[\mathcal{O} : \mathfrak{a}]$ denotes the index of $\mathfrak{a}$ as a subgroup of $(\mathcal{O}, +)$ (the *norm* of $\mathfrak{a}$). We write $w := v_p(f)$ for the $p$-adic valuation of the conductor; in this document only $w \geq 1$ (i.e. $p \mid f$) plays a role. The letter $p$ always denotes a rational prime, $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$, and $\bar g \in \mathbb{F}_p[X]$ is the reduction of $g$ modulo $p$ (reduce each coefficient). For odd $p$, $\left(\tfrac{d}{p}\right) \in \{-1, 0, 1\}$ is the Legendre symbol.

Because $\mathcal{O}$ is not Dedekind when $f > 1$, "splitting behaviour of $p$" must be *defined* rather than read off a factorization $p\mathcal{O} = \prod \mathfrak{p}_i^{e_i}$ (which need not exist). We use the ideal-theoretic definition below; Theorem 4 shows it agrees with the classical one when it applies (in particular in $\mathcal{O}_K$).

## Statement

> **Definition 1 (splitting type).** Let $p$ be a rational prime and $\mathcal{O} = \mathcal{O}_d$. We say
>
> * $p$ is **inert** in $\mathcal{O}$ if $p\mathcal{O}$ is a maximal ideal of $\mathcal{O}$;
> * $p$ is **split** in $\mathcal{O}$ if $p\mathcal{O}$ is a radical ideal of $\mathcal{O}$ but not maximal;
> * $p$ is **ramified** in $\mathcal{O}$ if $p\mathcal{O}$ is not a radical ideal of $\mathcal{O}$.
>
> Since maximal ideals are radical, exactly one of the three alternatives holds for each $p$.

> **Lemma 2 (quotient presentation).** For every rational prime $p$ there is a ring isomorphism
> $$\Phi \colon \mathcal{O}/p\mathcal{O} \;\xrightarrow{\;\sim\;}\; \mathbb{F}_p[X]/(\bar g), \qquad \Phi(\tau \bmod p\mathcal{O}) = X \bmod (\bar g), \quad \Phi(n \bmod p\mathcal{O}) = \bar n \ \ (n \in \mathbb{Z}).$$

> **Proposition 3 (thesis Prop 3.2.1).** Let $p$ be a rational prime and let $\bar g = \prod_{i=1}^{r} \bar g_i^{\,e_i}$ be the factorization of $\bar g$ into powers of pairwise distinct monic irreducible polynomials $\bar g_i \in \mathbb{F}_p[X]$. For each $i$ choose a lift $g_i \in \mathbb{Z}[X]$ of $\bar g_i$. Then the prime ideals of $\mathcal{O}$ containing $p$ are exactly
> $$\mathfrak{p}_i = p\mathcal{O} + g_i(\tau)\,\mathcal{O}, \qquad i = 1, \dots, r,$$
> and these are pairwise distinct, independent of the choice of lifts, and all maximal, with residue fields $\mathcal{O}/\mathfrak{p}_i \cong \mathbb{F}_p[X]/(\bar g_i) \cong \mathbb{F}_{p^{\deg \bar g_i}}$. In particular the number of primes of $\mathcal{O}$ above $p$ equals the number $r \in \{1, 2\}$ of distinct monic irreducible factors of $\bar g$.

> **Theorem 4 (trichotomy).** Let $p$ be a rational prime. Exactly one of the following three cases holds, and within each row all listed conditions are equivalent:
>
> 1. **(inert)** $\bar g$ is irreducible in $\mathbb{F}_p[X]$ $\iff$ $p\mathcal{O}$ is maximal. Then $\mathcal{O}/p\mathcal{O} \cong \mathbb{F}_{p^2}$, and $p\mathcal{O}$ itself is the unique prime of $\mathcal{O}$ containing $p$.
> 2. **(split)** $\bar g = (X - \bar r)(X - \bar s)$ with $\bar r \neq \bar s$ in $\mathbb{F}_p$ $\iff$ $p\mathcal{O}$ is radical but not maximal. Then $\mathcal{O}/p\mathcal{O} \cong \mathbb{F}_p \times \mathbb{F}_p$, and there are exactly two primes above $p$, namely $p\mathcal{O} + (\tau - r)\mathcal{O}$ and $p\mathcal{O} + (\tau - s)\mathcal{O}$ for integer lifts $r, s$.
> 3. **(ramified)** $\bar g = (X - \bar A)^2$ for some $\bar A \in \mathbb{F}_p$ $\iff$ $p\mathcal{O}$ is not radical. Then $\mathcal{O}/p\mathcal{O} \cong \mathbb{F}_p[Y]/(Y^2)$ (dual numbers), and $\mathfrak{p} = p\mathcal{O} + (\tau - A)\mathcal{O}$ is the unique prime above $p$ (any integer lift $A$); it satisfies $\mathfrak{p}^2 \subseteq p\mathcal{O} \subsetneq \mathfrak{p}$.
>
> Moreover, the cases are detected by symbols and congruences:
>
> * for $p$ **odd**: case 1 $\iff \left(\tfrac{d}{p}\right) = -1$; case 2 $\iff \left(\tfrac{d}{p}\right) = 1$; case 3 $\iff \left(\tfrac{d}{p}\right) = 0 \iff p \mid d$;
> * for $p = 2$: case 1 $\iff d \equiv 5 \pmod 8$; case 2 $\iff d \equiv 1 \pmod 8$; case 3 $\iff 2 \mid d$ (equivalently $4 \mid d$, as $d \equiv 0, 1 \bmod 4$).

> **Lemma 5 (split criterion; thesis Remark 3.2.3, promoted to a lemma).** For every rational prime $p$:
> $$p \text{ splits in } \mathcal{O}_d \iff p \text{ splits in } \mathcal{O}_K \text{ and } p \nmid f.$$
> Here "splits in $\mathcal{O}_K$" is Definition 1 applied to $\mathcal{O}_K = \mathcal{O}_D$, which by Theorem 4 agrees with the classical Dedekind-domain notion $p\mathcal{O}_K = \mathfrak{q}\mathfrak{q}'$, $\mathfrak{q} \neq \mathfrak{q}'$.

> **Corollary 6 (unique prime above a conductor prime).** Suppose $p \mid f$. Then $\bar g = (X - \bar A)^2$ is the square of a monic linear polynomial ($A = 0$ works for odd $p$; $A = (d^2-d)/4$ works for $p = 2$), so $p$ is ramified in $\mathcal{O}_d$, and there is **exactly one** prime ideal of $\mathcal{O}$ containing $p$, namely
> $$\mathfrak{p} = p\mathcal{O} + (\tau - A)\mathcal{O} = p\mathbb{Z} \oplus (\tau - A)\mathbb{Z}, \qquad [\mathcal{O} : \mathfrak{p}] = p, \qquad \mathcal{O}/\mathfrak{p} \cong \mathbb{F}_p.$$

## Role in the development

Proposition 3 and Theorem 4 are the entry point of all of Chapter 3: they classify the primes of the (generally non-maximal) order $\mathcal{O}_d$ above a rational prime, where Kummer–Dedekind for the maximal order does not apply (conductor primes are exactly the excluded case). Corollary 6 is the **standing hypothesis of §§3.2–3.3 of the thesis** (ERRATA E6.2): Lemmas 3.2.2, 3.2.4, 3.2.7 and 3.2.8 all speak of "the" prime $\mathfrak{p}$ above $p \mid f$, and the bridge lemma "index $p^m$ $\Rightarrow$ $\mathfrak{p}$-primary" rests on the uniqueness proved here. Lemma 5 (asserted without proof in the thesis as Remark 3.2.3; flagged as load-bearing in ERRATA E6.3) supplies the link between splitting in $\mathcal{O}_d$ and in $\mathcal{O}_K$ used when the counting formulas of Theorem 3.1.2 are cased on the behaviour of $p$ in $\mathcal{O}_K$. Upstream, this document uses only the construction of $\mathcal{O}_d$ with its power basis $\{1, \tau\}$ and elementary algebra of $\mathbb{F}_p[X]$.

## Proof

### Proof of Lemma 2 (quotient presentation)

Identify $\mathcal{O} = \mathbb{Z}[X]/(g)$ as in the notation section. Let $\pi \colon \mathbb{Z}[X] \to \mathbb{F}_p[X]$ be coefficientwise reduction; $\pi$ is a surjective ring homomorphism with kernel $p\mathbb{Z}[X]$.

**Step 1: $\mathbb{Z}[X]/(p, g) \cong \mathbb{F}_p[X]/(\bar g)$.** Let $\psi \colon \mathbb{Z}[X] \to \mathbb{F}_p[X]/(\bar g)$ be $\pi$ followed by the quotient map; $\psi$ is surjective. Its kernel is $\pi^{-1}\big((\bar g)\big) = p\mathbb{Z}[X] + g\mathbb{Z}[X]$: the inclusion $\supseteq$ holds because $\pi(p) = 0$ and $\pi(g) = \bar g$; conversely, if $\pi(h) = \bar g\,\bar k$ then, lifting $\bar k$ to $k \in \mathbb{Z}[X]$, we get $\pi(h - gk) = 0$, so $h - gk \in p\mathbb{Z}[X]$ and $h \in p\mathbb{Z}[X] + g\mathbb{Z}[X]$. The first isomorphism theorem gives $\mathbb{Z}[X]/(p, g) \cong \mathbb{F}_p[X]/(\bar g)$.

**Step 2: $\mathcal{O}/p\mathcal{O} \cong \mathbb{Z}[X]/(p, g)$.** The preimage of $p\mathcal{O}$ under the quotient map $\rho \colon \mathbb{Z}[X] \twoheadrightarrow \mathbb{Z}[X]/(g) = \mathcal{O}$ is $(p) + (g)$: indeed, $h \in \rho^{-1}(p\mathcal{O})$ means $h(\tau) = p\beta$ for some $\beta \in \mathcal{O}$; lifting $\beta$ to $b \in \mathbb{Z}[X]$ gives $h - pb \in \ker\rho = (g)$. By the third isomorphism theorem, $\mathcal{O}/p\mathcal{O} \cong \mathbb{Z}[X]/(p, g)$.

Composing Steps 1–2 yields the isomorphism $\Phi$; chasing $X$ and constants through both steps gives $\Phi(\tau \bmod p\mathcal{O}) = X \bmod (\bar g)$ and $\Phi(n \bmod p\mathcal{O}) = \bar n$. $\blacksquare$

*(Note: primality of $p$ is not used — the same argument works for any integer modulus. The Lean statement `quadraticOrderModP_equiv_polyModQuot` carries a primality instance only because that is its sole use site; it also needs no congruence hypothesis on $d$.)*

### Proof of Proposition 3

Write $I = (\bar g) \subseteq \mathbb{F}_p[X]$. We chain three inclusion-preserving bijections.

**(a) Primes of $\mathcal{O}$ containing $p$ $\leftrightarrow$ primes of $\mathcal{O}/p\mathcal{O}$.** A prime of $\mathcal{O}$ contains $p$ iff it contains the ideal $p\mathcal{O}$; the correspondence theorem for the quotient map $\mathcal{O} \twoheadrightarrow \mathcal{O}/p\mathcal{O}$ restricts to a bijection between primes of $\mathcal{O}$ containing $p\mathcal{O}$ and primes of $\mathcal{O}/p\mathcal{O}$, preserving inclusions, maximality, and residue rings.

**(b) Transport along $\Phi$.** By Lemma 2, primes of $\mathcal{O}/p\mathcal{O}$ correspond to primes of $\mathbb{F}_p[X]/(\bar g)$, which in turn (correspondence theorem again) correspond to primes of $\mathbb{F}_p[X]$ containing $\bar g$.

**(c) Primes of $\mathbb{F}_p[X]$ containing $\bar g$ $\leftrightarrow$ $\{\bar g_1, \dots, \bar g_r\}$.** $\mathbb{F}_p[X]$ is a principal ideal domain. Its prime ideals are $(0)$ and $(\pi)$ with $\pi$ irreducible, and each nonzero prime is generated by a unique *monic* irreducible. Since $\bar g$ is monic (hence nonzero), $(0)$ does not contain it, and $\bar g \in (\pi) \iff \pi \mid \bar g \iff \pi$ is an associate of some $\bar g_i$, by uniqueness of factorization. Distinct monic irreducibles generate distinct ideals, so the primes of $\mathbb{F}_p[X]$ containing $\bar g$ are exactly $(\bar g_1), \dots, (\bar g_r)$, pairwise distinct.

**Explicit form of the pullback.** Let $\chi \colon \mathcal{O} \to \mathbb{F}_p[X]/(\bar g)$ be the composite of the quotient map with $\Phi$; for $\alpha = h(\tau)$ with $h \in \mathbb{Z}[X]$ we have $\chi(\alpha) = \bar h \bmod (\bar g)$. Fix $i$ and let $\mathfrak{p}_i \subseteq \mathcal{O}$ be the pullback of $(\bar g_i)/(\bar g)$ under $\chi$. Then:

* $p \in \mathfrak{p}_i$ (as $\chi(p) = 0$) and $g_i(\tau) \in \mathfrak{p}_i$ (as $\chi(g_i(\tau)) = \bar g_i$), so $p\mathcal{O} + g_i(\tau)\mathcal{O} \subseteq \mathfrak{p}_i$.
* Conversely let $\alpha = h(\tau) \in \mathfrak{p}_i$, i.e. $\bar h \equiv \bar k\,\bar g_i \pmod{\bar g}$ for some $\bar k$. Lifting $\bar k$ to $k$ and the cofactor to $l$, we get $h - k g_i - l g \in p\mathbb{Z}[X]$; evaluating at $\tau$ (where $g(\tau) = 0$) gives $\alpha - k(\tau)g_i(\tau) \in p\mathcal{O}$, hence $\alpha \in p\mathcal{O} + g_i(\tau)\mathcal{O}$.

So $\mathfrak{p}_i = p\mathcal{O} + g_i(\tau)\mathcal{O}$. If $g_i'$ is another lift of $\bar g_i$ then $g_i - g_i' \in p\mathbb{Z}[X]$, so $g_i(\tau) - g_i'(\tau) \in p\mathcal{O}$ and the ideal is unchanged. Maximality and the residue field: by the chain above,

$$\mathcal{O}/\mathfrak{p}_i \;\cong\; \big(\mathbb{F}_p[X]/(\bar g)\big)\big/\big((\bar g_i)/(\bar g)\big) \;\cong\; \mathbb{F}_p[X]/(\bar g_i),$$

a field with $p^{\deg \bar g_i}$ elements ($(\bar g_i)$ is maximal in the PID $\mathbb{F}_p[X]$). Distinctness of the $\mathfrak{p}_i$ follows from (c) and bijectivity. Finally $\deg \bar g = 2$, so the factorization of $\bar g$ is one of: an irreducible quadratic ($r = 1$), two distinct monic linear factors ($r = 2$), or the square of a monic linear factor ($r = 1$); in particular $r \in \{1, 2\}$. $\blacksquare$

### Proof of Theorem 4

**Step 0 (trichotomy of shapes).** A monic quadratic over the field $\mathbb{F}_p$ either has no root (then it is irreducible, being quadratic) or factors into monic linear factors, which are distinct or equal. So exactly one of the three shapes in cases 1–3 holds.

**Step 1 (shape $\Rightarrow$ ideal property, plus the extra assertions).**

*Case 1: $\bar g$ irreducible.* In the PID $\mathbb{F}_p[X]$ the ideal $(\bar g)$ is then maximal, so $\mathbb{F}_p[X]/(\bar g)$ is a field, with $p^{\deg \bar g} = p^2$ elements, hence $\cong \mathbb{F}_{p^2}$. By Lemma 2, $\mathcal{O}/p\mathcal{O}$ is a field, i.e. $p\mathcal{O}$ is maximal. By Proposition 3 (with $r = 1$, $g_1 = g$) the unique prime above $p$ is $p\mathcal{O} + g(\tau)\mathcal{O} = p\mathcal{O}$, since $g(\tau) = 0$.

*Case 2: $\bar g = (X - \bar r)(X - \bar s)$, $\bar r \neq \bar s$.* The ideals $(X - \bar r)$ and $(X - \bar s)$ are comaximal, since $(X - \bar r) - (X - \bar s) = \bar s - \bar r$ is a unit. By the Chinese remainder theorem,

$$\mathbb{F}_p[X]/(\bar g) \;\cong\; \mathbb{F}_p[X]/(X - \bar r) \times \mathbb{F}_p[X]/(X - \bar s) \;\cong\; \mathbb{F}_p \times \mathbb{F}_p.$$

A product of fields is reduced, and an ideal $I \subseteq R$ is radical iff $R/I$ is reduced (if $x^n \in I$, $x \notin I$, the class of $x$ is a nonzero nilpotent; conversely a nonzero nilpotent class lifts to such an $x$). Hence $p\mathcal{O}$ is radical (using Lemma 2 to transport reducedness). It is not maximal: $\mathbb{F}_p \times \mathbb{F}_p$ is not a domain ($(1,0)(0,1) = 0$), so $p\mathcal{O}$ is not even prime. The two primes above $p$ are given by Proposition 3 applied to the lifts $X - r$, $X - s$: they are $p\mathcal{O} + (\tau - r)\mathcal{O}$ and $p\mathcal{O} + (\tau - s)\mathcal{O}$.

*Case 3: $\bar g = (X - \bar A)^2$.* Comparing coefficients of $\bar g = X^2 - \bar d X + \overline{(d^2 - d)/4}$ with $(X - \bar A)^2$ gives

$$2A \equiv d \pmod p \qquad\text{and}\qquad A^2 \equiv \tfrac{d^2 - d}{4} \pmod p,$$

whence $g(A) = A^2 - dA + \tfrac{d^2-d}{4} \equiv A^2 - 2A\cdot A + A^2 = 0 \pmod p$. Substituting $X = A + Y$ in $g$ yields the polynomial identity $g(A + Y) = Y^2 + (2A - d)Y + g(A)$; evaluating at $Y = \tau - A$ and using $g(\tau) = 0$:

$$(\tau - A)^2 = (d - 2A)(\tau - A) - g(A).$$

Both terms on the right lie in $p\mathcal{O}$, because $p \mid d - 2A$ and $p \mid g(A)$. So $(\tau - A)^2 \in p\mathcal{O}$. On the other hand $\tau - A \notin p\mathcal{O} = p\mathbb{Z} \oplus p\mathbb{Z}\tau$: its $\tau$-coordinate in the basis $\{1, \tau\}$ is $1 \notin p\mathbb{Z}$. Hence $p\mathcal{O}$ is not radical, with explicit witness $\tau - A$. For the quotient: the substitution $X \mapsto X + \bar A$ is an $\mathbb{F}_p$-algebra automorphism of $\mathbb{F}_p[X]$ carrying $((X - \bar A)^2)$ to $(X^2)$, so $\mathcal{O}/p\mathcal{O} \cong \mathbb{F}_p[X]/(X^2) = \mathbb{F}_p[Y]/(Y^2)$. By Proposition 3 ($r = 1$, lift $X - A$) the unique prime above $p$ is $\mathfrak{p} = p\mathcal{O} + (\tau - A)\mathcal{O}$. Containments: $\mathfrak{p}^2$ is generated by $p^2$, $p(\tau - A)$, $(\tau - A)^2$, all of which lie in $p\mathcal{O}$, so $\mathfrak{p}^2 \subseteq p\mathcal{O}$; and $p\mathcal{O} \subsetneq \mathfrak{p}$ because $\tau - A \in \mathfrak{p} \setminus p\mathcal{O}$.

**Step 2 (ideal property $\Rightarrow$ shape).** The three shapes are mutually exclusive and exhaustive (Step 0). The three ideal properties are also mutually exclusive and exhaustive: every ideal is radical or not, a radical ideal is maximal or not, and a maximal ideal is prime, hence radical — so "maximal", "radical but not maximal", "not radical" partition all cases. Given Step 1 ($\text{shape}_i \Rightarrow \text{property}_i$ for $i = 1, 2, 3$), suppose $\text{property}_i$ holds; the actual shape is some $\text{shape}_j$, which forces $\text{property}_j$; disjointness of the properties gives $j = i$. This proves all three equivalences.

**Step 3 (symbol form, $p$ odd).** Here $\bar 2, \bar 4 \in \mathbb{F}_p^\times$. Note first that the constant term of $\bar g$ is $\overline{(d^2 - d)/4} = (\bar d^2 - \bar d)\,\bar 4^{-1}$, since $4 \cdot \tfrac{d^2-d}{4} = d^2 - d$ in $\mathbb{Z}$. Completing the square:

$$\bar g = \Big(X - \tfrac{\bar d}{2}\Big)^2 + \Big(\tfrac{\bar d^2 - \bar d}{4} - \tfrac{\bar d^2}{4}\Big) = \Big(X - \tfrac{\bar d}{2}\Big)^2 - \tfrac{\bar d}{4}.$$

(Equivalently: the discriminant of $\bar g$ is $\bar d^2 - 4 \cdot \overline{(d^2-d)/4} = \bar d$.) The substitution $X \mapsto X + \bar d/2$ is an automorphism of $\mathbb{F}_p[X]$, so $\bar g$ has the same shape as $Y^2 - \bar d/4$, namely: irreducible if $\bar d/4$ — equivalently $\bar d = \bar 4 \cdot (\bar d/4)$, a square multiple — is a nonsquare; two distinct roots $\pm t$ ($t \ne 0$, and $t \ne -t$ as $p$ is odd) if $\bar d$ is a nonzero square; a double root if $\bar d = 0$. These three cases are $\left(\tfrac dp\right) = -1$, $1$, $0$ respectively, and $\left(\tfrac dp\right) = 0 \iff p \mid d$.

**Step 4 ($p = 2$).** Over $\mathbb{F}_2$, $\bar g = X^2 + \bar d X + \bar q$ where $q := \tfrac{d^2 - d}{4} = \tfrac{d(d-1)}{4}$ (note $-\bar d = \bar d$).

* If $d \equiv 0 \pmod 4$ (the only even case allowed by $d \equiv 0, 1 \bmod 4$): $\bar d = 0$, so $\bar g = X^2 + \bar q = (X + \bar q)^2$, using $c^2 = c$ for $c \in \mathbb{F}_2$. Shape 3 (ramified).
* If $d \equiv 1 \pmod 4$: $\bar d = 1$ and $q = d \cdot \tfrac{d - 1}{4}$ with $\tfrac{d-1}{4} \in \mathbb{Z}$ and $d$ odd, so $\bar q = \overline{\tfrac{d-1}{4}}$.
  * $d \equiv 1 \pmod 8$: $\tfrac{d-1}{4}$ is even, $\bar q = 0$, and $\bar g = X^2 + X = X(X + 1)$ — two distinct roots, shape 2 (split).
  * $d \equiv 5 \pmod 8$: $\tfrac{d-1}{4}$ is odd, $\bar q = 1$, and $\bar g = X^2 + X + 1$, which has no root in $\mathbb{F}_2$ (it evaluates to $1$ at both $0$ and $1$) — shape 1 (inert). $\blacksquare$

### Proof of Lemma 5 (split criterion)

**Claim 1: if $p \mid f$, then $\bar g_d$ is the square of a monic linear polynomial; in particular $p$ is ramified, hence does not split, in $\mathcal{O}_d$.**

Since $d = Df^2$, we have $f^2 \mid d$, so $p \mid f$ gives $p^2 \mid d$.

* $p$ odd: $p \mid d$ gives $\bar d = 0$; moreover $4 \cdot \tfrac{d^2 - d}{4} = d(d - 1) \equiv 0 \pmod p$ and $p \nmid 4$, so $p \mid \tfrac{d^2-d}{4}$ and the constant term also vanishes. Thus $\bar g_d = X^2$, shape 3 (with $\bar A = 0$).
* $p = 2$: $p^2 \mid d$ gives $4 \mid d$, and Step 4 of Theorem 4 shows $\bar g_d = (X + \bar q)^2$, shape 3.

By Theorem 4, $p$ is ramified in $\mathcal{O}_d$.

**Claim 2: if $p \nmid f$, then $\bar g_d$ and $\bar g_D$ have the same shape; consequently $p$ has the same splitting type in $\mathcal{O}_d$ and in $\mathcal{O}_K = \mathcal{O}_D$.**

Set $c := \tfrac{d - Df}{2} = \tfrac{Df(f-1)}{2} \in \mathbb{Z}$ (one of $f$, $f - 1$ is even). We claim the polynomial identity in $\mathbb{Z}[X]$:

$$g_d(fX + c) = f^2\, g_D(X).$$

Expand the left side: $g_d(fX + c) = f^2 X^2 + (2cf - df)X + \big(c^2 - dc + \tfrac{d^2 - d}{4}\big)$.

* Linear coefficient: $2c = d - Df$, so $2cf - df = f(2c - d) = f(-Df) = -Df^2 = f^2 \cdot (-D)$. ✔
* Constant coefficient: with $c = \tfrac{d - Df}{2}$,
  $$c^2 - dc + \tfrac{d^2-d}{4} = \tfrac{(d - Df)^2 - 2d(d - Df) + d^2 - d}{4} = \tfrac{D^2 f^2 - d}{4} = \tfrac{D^2 f^2 - D f^2}{4} = f^2 \cdot \tfrac{D^2 - D}{4}. \;✔$$

Reducing mod $p$: $\bar g_d(\bar f X + \bar c) = \bar f^{\,2}\, \bar g_D(X)$. Since $p \nmid f$, $\bar f \in \mathbb{F}_p^\times$, so $\sigma \colon h(X) \mapsto h(\bar f X + \bar c)$ is an $\mathbb{F}_p$-algebra automorphism of $\mathbb{F}_p[X]$ (with inverse $X \mapsto \bar f^{-1}(X - \bar c)$). Automorphisms of $\mathbb{F}_p[X]$ of this form preserve degrees, irreducibility, and multiplicities of factors; and $\sigma(\bar g_d) = \bar f^{\,2} \bar g_D$ is a unit multiple of $\bar g_D$. Hence $\bar g_d$ and $\bar g_D$ have the same shape (irreducible / two distinct linear / square of linear). By Theorem 4 — applied once with discriminant $d$ and once with discriminant $D$ (note $\mathcal{O}_K = \mathcal{O}_D$ is itself an order of the same form, with conductor $1$) — the splitting type of $p$ in $\mathcal{O}_d$ equals that in $\mathcal{O}_K$.

**Conclusion.** If $p$ splits in $\mathcal{O}_d$, then $p \nmid f$ by Claim 1 (contrapositive), and then $p$ splits in $\mathcal{O}_K$ by Claim 2. Conversely, if $p$ splits in $\mathcal{O}_K$ and $p \nmid f$, Claim 2 gives that $p$ splits in $\mathcal{O}_d$. $\blacksquare$

### Proof of Corollary 6

By Claim 1 of Lemma 5, $\bar g = (X - \bar A)^2$ with $A = 0$ for odd $p$, and $A = q = \tfrac{d^2-d}{4}$ for $p = 2$ (over $\mathbb{F}_2$, $(X + \bar q)^2 = (X - \bar q)^2$). So $\bar g$ has exactly one distinct monic irreducible factor, $X - \bar A$. By Proposition 3, $\mathcal{O}$ has exactly one prime ideal containing $p$, namely $\mathfrak{p} = p\mathcal{O} + (\tau - A)\mathcal{O}$, with $\mathcal{O}/\mathfrak{p} \cong \mathbb{F}_p[X]/(X - \bar A) \cong \mathbb{F}_p$, hence $[\mathcal{O} : \mathfrak{p}] = p$.

For the explicit $\mathbb{Z}$-module form: $\mathfrak{p}$ is generated as a $\mathbb{Z}$-module by $p,\ p\tau,\ \tau - A,\ (\tau - A)\tau$. Now $p\tau = p(\tau - A) + pA \in p\mathbb{Z} + (\tau - A)\mathbb{Z}$, and by the identity from Theorem 4 Step 1 Case 3,

$$(\tau - A)\tau = (\tau - A)^2 + A(\tau - A) = (d - 2A)(\tau - A) - g(A) + A(\tau - A) = (d - A)(\tau - A) - g(A),$$

with $g(A) \in p\mathbb{Z}$ (shape 3). So all four generators lie in $p\mathbb{Z} + (\tau - A)\mathbb{Z}$, giving $\mathfrak{p} = p\mathbb{Z} + (\tau - A)\mathbb{Z}$; the sum is direct because $p$ and $\tau - A$ have coordinates $(p, 0)$ and $(-A, 1)$ in the basis $\{1, \tau\}$, which are $\mathbb{Z}$-linearly independent. $\blacksquare$

## Remarks

**R1 (Divergence from the thesis: proof route).** The thesis proves Proposition 3.2.1 by writing a candidate prime as $\mathfrak{p} = (p) + I$ and manipulating $\mathcal{O}/\mathfrak{p} \cong \big(\mathbb{Z}/p[x]/(\prod \bar g_i)\big)/\bar I$, asserting that "in order to be an integral domain, $\bar I$ must contain $(\bar g_i)$ for some $i$". Here — following the existing Lean formalization — everything is instead routed through the single ring isomorphism $\Phi \colon \mathcal{O}/p\mathcal{O} \cong \mathbb{F}_p[X]/(\bar g)$ of Lemma 2, and all ideal-theoretic properties (maximality, radicality, reducedness of quotients) are transported across it; the PID structure of $\mathbb{F}_p[X]$ then does all the work. This route also makes explicit three points the thesis leaves implicit: (i) the justification of the "integral domain" step (classification of the primes of $\mathbb{F}_p[X]/(\bar g)$); (ii) pairwise distinctness of the $\mathfrak{p}_i$ and their independence of the chosen lifts $g_i$; (iii) that all primes above $p$ are maximal, with computed residue fields. The mathematical content is unchanged.

**R2 (Remark 3.2.3 promoted; ERRATA E6.3, E6.2).** In the thesis, Remark 3.2.3 is asserted without proof, yet it is load-bearing: the standing hypothesis "$p \mid f$, hence a unique prime $\mathfrak{p}$ above $p$" underlies Lemmas 3.2.2, 3.2.4, 3.2.7, 3.2.8, whose statements are false for split $p$ (ERRATA E6.2). Lemma 5 supplies the missing proof, and Corollary 6 promotes the uniqueness consequence to a standalone statement, as ERRATA E6.3 prescribes ("easy from Prop 3.2.1: for $p \mid f$, $g$ mod $p$ is the square of a linear polynomial" — exactly Claim 1).

**R3 (Pitfall: "ramified" does not mean $p\mathcal{O} = \mathfrak{p}^2$ when $p \mid f$).** In $\mathcal{O}_K$, a ramified prime satisfies $p\mathcal{O}_K = \mathfrak{q}^2$. For conductor primes this fails: only $\mathfrak{p}^2 \subseteq p\mathcal{O} \subsetneq \mathfrak{p}$ survives (Theorem 4, case 3). Example: $d = -27$ ($D = -3$, $f = 3$, $p = 3$), $g = X^2 + 27X + 189$, $\mathfrak{p} = (3, \tau) = 3\mathbb{Z} \oplus \tau\mathbb{Z}$. Then $\mathfrak{p}^2 = (9, 3\tau, \tau^2)$ with $\tau^2 = -27\tau - 189 \in (9, 3\tau)$, so $\mathfrak{p}^2 = (9, 3\tau) = 3\mathfrak{p}$, of index $27$, while $[\mathcal{O} : 3\mathcal{O}] = 9$; thus $\mathfrak{p}^2 \neq 3\mathcal{O}$. The relation $\mathfrak{p}^2 = 3\mathfrak{p}$ with $\mathfrak{p} \neq 3\mathcal{O}$ also shows $\mathfrak{p}$ is not invertible (cancel $\mathfrak{p}$ otherwise). This is the structural reason the counting arguments of §3.3 cannot proceed by unique factorization.

**R4 (Hypotheses actually used).** Nothing here needs $d < 0$: every statement and proof works for any non-square integer $d \equiv 0, 1 \pmod 4$ (compare the analogous observation for Prop 3.1.1 in ERRATA E6.9). The hypothesis "$d$ is not a perfect square" is used only for the identification $\mathbb{Z}[X]/(g) \cong \mathbb{Z}[\tau] \subseteq K$; the Lean formalization sidesteps it by *defining* $\mathcal{O}_d := \mathbb{Z}[X]/(g)$ (`AdjoinRoot (poly d)`) for every $d \in \mathbb{Z}$, introducing $d \equiv 0, 1 \pmod 4$ only where needed (a deliberate divergence recorded in `Basic.lean`).

**R5 ($p = 2$ and the Kronecker symbol).** With the Kronecker symbol $\left(\tfrac{d}{2}\right)$ ($= 0$ if $2 \mid d$; $1$ if $d \equiv \pm 1 \bmod 8$; $-1$ if $d \equiv \pm 3 \bmod 8$; for discriminants only $d \equiv 1, 5 \bmod 8$ occur among odd $d$), the symbol form of Theorem 4 is uniform in $p$: inert $\iff \left(\tfrac dp\right) = -1$, split $\iff \left(\tfrac dp\right) = 1$, ramified $\iff \left(\tfrac dp\right) = 0$. The current Lean formalization states the symbol form only for odd $p$ (Mathlib's `legendreSym` requires odd $p$; a Kronecker symbol would come from the QNF vendor plan, PLAN.md D1); the $p = 2$ case is nonetheless fully covered *structurally* by Lemma 2 (which has no $p \neq 2$ hypothesis) plus the explicit mod-8 case analysis of Theorem 4 Step 4. Note also that the Lean `prime_ramified_iff` carries a $p \neq 2$ hypothesis although the equivalence "$p\mathcal{O}$ not radical $\iff p \mid d$" is true for $p = 2$ as well (Step 4) — a possible future strengthening, not an error.

**R6 (Multiplicities are dropped).** The bijection of Proposition 3 is with the *distinct* monic irreducible factors of $\bar g$, not with factors counted with multiplicity: in the ramified case $\bar g = (X - \bar A)^2$ has one distinct factor and one prime above $p$. The thesis's phrasing "denote the irreducible factors of $g(x)$ mod $p$ by $g_i(x)$" should be read this way.

**R7 (Odd-$p$ shortcut for Lemma 5).** For odd $p \nmid f$, Claim 2 also follows in one line from symbols: $\left(\tfrac{d}{p}\right) = \left(\tfrac{D}{p}\right)\left(\tfrac{f}{p}\right)^2 = \left(\tfrac{D}{p}\right)$. This is the route a Lean proof composing `prime_split_iff` at $d$ and at $D$ would take; the substitution argument given above is preferred here because it covers $p = 2$ uniformly.

## Lean correspondence

| Statement | Lean declaration | File | Status |
|---|---|---|---|
| Lemma 2 (quotient presentation $\Phi$) | `QuadraticOrder.quadraticOrderModP_equiv_polyModQuot` | `singular_moduli/QuadraticOrder/Prime/QuotientIso.lean` | **Proved.** No $p \neq 2$ or $d \equiv 0,1 \ (4)$ hypotheses needed. |
| Reduction $\bar g$ and its symbol bridges (Steps 0, 3 of Thm 4) | `QuadraticOrder.polyMod`, `polyMod_eq`, `polyMod_monic`, `polyMod_natDegree`, `polyMod_discrim_eq`, `polyMod_exists_root_iff_isSquare_d`, `polyMod_no_root_iff_legendreSym_eq_neg_one`, `legendreSym_eq_zero_iff_dvd`, `polyMod_eq_X_sq_of_p_dvd_d`, `polyMod_exists_two_distinct_roots_of_legendreSym_eq_one`, `polyMod_irreducible_iff_legendreSym_eq_neg_one` | `singular_moduli/QuadraticOrder/Prime/PolyMod.lean` | **Proved** (symbol statements for odd $p$). |
| Proposition 3 (primes $\leftrightarrow$ irreducible factors) | no standalone declaration; realized through the quotient iso + the trichotomy files | — | Implicit. A named bijection statement could be added later if a downstream proof needs it. |
| Theorem 4, case 1 (inert) | `QuadraticOrder.prime_inert_iff` (via `span_p_isMaximal_iff_irreducible_polyMod`) | `singular_moduli/QuadraticOrder/Prime/Inert.lean` | **Proved** (odd $p$). |
| Theorem 4, case 3 (ramified) | `QuadraticOrder.prime_ramified_iff`; witnesses `tau_sq_mem_span_p_of_p_dvd_d`, `tau_not_mem_span_p`; quotient shape `quadraticOrderModP_equiv_X_sq_quot` | `singular_moduli/QuadraticOrder/Prime/Ramified.lean`, `Prime/QuotientIso.lean` | **Proved** (odd $p$; the Lean witness is $\tau$, i.e. the lift $A = 0$). |
| Theorem 4, case 2 (split) | `QuadraticOrder.prime_split_iff` | `singular_moduli/QuadraticOrder/Prime/Split.lean` | **Proved** (odd $p$). |
| Theorem 4, $p = 2$ congruence form (Step 4) | — | — | **Not formalized.** Needs either a direct mod-8 case analysis or a Kronecker symbol (PLAN.md D1). |
| Lemma 5 (split criterion, Rem 3.2.3) | no declaration yet; derivable from `prime_split_iff` at $d$ and at $D$ plus Legendre multiplicativity (odd $p$) | — | **Not started.** Should be added alongside the conductor-prime stub. |
| Corollary 6 (unique prime above $p \mid f$) | `QuadraticOrder.existsUnique_isPrime_mem_of_dvd_conductor` | `singular_moduli/QuadraticOrder/Prime/ConductorPrime.lean` | **Stub** (`sorry`; statement frozen by WP-0). Stated as `∃! P : Ideal (QuadraticOrder d), P.IsPrime ∧ (p : QuadraticOrder d) ∈ P` under the bundled standing hypotheses `[ConductorPrimeSetup d D f p]` of `Defs/Setup.lean` ($d < 0$, $d = Df^2$ with $D$ fundamental, $f > 0$, $p$ prime, $p \mid f$); negativity of $d$ enters only through that shared setup class, not through the proof below. |

## References

* C. Geiger, *Singular Moduli and the Ideal Class Group*, senior thesis, University of Washington, 2020 — §3.2, Proposition 3.2.1 and Remark 3.2.3 (thesis pp. 14–15).
* `ERRATA.md` (repo root) — E6.2 (unrestated standing hypotheses of §3.2), E6.3 (Remark 3.2.3 asserted without proof; proof sketch adopted here), E6.9 (hypothesis hygiene).
* D. A. Cox, *Primes of the Form $x^2 + ny^2$*, 2nd ed., Wiley — §7 (orders in imaginary quadratic fields; conductor, $\mathcal{O} = \mathbb{Z} + f\mathcal{O}_K$).
* J. Neukirch, *Algebraic Number Theory*, Springer — Proposition I.8.3 (Kummer–Dedekind factorization; Proposition 3 is its conductor-inclusive analogue for the monogenic order $\mathbb{Z}[\tau]$).
* `PLAN.md` §2 (inventory rows for Prop 3.2.1 / Rem 3.2.3) and §5.2 (dependency graph nodes P321, R323).
