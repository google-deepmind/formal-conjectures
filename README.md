# Cuboid Conjecture 1

A formal proof in Lean 4 / Mathlib of the **First Cuboid Conjecture**, posed by
Shapirov in [*Perfect cuboids and irreducible
polynomials*](https://arxiv.org/abs/1108.5348) (arXiv:1108.5348).

## The conjecture

An **Euler brick** is a rectangular cuboid whose edges and face diagonals all
have integer length. A **perfect cuboid** would be an Euler brick whose space
diagonal is also an integer; none has been found, and the existence question
remains open.

Shapirov reduced the perfect-cuboid problem to three polynomial-irreducibility
conjectures. The first states:

> **First Cuboid Conjecture.** For all positive coprime integers $a$, $b$ with
> $a \neq b$, the degree-8 polynomial
>
> $$P_{a,b}(x) = x^8 + 6(a^2 - b^2)x^6 + (b^4 - 4a^2b^2 + a^4)x^4 - 6a^2b^2(a^2 - b^2)x^2 + a^4b^4$$
>
> is irreducible over $\mathbb{Z}$.

This formalization proves the conjecture. The formal proof was autonomously
discovered by the [AlphaProof
Nexus](https://arxiv.org/abs/2605.22763) agent. An independent informal proof,
using rank-zero elliptic curves, was given by Asiryan
([arXiv:2510.11768](https://arxiv.org/abs/2510.11768)).

## Proof outline

The proof proceeds in four stages.

### 1. No rational roots

Write $Q_{a,b}(y)$ for the degree-4 polynomial satisfying $P_{a,b}(x) = Q_{a,b}(x^2)$.
If $y_0$ is a rational root of $Q$, one can rewrite $Q(y_0) = 0$ as $u^2 = 2v^2$
for certain rational expressions $u$, $v$ in $y_0$. Because $\sqrt{2}$ is irrational, $u = v = 0$,
which forces $ab = 0$ — a contradiction. Hence $Q$ (and therefore $P$) has no
rational root, ruling out any linear factor.

### 2. Irreducibility of $Q_{a,b}$

Suppose $Q_{a,b}$ factors over $\mathbb{Z}$ as $(x^2 + Ux + V)(x^2 + Wx + Z)$. Comparing
coefficients and manipulating the resulting system yields a polynomial identity
in $V + Z$ that factors as

$$(V + Z + 2a^2b^2) \cdot [\text{quadratic in } V + Z] = 0.$$

- **Case $V + Z = -2a^2b^2$:** Forces $(U - W)^2 = 2 \cdot (4(a^2 - b^2))^2$, so
  $a^2 = b^2$ by irrationality of $\sqrt{2}$ — contradiction.
- **Quadratic case:** The discriminant must be a perfect square, but it takes
  the form $x^4 + 34x^2y^2 + y^4$ with $x = a^2 - b^2$, $y = 2ab$.
  This is the Diophantine equation treated in stage 3 below, and
  its only solutions are trivial, again yielding $a^2 = b^2$ or $ab = 0$.

### 3. The Diophantine equation $x^4 + 34x^2y^2 + y^4 = z^2$

The core of the proof shows this equation has only trivial integer solutions
($x = 0$, $y = 0$, or $x = \pm y$) via Fermat-style **infinite descent**: given any
nontrivial positive solution $(x, y, z)$ with $\gcd(x, y) = 1$, a strictly smaller
positive solution is constructed.

**$x$ odd, $y$ even.** A gcd analysis on $z \pm (x^2 + y^2)$ shows
$\gcd = 2$. Factoring through 2 and distributing coprime prime powers yields
coprime $u$, $v$ with $uv = xy$ and $x^2 + y^2 = u^2 - 8v^2$. One then further
factors into pairwise coprime $a$, $b$, $c$, $d$ satisfying $b^2 - c^2 = kd^2$ and
$b^2 + 8c^2 = ka^2$ with $k \mid 9$. The case $k = 3$ is excluded mod 8; the cases
$k = 1$ and $k = 9$ each reduce (via Pythagorean-triple generators $m$, $n$) to a
smaller solution of $x^4 + 34x^2y^2 + y^4 = z^2$.

**Both $x$ and $y$ odd.** Here $z$ is even. Setting $A' = (x^2 - y^2)/2$ and
$B' = 3xy$ gives a Pythagorean-type relation $A'^2 + B'^2 = (z/2)^2$. The gcd of
$A'$ and $B'$ is 1 or 3; in each sub-case, Pythagorean generators again yield a
smaller solution. The size bound $m + n < x + y$ is verified by
comparing squares and using monotonicity of a cubic polynomial.

### 4. Irreducibility of $P_{a,b}$

Suppose $P_{a,b}(x)$ is reducible. Let $F(x)$ be a monic irreducible factor of
degree $d \leq 4$ (since $P$ has degree 8). Since $P$ has no rational root, $d \geq 2$.

- **Symmetry case $F(-x) = F(x)$:** Then $F$ is an even polynomial $F(x) = M(x^2)$,
  and $M$ divides $Q_{a,b}$. But $Q$ is irreducible by stage 2 — contradiction.

- **Coprime case $\gcd(F(x), F(-x)) = 1$:** Then $F(x) \cdot F(-x)$ divides $P_{a,b}(x)$.
  Since $F \cdot F(-x)$ is even and has degree $2d$, it equals some $M(x^2)$ of degree $d$.
  Irreducibility of $Q$ forces $M = Q$, hence $d = 4$ and $F \cdot F(-x) = P$. Writing
  $F = x^4 + Ax^3 + Bx^2 + Cx + D$ and comparing the product against $P$'s
  coefficients, one shows:
  - **$D = a^2b^2$** leads to an identity matching the impossible structure of
    Lemma `square_ident` (no real solutions).
  - **$D = -a^2b^2$** forces $A = 0$, then $B = 3(a^2 - b^2)$, then
    $9(a^2 - b^2)^2 = (a^2 - b^2)^2$, giving $a^2 = b^2$ — contradiction.

## Repository map

- `Challenge.lean` — the auditable theorem statement (with a deliberate `sorry`).
- `Solution.lean` — connects the statement to the completed proof.
- `EulerBrick/` — the full proof development.
- `comparator.json` — tells Comparator which declarations must match.
- `formalization.yaml` — provenance, authorship, automation, and review metadata.
- `LICENSE` — Apache License 2.0.
- `docbuild/` — nested doc-gen4 project.
- `scripts/verify-comparator.sh` — runs pinned Comparator and lean4export.

## Building

```
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
```

The build produces zero `sorry` axioms in `Solution.lean`; the only `sorry` is
the deliberate one in `Challenge.lean`.

## Acknowledgements

Thanks to the Lean community and Mathlib contributors.
