/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Decidability of short polynomials in polynomial ideals

*Reference:* [No short polynomials vanish on bounded rank matrices](
https://doi.org/10.1112/blms.12819)
by *Jan Draisma, Thomas Kahle, Finn Wiersig*, Bull. Lond. Math. Soc. (2023)

*Reference:* [Finding binomials in polynomial ideals](
https://doi.org/10.1186/s40687-017-0106-0)
by *Anders Jensen, Thomas Kahle, Lukas Katthän*, Res. Math. Sci. (2017)

*Reference:* [Computing the binomial part of a polynomial ideal](
https://doi.org/10.1016/j.jsc.2023.102298)
by *Martin Kreuzer, Florian Walsh*, J. Symbolic Comput. (2024)

*Reference:* [Computing sparse multiples of polynomials](
https://doi.org/10.1007/s00453-012-9652-4)
by *Mark Giesbrecht, Daniel S. Roche, Hrushikesh Tilak*, Algorithmica (2012)

*Reference:* [What is the shortest polynomial divisible by (x-1)(y-1)(x²y-1)?](
https://mathoverflow.net/questions/273132) — MathOverflow question by Thomas Kahle (2017).
YCor's comment poses the decidability question: "A general question is whether it's decidable
(given an oracle to compute in K), and also whether it's decidable for principal ideals."

A polynomial is *$t$-short* if it is nonzero and has at most $t$ terms. Given generators
of an ideal $I \subseteq \mathbb{Q}[x_1, x_2, \ldots]$, can one algorithmically decide
whether $I$ contains a $t$-short polynomial?

The problem is solved for $t \leq 2$: monomials ($t = 1$) can be detected via colon ideals,
and binomials ($t = 2$) via the algorithm of Jensen–Kahle–Katthän (2017). For $t \geq 3$,
the problem is open, even in the univariate case $\mathbb{Q}[x]$.
-/

namespace ShortPolynomialDecidability

noncomputable section

open MvPolynomial

/--
An ideal $I \subseteq \mathbb{Q}[x_1, x_2, \ldots]$ *has a $t$-short polynomial* if there
exists a nonzero $p \in I$ with $|\operatorname{supp}(p)| \leq t$.

The original problem is stated for polynomial rings $\mathbb{Q}[x_1, \ldots, x_n]$ in
finitely many variables, with $n$ part of the input. Here we use `MvPolynomial ℕ ℚ`
(countably many variables) as the ambient ring. This is equivalent because the generators
are finite and each mentions only finitely many variables, so every element of the ideal
uses finitely many variables. The ideal effectively lives in `MvPolynomial (Fin n) ℚ`
for the appropriate $n$.
-/
def HasShortPoly (t : ℕ) (I : Ideal (MvPolynomial ℕ ℚ)) : Prop :=
  ∃ p ∈ I, p ≠ 0 ∧ p.support.card ≤ t

/--
A multivariate polynomial represented as a list of (exponent vector, coefficient) pairs.
Each exponent vector is a `List ℕ` giving exponents of $x_0, x_1, \ldots$ in order.
Coefficients are pairs `(num : ℤ, den : ℕ)` representing the rational number `num / den`.

We use this concrete representation rather than `MvPolynomial ℕ ℚ` directly because
`ComputablePred` requires `Primcodable` on its input type. Mathlib provides `Primcodable`
for `List`, `ℕ`, `ℤ`, and their products, so `PolyRep` is automatically `Primcodable`.
In contrast, `MvPolynomial ℕ ℚ` is defined as `(ℕ →₀ ℕ) →₀ ℚ` (a `Finsupp` of
`Finsupp`s), and Mathlib has no `Primcodable` instance for `Finsupp`. While `Finsupp`
is `Encodable` (via `Mathlib.Data.Finsupp.Encodable`), the stronger `Primcodable`
instance needed for `ComputablePred` is not available.

The interpretation function `polyOfRep` bridges this concrete encoding to the
mathematical `MvPolynomial ℕ ℚ` where the predicate `HasShortPoly` is stated.
-/
abbrev PolyRep := List (List ℕ × ℤ × ℕ)

/--
Interpret an exponent vector as a monomial in `ℕ →₀ ℕ`.
-/
def monomialOfList (l : List ℕ) : ℕ →₀ ℕ :=
  (l.mapIdx (fun i e => Finsupp.single i e)).sum

/--
Interpret a `PolyRep` as a polynomial in $\mathbb{Q}[x_1, x_2, \ldots]$.
Each entry `(exps, num, den)` represents the term $\frac{\mathtt{num}}{\mathtt{den}} \cdot
x_0^{e_0} x_1^{e_1} \cdots$, where the coefficient is given as a fraction `num / den`
with `num : ℤ` and `den : ℕ`.
-/
def polyOfRep (p : PolyRep) : MvPolynomial ℕ ℚ :=
  (p.map (fun (exps, num, den) =>
    MvPolynomial.monomial (monomialOfList exps) (↑num / ↑den))).sum

/--
Build an ideal from a list of polynomial representations.
-/
def idealOfInput (L : List PolyRep) : Ideal (MvPolynomial ℕ ℚ) :=
  Ideal.span (Set.range (fun i : Fin L.length => polyOfRep (L.get i)))

/--
The short polynomial decision problem for a fixed $t$: given a list of generators
(in the concrete `PolyRep` encoding), does the ideal they generate contain a $t$-short
polynomial?
-/
def decisionProblem (t : ℕ) : List PolyRep → Prop :=
  fun L => HasShortPoly t (idealOfInput L)

/--
It is decidable whether a finitely generated ideal in
$R = \mathbb{Q}[x_1, x_2, \ldots]$
contains a monomial ($1$-short polynomial).
This follows from the characterization via iterated colon ideals:
$I$ contains a monomial if and only if $I : (\prod x_i)^\infty = R$.
-/
@[category research solved, AMS 13 68]
theorem monomial_decidability : ComputablePred (decisionProblem 1) := by
  sorry

/--
It is decidable whether a finitely generated ideal in
$R = \mathbb{Q}[x_1, x_2, \ldots]$
contains a binomial ($2$-short polynomial).
This was proved by Jensen–Kahle–Katthän (2017) using Artinian reduction via tropical
geometry and algorithms from algebraic number theory. Kreuzer–Walsh (2024) later gave
an explicit algorithm computing the full binomial part of any polynomial ideal over an
arbitrary field, using cellular decomposition and exponent lattices, without tropical geometry.
It is implemented in SageMath.
-/
@[category research solved, AMS 13 68]
theorem binomial_decidability : ComputablePred (decisionProblem 2) := by
  sorry

/--
**Main conjecture.** Is it decidable whether a finitely generated ideal in
$\mathbb{Q}[x_1, x_2, \ldots]$ contains a $t$-short polynomial, for $t \geq 3$?

Both decidability and undecidability are considered plausible. No degree bound is known
that would reduce the problem to a finite-dimensional linear algebra computation.
The difficulty is illustrated by Fibonacci-type examples where the degree of the shortest
polynomial in an ideal depends on the *coefficients* of the generators, not on any classical
degree based invariant of the ideal (see below).
-/
@[category research open, AMS 13 68]
theorem short_poly_decidability :
    answer(sorry) ↔ ∀ t, 3 ≤ t → ComputablePred (decisionProblem t) := by
  sorry

/--
The trinomial case ($t = 3$) is the first open instance.
-/
@[category research open, AMS 13 68]
theorem short_poly_decidability.variants.trinomial :
    answer(sorry) ↔ ComputablePred (decisionProblem 3) := by
  sorry

/--
The Fibonacci family of ideals $I_n = \langle y - F_n x - F_{n-1},\, x^2 - x - 1 \rangle
\subseteq \mathbb{Q}[x, y]$, where $F_n = \mathtt{Nat.fib}\, n$ ($F_0 = 0$, $F_1 = 1$).

This family shows that a computable degree bound for the shortest polynomial in an ideal
must depend on the *coefficients* of the generators: the ideal $I_n$ contains the binomial
$x^n - y$, and this is the lowest-degree binomial in $I_n$. Since the degree grows with $n$
while the generators always have degrees 1 and 2, no classical invariant (generating degree,
Castelnuovo–Mumford regularity, primary decomposition) can yield a uniform degree bound.
-/
def fibIdeal (n : ℕ) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {
    X 1 - C (Nat.fib n : ℚ) * X 0 - C (Nat.fib (n - 1) : ℚ),
    X 0 ^ 2 - X 0 - 1
  }

/-- The binomial $x^n - y$ belongs to $I_n$. This follows from the Fibonacci recurrence:
modulo $x^2 - x - 1$, one has $x^n \equiv F_n x + F_{n-1}$, so $x^n - y \equiv 0$ in $I_n$. -/
@[category test, AMS 13]
theorem fib_ideal_contains_binomial (n : ℕ) (hn : 1 ≤ n) :
    X 0 ^ n - X 1 ∈ fibIdeal n := by
  sorry

/-- The binomial $x^n - y$ is a binomial of minimum total degree in $I_n$: any binomial
in $I_n$ has total degree at least $n$. This is the key property showing that coefficients
govern the degree of the shortest polynomial in an ideal. -/
@[category research solved, AMS 13 68]
theorem fib_ideal_min_degree_binomial (n : ℕ) (hn : 1 ≤ n) :
    ∀ p ∈ fibIdeal n, p.support.card = 2 → n ≤ p.totalDegree := by
  sorry

end

end ShortPolynomialDecidability
