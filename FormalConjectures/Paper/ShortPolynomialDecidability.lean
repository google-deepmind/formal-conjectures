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

*References:*
- [No short polynomials vanish on bounded rank matrices](
  https://doi.org/10.1112/blms.12819)
  by *Jan Draisma, Thomas Kahle, Finn Wiersig*, Bull. Lond. Math. Soc. (2023)
- [Finding binomials in polynomial ideals](
  https://doi.org/10.1186/s40687-017-0106-0)
  by *Anders Jensen, Thomas Kahle, Lukas Katthän*, Res. Math. Sci. (2017)
- [Computing the binomial part of a polynomial ideal](
  https://doi.org/10.1016/j.jsc.2023.102298)
  by *Martin Kreuzer, Florian Walsh*, J. Symbolic Comput. (2024)
- [Computing sparse multiples of polynomials](
  https://doi.org/10.1007/s00453-012-9652-4)
  by *Mark Giesbrecht, Daniel S. Roche, Hrushikesh Tilak*, Algorithmica (2012)
- [What is the shortest polynomial divisible by (x-1)(y-1)(x²y-1)?](
  https://mathoverflow.net/questions/273132) — MathOverflow question by Thomas Kahle (2017).
  YCor's comment poses the decidability question: "A general question is whether it's decidable
  (given an oracle to compute in K), and also whether it's decidable for principal ideals."

A polynomial is *$t$-short* if it is nonzero and has at most $t$ terms. Given generators
of an ideal $I \subseteq \mathbb{Q}[x_0, x_1, \ldots]$, can one algorithmically decide
whether $I$ contains a $t$-short polynomial?

The problem is solved for $t \leq 2$: monomials ($t = 1$) can be detected via colon ideals,
and binomials ($t = 2$) via the algorithm of Jensen–Kahle–Katthän (2017). For $t \geq 3$,
the problem is open, even in the univariate case $\mathbb{Q}[x]$.
-/

namespace ShortPolynomialDecidability

noncomputable section

open MvPolynomial

/--
An ideal $I \subseteq \mathbb{Q}[x_0, x_1, \ldots]$ *has a $t$-short polynomial* if there
exists a nonzero $p \in I$ with $|\operatorname{supp}(p)| \leq t$.

The original problem is stated for polynomial rings $\mathbb{Q}[x_0, \ldots, x_{n-1}]$ in
finitely many variables, with $n$ part of the input. Here we use `MvPolynomial ℕ ℚ`
(countably many variables) as the ambient ring. This is equivalent because the generators
are finite and each mentions only finitely many variables, so every element of the ideal
uses finitely many variables. The ideal effectively lives in `MvPolynomial (Fin n) ℚ`
for the appropriate $n$.
-/
def HasShortPoly (t : ℕ) (I : Ideal (MvPolynomial ℕ ℚ)) : Prop :=
  ∃ p ∈ I, p ≠ 0 ∧ p.support.card ≤ t

/-- No nonzero polynomial has zero terms, so `HasShortPoly 0` is always false. -/
@[category API, AMS 13]
theorem not_hasShortPoly_zero (I : Ideal (MvPolynomial ℕ ℚ)) : ¬ HasShortPoly 0 I := by
  intro ⟨p, _, hp_ne, hp_card⟩
  exact hp_ne (MvPolynomial.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hp_card)))

/-- The zero ideal contains no nonzero elements, so it has no short polynomials. -/
@[category API, AMS 13]
theorem not_hasShortPoly_bot (t : ℕ) : ¬ HasShortPoly t (⊥ : Ideal (MvPolynomial ℕ ℚ)) := by
  intro ⟨p, hp_mem, hp_ne, _⟩
  exact hp_ne (Ideal.mem_bot.mp hp_mem)

/-- The whole ring contains the monomial $1$, which has one term. -/
@[category API, AMS 13]
theorem hasShortPoly_one_top : HasShortPoly 1 (⊤ : Ideal (MvPolynomial ℕ ℚ)) := by
  refine ⟨X 0, Submodule.mem_top, by simp, ?_⟩
  simp [MvPolynomial.support_X]

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

/-- The empty exponent vector gives the zero `Finsupp`, representing $x^0 = 1$. -/
@[category API, AMS 13]
theorem monomialOfList_nil : monomialOfList [] = 0 := by
  simp [monomialOfList]

/--
Interpret a `PolyRep` as a polynomial in $\mathbb{Q}[x_0, x_1, \ldots]$.
Each entry `(exps, num, den)` represents the term $\frac{\mathtt{num}}{\mathtt{den}} \cdot
x_0^{e_0} x_1^{e_1} \cdots$, where the coefficient is given as a fraction `num / den`
with `num : ℤ` and `den : ℕ`.
-/
def polyOfRep (p : PolyRep) : MvPolynomial ℕ ℚ :=
  (p.map (fun (exps, num, den) =>
    MvPolynomial.monomial (monomialOfList exps) (↑num / ↑den))).sum

/-- The empty list represents the zero polynomial. -/
@[category API, AMS 13]
theorem polyOfRep_nil : polyOfRep [] = 0 := by
  simp [polyOfRep]

/--
Build an ideal from a list of polynomial representations.
-/
def idealOfInput (L : List PolyRep) : Ideal (MvPolynomial ℕ ℚ) :=
  Ideal.span (Set.range (fun i : Fin L.length => polyOfRep (L.get i)))

/-- Empty generators produce the zero ideal. -/
@[category API, AMS 13]
theorem idealOfInput_nil : idealOfInput [] = ⊥ := by
  simp [idealOfInput]

/--
The short polynomial decision problem for a fixed $t$: given a list of generators
(in the concrete `PolyRep` encoding), does the ideal they generate contain a $t$-short
polynomial?
-/
def decisionProblem (t : ℕ) : List PolyRep → Prop :=
  fun L => HasShortPoly t (idealOfInput L)

/-- The zero ideal has no $t$-short polynomial. -/
@[category API, AMS 13]
theorem not_decisionProblem_nil (t : ℕ) : ¬ decisionProblem t [] := by
  simp only [decisionProblem]
  rw [idealOfInput_nil]
  exact not_hasShortPoly_bot t

/--
It is decidable whether a finitely generated ideal in
$R = \mathbb{Q}[x_0, x_1, \ldots]$
contains a monomial ($1$-short polynomial).
This follows from the characterization via iterated colon ideals:
$I$ contains a monomial if and only if $I : (\prod x_i)^\infty = R$.
-/
@[category research solved, AMS 13 68]
theorem monomial_decidability : ComputablePred (decisionProblem 1) := by
  sorry

/--
It is decidable whether a finitely generated ideal in
$R = \mathbb{Q}[x_0, x_1, \ldots]$
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
$\mathbb{Q}[x_0, x_1, \ldots]$ contains a $t$-short polynomial, for $t \geq 3$?

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

The ideal $I_n$ contains the binomial
$x^n - y$, and this is the lowest-degree binomial in $I_n$. Since the degree grows with $n$
while the generators always have degrees 1 and 2, no classical invariant (generating degree,
Castelnuovo–Mumford regularity, primary decomposition) can yield a uniform degree bound.
-/
def fibIdeal (n : ℕ) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {
    X 1 - C (Nat.fib n : ℚ) * X 0 - C (Nat.fib (n - 1) : ℚ),
    X 0 ^ 2 - X 0 - 1
  }

/-- The binomial $x^n - y$ belongs to $I_n$. A direct induction from $x^2 \equiv x + 1$
gives the polynomial-division identity $x^n \equiv F_n x + F_{n-1} \pmod{x^2 - x - 1}$;
combined with the generator $y - F_n x - F_{n-1}$, this yields $x^n - y \in I_n$. -/
@[category test, AMS 13]
theorem fib_ideal_contains_binomial (n : ℕ) (hn : 1 ≤ n) :
    X 0 ^ n - X 1 ∈ fibIdeal n := by
  suffices h : ∃ Q : MvPolynomial (Fin 2) ℚ,
      X 0 ^ n - C (Nat.fib n : ℚ) * X 0 - C (Nat.fib (n - 1) : ℚ) =
        Q * (X 0 ^ 2 - X 0 - 1) by
    obtain ⟨Q, hQ⟩ := h
    rw [fibIdeal, Ideal.mem_span_pair]
    exact ⟨-1, Q, by linear_combination -hQ⟩
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ k hk ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨X 0 * Q + C (Nat.fib k : ℚ), ?_⟩
    rw [show (k + 1) - 1 = k from rfl,
        show (C (Nat.fib (k + 1) : ℚ) : MvPolynomial (Fin 2) ℚ) =
          C (Nat.fib (k - 1) : ℚ) + C (Nat.fib k : ℚ) from by
          rw [← map_add]; congr 1; exact_mod_cast Nat.fib_add_one (by omega : k ≠ 0)]
    linear_combination X 0 * hQ

/-!
### Minimum-degree binomial in $I_n$

Every binomial in $I_n$ has total degree at least $n$.

Let $\varphi = (1 + \sqrt 5)/2$ be the golden ratio, a root of $x^2 - x - 1$. Evaluate
a binomial $a x^r y^s + b x^u y^v \in I_n$ at $(\varphi, \varphi^n)$ to get
$a \varphi^{r + ns} + b \varphi^{u + nv} = 0$. If the two exponents differed, factoring
out the smaller power would force a positive integer power of $\varphi$ to be rational,
but $\varphi^d = F_d \varphi + F_{d-1}$ is irrational for $d \geq 1$. Hence the exponents
agree, and combined with $(r,s) \neq (u,v)$ this forces $|r - u| \geq n$.
-/

namespace FibMinDeg

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

open Real

/-- Evaluation $\mathbb{Q}[x, y] \to \mathbb{R}$ at $(x, y) = (\varphi, \varphi^n)$. -/
private def evalGold (n : ℕ) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℝ :=
  MvPolynomial.aeval ![goldenRatio, goldenRatio ^ n]

private lemma evalGold_mem_fibIdeal (n : ℕ) (hn : 1 ≤ n) {p : MvPolynomial (Fin 2) ℚ}
    (hp : p ∈ fibIdeal n) : evalGold n p = 0 := by
  refine Submodule.span_induction (p := fun p _ => evalGold n p = 0) ?_ ?_ ?_ ?_ hp
  · rintro p (rfl | rfl)
    · simp [evalGold]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp; linear_combination -(goldenRatio_mul_fib_succ_add_fib m)
    · simp [evalGold]
  · simp
  · intros _ _ _ _ h₁ h₂; simp [h₁, h₂]
  · intros r _ _ h; simp [h]

private lemma evalGold_monomial (n : ℕ) (e : Fin 2 →₀ ℕ) (c : ℚ) :
    evalGold n (monomial e c) = (c : ℝ) * goldenRatio ^ (e 0 + n * e 1) := by
  rw [evalGold, MvPolynomial.aeval_monomial,
      Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp [Fin.prod_univ_two, pow_mul, pow_add]

/-- Positive integer powers of the golden ratio are irrational, since
$\varphi^{m+1} = F_{m+1} \cdot \varphi + F_m$ with $F_{m+1} \neq 0$. -/
private lemma goldenRatio_pow_irrational {d : ℕ} (hd : d ≠ 0) :
    Irrational (goldenRatio ^ d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  rw [← goldenRatio_mul_fib_succ_add_fib m, mul_comm]
  exact (goldenRatio_irrational.natCast_mul (by simp)).add_natCast _

/-- If $a \varphi^p + b \varphi^q = 0$ with rational $b \neq 0$ and $p < q$, contradiction:
factoring $\varphi^p$ would force $\varphi^{q-p}$ to equal $-a/b \in \mathbb{Q}$. -/
private lemma not_two_term_zero_of_lt (a : ℚ) {b : ℚ} (hb : b ≠ 0)
    {p q : ℕ} (hpq : p < q)
    (h : (a : ℝ) * goldenRatio ^ p + (b : ℝ) * goldenRatio ^ q = 0) : False := by
  obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
  have hd : d ≠ 0 := by omega
  have hp0 : (goldenRatio : ℝ) ^ p ≠ 0 := pow_ne_zero _ goldenRatio_ne_zero
  have hbR : (b : ℝ) ≠ 0 := mod_cast hb
  have hkey : (a : ℝ) + b * goldenRatio ^ d = 0 := by
    have hfac : (goldenRatio : ℝ) ^ p * ((a : ℝ) + b * goldenRatio ^ d) = 0 := by
      rw [pow_add] at h; linear_combination h
    exact (mul_eq_zero.mp hfac).resolve_left hp0
  exact (goldenRatio_pow_irrational hd).ne_rat (-a / b)
    (by push_cast; field_simp; linarith)

/-- A vanishing two-term combination $a \varphi^p + b \varphi^q = 0$ with nonzero rational
coefficients forces $p = q$. -/
private lemma exponents_eq_of_two_term_zero {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {p q : ℕ} (h : (a : ℝ) * goldenRatio ^ p + (b : ℝ) * goldenRatio ^ q = 0) :
    p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · exact (not_two_term_zero_of_lt a hb hpq h).elim
  · exact hpq
  · exact (not_two_term_zero_of_lt b ha hpq (by simpa [add_comm] using h)).elim

end FibMinDeg

/-- Every binomial in $I_n$ has total degree at least $n$, so $x^n - y$ is a minimum-degree
binomial. The bound depends on $n$, showing that the degree of the shortest binomial in an
ideal is controlled by the coefficients of the generators rather than by any classical
degree invariant. -/
@[category research solved, AMS 13 68]
theorem fib_ideal_min_degree_binomial (n : ℕ) (hn : 1 ≤ n) :
    ∀ p ∈ fibIdeal n, p.support.card = 2 → n ≤ p.totalDegree := by
  open FibMinDeg Real in
  intro p hp hcard
  rw [Finset.card_eq_two] at hcard
  obtain ⟨e₁, e₂, hne, hsupp⟩ := hcard
  set a := p.coeff e₁
  set b := p.coeff e₂
  have ha_ne : a ≠ 0 := MvPolynomial.mem_support_iff.mp (by rw [hsupp]; simp)
  have hb_ne : b ≠ 0 := MvPolynomial.mem_support_iff.mp (by rw [hsupp]; simp [Ne.symm hne])
  have hp_eq : p = monomial e₁ a + monomial e₂ b := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [hsupp, Finset.sum_pair hne]
  set p₁ := e₁ 0 + n * e₁ 1 with hp₁_def
  set p₂ := e₂ 0 + n * e₂ 1 with hp₂_def
  have hG : (a : ℝ) * goldenRatio ^ p₁ + (b : ℝ) * goldenRatio ^ p₂ = 0 := by
    have := evalGold_mem_fibIdeal n hn hp
    rwa [hp_eq, map_add, evalGold_monomial, evalGold_monomial] at this
  have hp₁p₂ : p₁ = p₂ := exponents_eq_of_two_term_zero ha_ne hb_ne hG
  -- Combined with e₁ ≠ e₂, this forces e₁ 1 ≠ e₂ 1.
  have he1_ne : e₁ 1 ≠ e₂ 1 := fun he => hne <| by
    ext i; fin_cases i
    · show e₁ 0 = e₂ 0; simp [hp₁_def, hp₂_def, he] at hp₁p₂; omega
    · exact he
  have hsum : ∀ e : Fin 2 →₀ ℕ, e.sum (fun _ e => e) = e 0 + e 1 := fun e => by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; simp [Fin.sum_univ_two]
  -- WLOG by symmetry: the larger e_i 1 forces the corresponding e_i 0 ≥ n.
  simp only [hp₁_def, hp₂_def] at hp₁p₂
  rcases lt_or_gt_of_ne he1_ne with hlt | hgt
  · have hd := MvPolynomial.le_totalDegree (s := e₁) (by rw [hsupp]; simp)
    rw [hsum] at hd; nlinarith
  · have hd := MvPolynomial.le_totalDegree (s := e₂) (by rw [hsupp]; simp)
    rw [hsum] at hd; nlinarith

end

end ShortPolynomialDecidability
