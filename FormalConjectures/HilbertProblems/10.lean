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

import FormalConjecturesUtil

/-!
# Hilbert's 10th problem

Hilbert's 10th problem asks for an algorithm which, given a polynomial equation
$f(x_1, \dots, x_n) = 0$ with integer coefficients, decides whether it has a solution in the
rational integers. Davis, Putnam, Robinson and Matiyasevich showed that no such algorithm
exists.

The same question over $\mathbb{Q}$ — is there an algorithm to decide whether a polynomial
equation in several variables has a *rational* solution? — is a well-known open problem. Since
a system $f_1 = \dots = f_k = 0$ has the same rational solutions as the single equation
$\sum_i f_i^2 = 0$, it is equivalent to ask for an algorithm deciding whether an affine variety
over $\mathbb{Q}$ has a rational point.

The standard strategy for a negative answer is to show that $\mathbb{Z}$ is *diophantine* in
$\mathbb{Q}$, i.e. positive-existentially definable, which would transfer the undecidability
over $\mathbb{Z}$ to $\mathbb{Q}$. Julia Robinson (1949) defined $\mathbb{Z}$ in $\mathbb{Q}$ by a
first-order formula, Poonen [Poonen2009] gave a $\forall \exists$ definition, and Koenigsmann
[Koenigsmann2016] gave a universal ($\forall$) definition; none of these is existential. In the
other direction, Mazur's conjecture [Mazur1992] — for a variety over $\mathbb{Q}$, the closure
of the set of rational points inside the real points has finitely many connected components —
would imply that $\mathbb{Z}$ is *not* diophantine in $\mathbb{Q}$, so that this strategy
cannot work.

By contrast, the analogous problem is undecidable over the ring of integers of every number
field ([KoymansPagano2024], [ABHS2025]), and decidable over $\mathbb{R}$ (by Tarski's
quantifier elimination for real closed fields), over $\mathbb{C}$, and over the $p$-adic fields
$\mathbb{Q}_p$ (Ax–Kochen and Ershov).

Polynomials are encoded here as finite lists of monomials, each monomial being an integer
coefficient together with a list of exponents; see `Hilbert10.MonomialList`. Restricting to
integer coefficients is no loss of generality, because clearing denominators turns an equation
with rational coefficients into an equivalent one with integer coefficients.

The negative answer over $\mathbb{Z}$ has been formalised in other proof assistants: in Coq by
[Larchey-Wendling and Forster](https://arxiv.org/abs/2003.04604), and in Isabelle by Bayer,
David, Stock, Pal, Matiyasevich and Schleicher
([AFP entry](https://www.isa-afp.org/entries/DPRM_Theorem.html)).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hilbert%27s_tenth_problem)
- [Matiyasevich1970] Yu. V. Matiyasevich, *Enumerable sets are Diophantine*, Soviet Math. Dokl.
  11 (1970), 354–358; Russian original in Dokl. Akad. Nauk SSSR 191 (1970), 279–282.
- [Davis1973] M. Davis, *Hilbert's tenth problem is unsolvable*, Amer. Math. Monthly 80 (1973),
  233–269, [doi:10.2307/2318447](https://doi.org/10.2307/2318447).
- [Mazur1992] B. Mazur, *The topology of rational points*, Experiment. Math. 1 (1992), 35–45,
  [Project Euclid](https://projecteuclid.org/euclid.em/1048709114).
- [Poonen2009] B. Poonen, *Characterizing integers among rational numbers with a
  universal-existential formula*, Amer. J. Math. 131 (2009), 675–682,
  [doi:10.1353/ajm.0.0057](https://doi.org/10.1353/ajm.0.0057),
  [arXiv:math/0703907](https://arxiv.org/abs/math/0703907).
- [Koenigsmann2016] J. Koenigsmann, *Defining $\mathbb{Z}$ in $\mathbb{Q}$*, Ann. of Math. 183
  (2016), 73–93, [doi:10.4007/annals.2016.183.1.2](https://doi.org/10.4007/annals.2016.183.1.2),
  [arXiv:1011.3424](https://arxiv.org/abs/1011.3424).
- [KoymansPagano2024] P. Koymans, C. Pagano, *Hilbert's tenth problem via additive
  combinatorics*, [arXiv:2412.01768](https://arxiv.org/abs/2412.01768).
- [ABHS2025] L. Alpöge, M. Bhargava, W. Ho, A. Shnidman, *Rank stability in quadratic extensions
  and Hilbert's tenth problem for the ring of integers of a number field*, Invent. Math. 243
  (2026), 1129–1139,
  [doi:10.1007/s00222-025-01392-3](https://doi.org/10.1007/s00222-025-01392-3),
  [arXiv:2501.18774](https://arxiv.org/abs/2501.18774).
-/

namespace Hilbert10

open MvPolynomial

/--
A finite encoding of a polynomial with integer coefficients in the variables
$X_0, X_1, X_2, \dots$: the list `[(c₀, e₀), (c₁, e₁), …]` encodes the polynomial
$\sum_j c_j \prod_i X_i^{(e_j)_i}$, where the exponent $(e_j)_i$ of $X_i$ is `eⱼ.getD i 0`, so
that an exponent list of length at most $i$ leaves $X_i$ out of that monomial.

This is the type of inputs to Hilbert's 10th problem: since it is `Primcodable`, it makes
sense to ask whether a predicate on it is decidable by an algorithm.
-/
abbrev MonomialList : Type := List (ℤ × List ℕ)

/-- The polynomial encoded by a `MonomialList`. -/
noncomputable def toMvPolynomial (p : MonomialList) : MvPolynomial ℕ ℤ :=
  (p.map fun m => C m.1 * ∏ i ∈ Finset.range m.2.length, X i ^ m.2.getD i 0).sum

/--
The equation `p = 0` has a solution in the commutative ring `K`.

Only finitely many variables occur in `toMvPolynomial p`, so quantifying over all assignments
`ℕ → K` is the same as quantifying over the finitely many relevant coordinates.
-/
def HasSolution (K : Type*) [CommRing K] (p : MonomialList) : Prop :=
  ∃ x : ℕ → K, aeval x (toMvPolynomial p) = 0

/-- Every polynomial with integer coefficients in the variables $X_0, X_1, \dots$ arises from
a `MonomialList`, so the encoding really does present all instances of Hilbert's 10th
problem. -/
@[category API, AMS 3 11]
theorem toMvPolynomial_surjective : Function.Surjective toMvPolynomial := by
  intro f
  refine ⟨f.support.toList.map fun d =>
    (coeff d f, (List.range (d.support.sup id + 1)).map d), ?_⟩
  rw [toMvPolynomial, List.map_map, Finset.sum_map_toList]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hsub : d.support ⊆ Finset.range (d.support.sup id + 1) := fun i hi =>
    Finset.mem_range.2 <| Nat.lt_succ_of_le <| Finset.le_sup (f := id) hi
  have : ∀ i ∈ Finset.range (d.support.sup id + 1),
      X (R := ℤ) i ^ ((List.range (d.support.sup id + 1)).map d).getD i 0 = X i ^ d i := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (Finset.mem_range.1 hi)]
    rfl
  simp only [Function.comp_apply, List.length_map, List.length_range]
  rw [Finset.prod_congr rfl this, ← Finset.prod_subset hsub
    fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi], prod_X_pow_eq_monomial,
    ← smul_eq_C_mul, smul_monomial, smul_eq_mul, mul_one]

/--
**Hilbert's 10th problem** (over $\mathbb{Z}$) has a negative answer: by the
Davis–Putnam–Robinson–Matiyasevich theorem there is no algorithm deciding whether a polynomial
equation with integer coefficients has an integer solution.

Mathlib has the Matiyasevich step of the proof, that exponentiation is diophantine
(`Dioph.pow_dioph`), but not the theorem itself.
-/
@[category research solved, AMS 3 11]
theorem hilbert_tenth_problem_int : ¬ ComputablePred (HasSolution ℤ) := by
  sorry

/--
**Hilbert's 10th problem over $\mathbb{Q}$**: is there an algorithm which, given a polynomial
equation in several variables with integer coefficients, decides whether it has a solution in
the rational numbers?
-/
@[category research open, AMS 3 11 14]
theorem hilbert_tenth_problem_rat : answer(sorry) ↔ ComputablePred (HasSolution ℚ) := by
  sorry

/--
Half of Hilbert's 10th problem over $\mathbb{Q}$ is easy: the equations that do have a rational
solution can be enumerated, by searching through all tuples of rationals. So by
`ComputablePred.computable_iff_re_compl_re'`, the content of `hilbert_tenth_problem_rat` is
whether the *complement* is also recursively enumerable.
-/
@[category textbook, AMS 3 11]
theorem rePred_hasSolution_rat : REPred (HasSolution ℚ) := by
  sorry

/--
Over $\mathbb{R}$ the answer is positive: by Tarski's quantifier elimination for real closed
fields it is decidable whether a polynomial equation with integer coefficients has a real
solution.
-/
@[category research solved, AMS 3 12 14]
theorem computablePred_hasSolution_real : ComputablePred (HasSolution ℝ) := by
  sorry

section Tests

/-- The list `[(2, [1]), (-1, [])]` encodes the polynomial $2X_0 - 1$. -/
@[category test, AMS 3 11]
theorem toMvPolynomial_two_X_sub_one :
    toMvPolynomial [(2, [1]), (-1, [])] = 2 * X 0 - 1 := by
  simp [toMvPolynomial]
  ring

/-- The list `[(1, [2]), (-2, [])]` encodes the polynomial $X_0^2 - 2$. -/
@[category test, AMS 3 11]
theorem toMvPolynomial_X_sq_sub_two :
    toMvPolynomial [(1, [2]), (-2, [])] = X 0 ^ 2 - 2 := by
  simp [toMvPolynomial]
  ring

/-- The list `[(1, [2]), (1, [0, 2]), (1, [])]` encodes the polynomial $X_0^2 + X_1^2 + 1$; a
trailing exponent list such as `[0, 2]` picks out the variable $X_1$. -/
@[category test, AMS 3 11]
theorem toMvPolynomial_sq_add_sq_add_one :
    toMvPolynomial [(1, [2]), (1, [0, 2]), (1, [])] = X 0 ^ 2 + X 1 ^ 2 + 1 := by
  simp [toMvPolynomial, Finset.prod_range_succ]
  ring

/-- The empty list encodes the zero polynomial, and the equation $0 = 0$ is solvable. -/
@[category test, AMS 3 11]
theorem hasSolution_nil (K : Type*) [CommRing K] : HasSolution K [] :=
  ⟨0, by simp [toMvPolynomial]⟩

/-- The constant polynomial `1` has no solution. -/
@[category test, AMS 3 11]
theorem not_hasSolution_one : ¬ HasSolution ℚ [(1, [])] := by
  rintro ⟨x, hx⟩
  simp [toMvPolynomial] at hx

/-- The equation $2X_0 - 1 = 0$ has the rational solution $X_0 = 1/2$. -/
@[category test, AMS 3 11]
theorem hasSolution_rat_two_X_sub_one : HasSolution ℚ [(2, [1]), (-1, [])] := by
  refine ⟨fun _ => 1 / 2, ?_⟩
  rw [toMvPolynomial_two_X_sub_one]
  simp

/-- The equation $2X_0 - 1 = 0$ has no integer solution: the rational and the integral problems
really are different. -/
@[category test, AMS 3 11]
theorem not_hasSolution_int_two_X_sub_one : ¬ HasSolution ℤ [(2, [1]), (-1, [])] := by
  rintro ⟨x, hx⟩
  rw [toMvPolynomial_two_X_sub_one] at hx
  simp at hx
  omega

/-- The equation $X_0^2 - 2 = 0$ has no rational solution. -/
@[category test, AMS 3 11]
theorem not_hasSolution_rat_X_sq_sub_two : ¬ HasSolution ℚ [(1, [2]), (-2, [])] := by
  rintro ⟨x, hx⟩
  rw [toMvPolynomial_X_sq_sub_two] at hx
  simp at hx
  have h : ((x 0 : ℝ)) ^ 2 = 2 := by exact_mod_cast (by linarith : x 0 ^ 2 = (2 : ℚ))
  refine irrational_sqrt_two ⟨|x 0|, ?_⟩
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, h]

/-- The equation $X_0^2 - 2 = 0$ does have a real solution: the rational and the real problems
really are different. -/
@[category test, AMS 3 12]
theorem hasSolution_real_X_sq_sub_two : HasSolution ℝ [(1, [2]), (-2, [])] := by
  refine ⟨fun _ => √2, ?_⟩
  rw [toMvPolynomial_X_sq_sub_two]
  simp

/-- The equation $X_0^2 + X_1^2 + 1 = 0$ has no rational solution. -/
@[category test, AMS 3 11]
theorem not_hasSolution_rat_sq_add_sq_add_one :
    ¬ HasSolution ℚ [(1, [2]), (1, [0, 2]), (1, [])] := by
  rintro ⟨x, hx⟩
  rw [toMvPolynomial_sq_add_sq_add_one] at hx
  simp at hx
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

end Tests

end Hilbert10
