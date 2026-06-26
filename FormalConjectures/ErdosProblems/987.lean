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
# Erdős Problem 987

The full Lean proofs of every statement below are available at
[Marti2203/formal-conjectures](https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean).
That file is too large to inline here, so this file keeps only the problem statements
(with `sorry` placeholders) and tags each with `formal_proof using lean4 at` pointing to the
external proof.

*References:*
- [erdosproblems.com/987](https://www.erdosproblems.com/987)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability, and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Cl67] Clunie, J., On a problem of Erdős. J. London Math. Soc. (1967), 133--136.
- [Er64b] Erdős, P., Problems and results on diophantine approximations. Compositio Math. (1964),
  52-65.
- [Er65b] Erdős, P., Some remarks on number theory. Israel J. Math. (the actual reference
  cited by Clunie 1967 as [2]; the erdosproblems.com bibliography points to a different
  Erdős 1965 paper, "Some recent advances and current problems in number theory" (Lectures
  on Modern Mathematics III, 1965, 196-244), which does not appear to contain the
  exponential-sum log-bound proof).
- [Ha74] Hayman, W. K., Research problems in function theory: new problems. (1974), 155--180.
- [Li69] Lindström, B., An inequality for $B_2$-sequences. J. Combinatorial Theory (1969), 211-212.
-/

open Filter Finset Asymptotics

namespace Erdos987

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Shorthand for the additive character $e(x) = e^{2 \pi i x}$.
(Matches `Real.fourierChar` / `𝐞` from `Mathlib/Analysis/Complex/Circle.lean`, but
kept as a local definition for readability across the many sites that use it.) -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

/--
For an infinite sequence $x_1, x_2, \ldots \in (0, 1)$, define
$$A_k = \limsup_{n \to \infty} \left\lvert \sum_{j \le n} e(k x_j) \right\rvert,$$
where $e(x) = e^{2\pi i x}$.
-/
noncomputable def A (x : ℕ → ℝ) (k : ℕ) : EReal :=
  atTop.limsup fun n : ℕ => (‖∑ j ∈ range n, e (k * x j)‖ : EReal)

/- ## Question 1 -/

/-- Question 1:

Is it true that $\limsup_{k \to \infty} A_k = \infty$?

Erdős [Er64b] remarks it is "easy to see" that $\limsup_k \sup_n |\sum_{j \le n} e(k x_j)| = \infty$.
Erdős [Er65b] later found a "very easy" proof that $A_k \gg \log k$ for infinitely many $k$.
Clunie [Cl67] proved that $A_k \gg k^{1/2}$ for infinitely many $k$, which implies the answer is
yes (Tao independently found a proof). This is Problem 7.21 in [Ha74]. -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.parts.i :
    answer(True) ↔ ∀ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      atTop.limsup (fun k : ℕ => A x k) = ⊤ := by
  sorry

/-- Erdős [Er64b] remarks it is "easy to see" that for every infinite sequence
$x_1, x_2, \ldots \in (0, 1)$,
$$\limsup_{k \to \infty} \sup_n \left\lvert \sum_{j \le n} e(k x_j) \right\rvert = \infty.$$ -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.sup_limsup_infty
    (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    atTop.limsup (fun k : ℕ =>
      ⨆ n : ℕ, ((‖∑ j ∈ range n, e ((k : ℝ) * x j)‖ : ℝ) : EReal)) = ⊤ := by
  sorry

/-- Erdős [Er65b] proved that, for every infinite sequence $x_1, x_2, \ldots \in (0, 1)$,
$A_k \gg \log k$ for infinitely many $k$. -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.log_lower_bound
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ᶠ k : ℕ in atTop, ((c * Real.log k : ℝ) : EReal) ≤ A x k := by
  sorry

/-- Clunie [Cl67] proved that, for every infinite sequence $x_1, x_2, \ldots \in (0, 1)$,
$A_k \gg k^{1/2}$ for infinitely many $k$. (Tao independently found a proof.) -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.sqrt_lower_bound
    (x : ℕ → ℝ) (hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ᶠ k : ℕ in atTop, ((c * Real.sqrt k : ℝ) : EReal) ≤ A x k := by
  sorry

/-- **Linear upper bound (weakened).** A first weakened version of Clunie's `A_k ≤ k`: there
exists a sequence $x \in (0,1)$ with $A_k \le 2k$ for all $k \ge 1$. The witness is the
(shifted) van der Corput sequence. For the tighter $A_k \le k + 1$ bound see
`linear_upper_bound_clunie`. -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.linear_upper_bound_weak :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((2 * k : ℝ) : EReal) := by
  sorry

/-- **Linear upper bound (tight via Clunie phase tracking).** Tighter than
`linear_upper_bound_weak`: there exists a sequence $x \in (0,1)$ with $A_k \le k + 1$ for all
$k \ge 1$, via the (shifted) van der Corput sequence. Whether the $+1$ can be eliminated to
recover Clunie's exact $A_k \le k$ under the strict $\mathrm{Ioo}\,0\,1$ hypothesis is open in
this formalization (see `linear_upper_bound`). -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.linear_upper_bound_clunie :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ (((k : ℝ) + 1) : EReal) := by
  sorry

/-- Clunie [Cl67] proved that there exists an infinite sequence $\{z_\nu\}$ on the unit circle
with $A_\nu \le \nu$ for all $\nu \ge 1$. Translating $z_\nu = e(x_\nu)$, the natural domain of
$x_\nu$ is the half-open unit interval $\mathrm{Ico}\,0\,1$, matching the original
[Er64b]/[Cl67] statement (any unit complex number is allowed, including $z = 1$, i.e. $x = 0$).

**Note**: erdosproblems.com/987 phrases the problem with the *open* interval
$x_\nu \in (0, 1)$, which excludes $z = 1$ and is strictly stronger than what [Er64b]/[Cl67]
state; we align with the original papers here. The shifted-vdc $\le k + 1$ variant under the
open interval is preserved as `linear_upper_bound_clunie`. -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.linear_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ico (0 : ℝ) 1),
      ∀ k : ℕ, 1 ≤ k → A x k ≤ ((k : ℝ) : EReal) := by
  sorry

/-- An internal OpenAI model (see [APSSV26b, §3]) proved that there exists an infinite sequence
$x_1, x_2, \ldots \in (0, 1)$ such that
$\sup_n \left\lvert \sum_{j \le n} e(k x_j) \right\rvert \ll (k \log k)^{1/2}$ for all $k \ge 1$
(in particular $A_k \ll (k \log k)^{1/2}$).

Note: the bound is restricted to $k \ge 2$ since $\log 1 = 0$ would make the RHS vanish at
$k = 1$, while the LHS $\|\sum_{j < n} e(x_j)\|$ can equal $1$ (e.g. for $n = 1$). -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.sqrt_log_upper_bound :
    ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (C : ℝ) (_ : 0 < C),
      ∀ k n : ℕ, 2 ≤ k → ‖∑ j ∈ range n, e (k * x j)‖ ≤ C * Real.sqrt (k * Real.log k) := by
  sorry

/- ## Question 2 -/

/-- **Question 2 (parts.ii)**: Is it possible for $A_k = o(k)$? Yes — there exists a sequence
$(x_n) \in (0, 1)$ and a bound $b(k) = o(k)$ with $A x k \le b k$ eventually. A corollary of
`sqrt_log_upper_bound` (which gives a $\sqrt{k \log k}$ bound) plus the asymptotic
$\sqrt{k \log k} = o(k)$. -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.parts.ii :
    answer(True) ↔ ∃ (x : ℕ → ℝ) (_ : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1) (b : ℕ → ℝ),
      b =o[atTop] (fun k : ℕ => (k : ℝ)) ∧ ∀ᶠ k : ℕ in atTop, A x k ≤ ((b k : ℝ) : EReal) := by
  sorry

/-- Liu [Li69] showed that, for any $\epsilon > 0$, $A_k \gg k^{1 - \epsilon}$ infinitely often
under the additional assumption that there are only a finite number of distinct points. Clunie
observed in the Mathscinet review of [Li69] that under this assumption in fact $A_k = \infty$
infinitely often (the version stated here). -/
@[category research solved, AMS 11 40 42, formal_proof using lean4 at
"https://github.com/Marti2203/formal-conjectures/blob/19c63d48acce3099c242b059518c49bf8dc0eab8/FormalConjectures/ErdosProblems/987.lean"]
theorem erdos_987.variants.finite_distinct_points
    (x : ℕ → ℝ) (_hx : ∀ j : ℕ, x j ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : (Set.range x).Finite) :
    ∃ᶠ k : ℕ in atTop, A x k = ⊤ := by
  sorry

end Erdos987
