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
# Erdős Problem 1088

*Reference:* [erdosproblems.com/1088](https://www.erdosproblems.com/1088)

Let $f_d(n)$ be the minimal $m$ such that any set of $m$ points in $\mathbb{R}^d$ contains
a set of $n$ points such that any two determined distances are distinct.
Estimate $f_d(n)$. In particular, is it true that, for fixed $n \geq 3$,
$f_d(n) = 2^{o(d)}$?

A problem of Erdős [Er75f]. It is easy to prove that $f_d(n) \leq n^{O_d(1)}$.
Erdős claimed that he and Straus proved $f_d(n) \leq c_n^d$ for some constant $c_n > 0$.

When $d = 1$, $f_1(n) \asymp n^2$ (see Problem 530). When $n = 3$,
$f_d(3) = d^2/2 + O(d)$ (see Problem 503). Specific known values include
$f_2(3) = 7$ (Erdős) and $f_3(3) = 9$ (Croft [Cr62]).

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Ann. Mat. Pura Appl. (4) (1975), 99-108.

[Cr62] Croft, H. T., _9-point and 7-point configurations in 3-space_.
Proc. London Math. Soc. (3) (1962), 400-424.
-/

namespace Erdos1088

/-- A finite set of points in a metric space has all pairwise distances
distinct if no two distinct unordered pairs determine the same distance:
whenever $\operatorname{dist}(a, b) = \operatorname{dist}(c, d)$ with $a \neq b$ and $c \neq d$, the pairs
$\{a, b\}$ and $\{c, d\}$ must coincide. -/
def AllPairwiseDistinctDists {α : Type*} [MetricSpace α]
    (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → c ≠ d → dist a b = dist c d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- $f_d(n)$ is the minimal $m$ such that any set of at least $m$ points in $\mathbb{R}^d$
contains a subset of $n$ points with all pairwise distances distinct. -/
noncomputable def erdosF (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
    S.card ≥ m →
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      T ⊆ S ∧ T.card = n ∧ AllPairwiseDistinctDists T}

/--
Erdős Problem 1088 [Er75f]:

For fixed $n \geq 3$, $f_d(n) = 2^{o(d)}$ as $d \to \infty$. That is, for every $\varepsilon > 0$,
there exists $D_0$ such that for all $d \geq D_0$, $f_d(n) \leq 2^{\varepsilon \cdot d}$.
-/
@[category research open, AMS 5 52]
theorem erdos_1088 :
    answer(sorry) ↔
      ∀ (n : ℕ), n ≥ 3 →
        ∀ ε : ℝ, ε > 0 →
          ∃ D₀ : ℕ, ∀ d : ℕ, d ≥ D₀ →
            (erdosF d n : ℝ) ≤ (2 : ℝ) ^ (ε * (d : ℝ)) := by
  sorry

/-- $f_2(3) = 7$: the minimum number of points in $\mathbb{R}^2$ that guarantees a subset
of $3$ points with all pairwise distances distinct is $7$. Due to Erdős. -/
@[category research solved, AMS 5 52]
theorem erdos_1088_f2_3 : erdosF 2 3 = 7 := by
  sorry

/-- $f_3(3) = 9$: the minimum number of points in $\mathbb{R}^3$ that guarantees a subset
of $3$ points with all pairwise distances distinct is $9$. Due to Croft [Cr62]. -/
@[category research solved, AMS 5 52]
theorem erdos_1088_f3_3 : erdosF 3 3 = 9 := by
  sorry

end Erdos1088
