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
# Erdős Problem 1005

*Reference:* [erdosproblems.com/1005](https://www.erdosproblems.com/1005)

Let $a_1/b_1, a_2/b_2, \ldots$ be the Farey fractions of order $n \geq 4$. Let $f(n)$ be
the largest integer such that for all pairs of indices $k < l$ with $l \leq k + f(n)$,
the fractions $a_k/b_k$ and $a_l/b_l$ are "similarly ordered":
$(a_k - a_l)(b_k - b_l) \geq 0$.

[Er43] Erdős, P., *On the distribution of the convergents of almost all real numbers*.
Bull. Amer. Math. Soc. (1943).

[vD25b] van Doorn, T. (2025).
-/

open Filter Finset

namespace Erdos1005

/-- The Farey fractions of order $n$: all reduced fractions $a/b \in [0,1]$ with
$b \leq n$, as a sorted list of rationals. -/
def fareyFractions (n : ℕ) : List ℚ :=
  ((Finset.Icc 1 n).biUnion fun b =>
    ((Finset.range (b + 1)).filter fun a => Nat.Coprime a b).image
      fun (a : ℕ) => (a : ℚ) / (b : ℚ)).sort (· ≤ ·)

/-- Two Farey fractions $p = a_1/b_1$ and $q = a_2/b_2$ (in lowest terms) are
similarly ordered if $(a_1 - a_2)(b_1 - b_2) \geq 0$. -/
def similarlyOrdered (p q : ℚ) : Prop :=
  (p.num - q.num) * ((p.den : ℤ) - q.den) ≥ 0

/-- $f(n)$: the largest $d$ such that for all pairs of indices $i < j$ with $j \leq i + d$
in the Farey sequence of order $n$, the fractions are similarly ordered. -/
noncomputable def fareySimOrderFn (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∀ i j : ℕ, i < j → j ≤ i + d →
    ∀ (hi : i < (fareyFractions n).length) (hj : j < (fareyFractions n).length),
    similarlyOrdered ((fareyFractions n).get ⟨i, hi⟩) ((fareyFractions n).get ⟨j, hj⟩)}

/--
Erdős Problem 1005 [Er43]:

There exists a constant $c > 0$ such that $f(n)/n \to c$ as $n \to \infty$, where $f(n)$ is
the largest window size for similarly ordered consecutive Farey fractions of
order $n$.

van Doorn [vD25b] proved $(1/12 - o(1))n \leq f(n) \leq n/4 + O(1)$ and conjectures
$c = 1/4$.
-/
@[category research open, AMS 11]
theorem erdos_1005 :
    ∃ c : ℝ, c > 0 ∧
    Tendsto (fun n : ℕ => (fareySimOrderFn n : ℝ) / (n : ℝ)) atTop (nhds c) := by
  sorry

end Erdos1005
