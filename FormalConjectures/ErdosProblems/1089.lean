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
# Erdős Problem 1089

*Reference:* [erdosproblems.com/1089](https://www.erdosproblems.com/1089)

Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$
determines at least $n$ distinct distances. Does $\lim_{d \to \infty} g_d(n) / d^{n-1}$
exist for all $n \geq 2$? The answer is yes, and the limit equals $1/(n-1)!$.

[BBS83] Bannai, E., Bannai, E., and Stanton, D., _An upper bound for the cardinality of an
$s$-distance subset in real Euclidean space. II_. Combinatorica (1983), 147–152.

[Cr62] Croft, H. T., _9-point and 7-point configurations in 3-space_.
Proc. London Math. Soc. (3) (1962), 400-424.

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Ann. Mat. Pura Appl. (4) (1975), 99-108.

[Fe26] T. Feng et al, _Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
Erdős Problems_. arXiv:2601.22401 (2026).
-/

open Classical Finset Filter

namespace Erdos1089

/-- The set of distinct distances determined by a finite set of points
in $d$-dimensional Euclidean space. -/
noncomputable def distinctDistances {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Finset ℝ :=
  S.offDiag.image (fun pq => dist pq.1 pq.2)

/-- The number of distinct distances determined by a finite set of points. -/
noncomputable def distinctDistanceCount {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (distinctDistances S).card

/-- $g_d(n)$ is the minimal number of points in $\mathbb{R}^d$ such that any collection of
that many points determines at least $n$ distinct distances. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (S : Finset (EuclideanSpace ℝ (Fin d))), S.card ≥ m →
    distinctDistanceCount S ≥ n}

/--
Erdős Problem 1089 (Kelly's question, resolved):
Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$ determines
at least $n$ distinct distances. The limit $\lim_{d \to \infty} g_d(n) / d^{n-1}$ exists and
equals $1/(n-1)!$ for all $n \geq 2$.

The lower bound $\binom{d+1}{n-1} + 1 \leq g_d(n)$ is due to Aletheia-Zomlefer [Fe26]
and the upper bound $g_d(n) \leq \binom{d+n-1}{n-1} + 1$ is due to Bannai, Bannai,
and Stanton [BBS83].
-/
@[category research solved, AMS 5 52]
theorem erdos_1089 :
    answer(True) ↔
      ∀ (n : ℕ), 2 ≤ n →
        Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
          atTop (nhds (1 / (Nat.factorial (n - 1) : ℝ))) := by
  sorry

end Erdos1089
