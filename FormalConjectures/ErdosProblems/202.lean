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
# Erdős Problem 202

*Reference:* [erdosproblems.com/202](https://www.erdosproblems.com/202)

Let $n_1 < \cdots < n_r \leq N$ with associated $a_i \pmod{n_i}$ such that the congruence
classes are disjoint (every integer is $\equiv a_i \pmod{n_i}$ for at most one $i$).
How large can $r$ be in terms of $N$?

Let $f(N)$ denote the maximum such $r$. Erdős and Stein conjectured $f(N) = o(N)$,
proved by Erdős and Szemerédi [ErSz68]. The exact asymptotics remain open.

The best known bounds, due to de la Bretèche, Ford, and Vandehey [BFV13], are:
$$N / L(N)^{1+o(1)} < f(N) < N / L(N)^{\sqrt{3}/2+o(1)}$$
where $L(N) = \exp(\sqrt{\log N \cdot \log \log N})$.

They conjecture the lower bound is the truth, i.e., $f(N) = N / L(N)^{1+o(1)}$.

[ErSz68] Erdős, P. and Szemerédi, E.

[BFV13] de la Bretèche, R., Ford, K., and Vandehey, J.

[Er61, Er65, Er65b, Er73, Er77c, ErGr80, Va99] — see
[erdosproblems.com/202](https://www.erdosproblems.com/202) for full references.
-/

open Filter

namespace Erdos202

/-- A system of congruence classes with distinct positive moduli at most $N$ is
*pairwise disjoint* if no integer belongs to more than one class.
Each element $(n, a)$ represents the congruence class
$\{x \in \mathbb{Z} : x \equiv a \pmod{n}\}$. -/
def IsPairwiseDisjointSystem (S : Finset (ℕ × ℤ)) (N : ℕ) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ N) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    ∀ x : ℤ, ¬(x % (↑p.1 : ℤ) = p.2 % (↑p.1 : ℤ) ∧
               x % (↑q.1 : ℤ) = q.2 % (↑q.1 : ℤ)))

/--
Erdős Problem 202 (de la Bretèche–Ford–Vandehey conjecture) — OPEN.
[Er61, Er65, Er65b, Er73, Er77c, ErGr80, Va99]:

The maximum number $f(N)$ of pairwise disjoint congruence classes with distinct
moduli at most $N$ satisfies $f(N) \leq N / L(N)^{1-\varepsilon}$ for every
$\varepsilon > 0$ and all sufficiently large $N$, where
$L(N) = \exp(\sqrt{\log N \cdot \log \log N})$.

Combined with the proved lower bound $f(N) \geq N / L(N)^{1+\varepsilon}$ [BFV13], this
gives the conjectured asymptotics $f(N) = N / L(N)^{1+o(1)}$.
-/
@[category research open, AMS 11]
theorem erdos_202 :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ N : ℕ in atTop,
    ∀ S : Finset (ℕ × ℤ),
    IsPairwiseDisjointSystem S N →
    (S.card : ℝ) ≤ (N : ℝ) /
      Real.exp ((1 - ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
  sorry

end Erdos202
