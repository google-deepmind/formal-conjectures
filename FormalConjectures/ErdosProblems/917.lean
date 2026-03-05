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
# Erdős Problem 917

*Reference:* [erdosproblems.com/917](https://www.erdosproblems.com/917)

Let $k \geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices
which has chromatic number $k$ and is critical (i.e. deleting any edge reduces
the chromatic number).

Is it true that $f_k(n) \gg_k n^2$?
Is it true that $f_6(n) \sim n^2/4$?
More generally, is it true that, for $k \geq 6$,
$$f_k(n) \sim \tfrac{1}{2}\left(1 - \tfrac{1}{\lfloor k/3 \rfloor}\right) n^2?$$

Toft [To70] proved that $f_k(n) \gg_k n^2$ for $k \geq 4$.
Stiebitz [St87] disproved the asymptotic for $k \not\equiv 0 \pmod{3}$.

[Er69b] Erdős, P. (1969).

[Er93] Erdős, P. (1993).

[To70] Toft, B. (1970).

[St87] Stiebitz, M. (1987).
-/

open SimpleGraph

namespace Erdos917

/--
A simple graph $G$ is $k$-critical if its chromatic number equals $k$ and for every
edge $e$, the graph obtained by deleting $e$ has chromatic number strictly less
than $k$.
-/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
  ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < (k : ℕ∞)

/--
Erdős Problem 917, Part 1 [Er69b]:
For $k \geq 4$, $f_k(n) \gg_k n^2$. There exists a constant $c > 0$ such that for all
sufficiently large $n$, there exists a $k$-critical graph on $n$ vertices with at
least $c \cdot n^2$ edges.

Proved by Toft [To70].
-/
@[category research solved, AMS 5]
theorem erdos_917 :
    answer(True) ↔ ∀ k : ℕ, k ≥ 4 →
      ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ G : SimpleGraph (Fin n),
          IsCritical G k ∧ (G.edgeSet.ncard : ℝ) ≥ c * (n : ℝ) ^ 2 := by
  sorry

/--
Erdős Problem 917, Part 2 [Er69b][Er93]:
$f_6(n) \sim n^2/4$. For all $\varepsilon > 0$ and sufficiently large $n$, the maximum number of
edges in a $6$-critical graph on $n$ vertices is asymptotically $n^2/4$.
-/
@[category research open, AMS 5]
theorem erdos_917.variants.f6_asymptotic :
    answer(sorry) ↔
      ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (∃ G : SimpleGraph (Fin n),
          IsCritical G 6 ∧ (G.edgeSet.ncard : ℝ) ≥ (1 / 4 - ε) * (n : ℝ) ^ 2) ∧
        (∀ G : SimpleGraph (Fin n),
          IsCritical G 6 → (G.edgeSet.ncard : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) ^ 2) := by
  sorry

/--
Erdős Problem 917, Part 3 [Er69b]:
For $k \geq 6$,
$$f_k(n) \sim \tfrac{1}{2}\left(1 - \tfrac{1}{\lfloor k/3 \rfloor}\right) n^2.$$

Note: Disproved by Stiebitz [St87] for $k \not\equiv 0 \pmod{3}$.
-/
@[category research solved, AMS 5]
theorem erdos_917.variants.general_asymptotic :
    answer(False) ↔ ∀ k : ℕ, k ≥ 6 →
      let d : ℕ := k / 3
      let α : ℝ := 1 / 2 * (1 - 1 / (d : ℝ))
      ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (∃ G : SimpleGraph (Fin n),
          IsCritical G k ∧ (G.edgeSet.ncard : ℝ) ≥ (α - ε) * (n : ℝ) ^ 2) ∧
        (∀ G : SimpleGraph (Fin n),
          IsCritical G k → (G.edgeSet.ncard : ℝ) ≤ (α + ε) * (n : ℝ) ^ 2) := by
  sorry

end Erdos917
