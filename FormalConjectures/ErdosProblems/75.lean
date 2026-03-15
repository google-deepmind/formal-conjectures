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
# Erdős Problem 75

*Reference:* [erdosproblems.com/75](https://www.erdosproblems.com/75)

Does there exist a graph on $\aleph_1$ vertices with chromatic number $\aleph_1$ such that
every set of $n$ vertices contains an independent set of size $> n^{1-\varepsilon}$ for all
$\varepsilon > 0$ and large $n$?

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large chromatic graphs_.
Annals of Discrete Mathematics **12** (1982), 117–123.

[Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and geometry_.
Resenhas (1995), 165–186.

[Er95d] Erdős, P., _On some problems in combinatorial set theory_.
Publ. Inst. Math. (Beograd) (N.S.) (1995), 61–65.

Erdős offered $1000 for a complete solution. See also Problems 74 and 750.
-/

open SimpleGraph Cardinal

namespace Erdos75

/--
Erdős Problem 75, Part 1 [EHS82, p. 120][Er95, p. 11][Er95d, p. 63]:

There exists a graph $G$ on $\aleph_1$ vertices with chromatic number $\aleph_1$ such that for
all $\varepsilon > 0$, if $n$ is sufficiently large and $S$ is any set of $n$ vertices, then
$S$ contains an independent set of size $> n^{1-\varepsilon}$.
-/
@[category research open, AMS 5]
theorem erdos_75 :
    answer(sorry) ↔
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      G.chromaticCardinal = ℵ_ 1 ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) > (n : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

/--
Erdős Problem 75, Part 2 (linear variant) [EHS82, p. 120][Er95, p. 11][Er95d, p. 63]:

There exists a graph $G$ on $\aleph_1$ vertices with chromatic number $\aleph_1$ such that
there exists $c > 0$ where every set of $n \geq 1$ vertices contains an independent
set of size at least $c \cdot n$.
-/
@[category research open, AMS 5]
theorem erdos_75.variants.linear :
    answer(sorry) ↔
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      G.chromaticCardinal = ℵ_ 1 ∧
      ∃ c : ℝ, c > 0 ∧
        ∀ n : ℕ, n ≥ 1 →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) ≥ c * (n : ℝ) := by
  sorry

end Erdos75
