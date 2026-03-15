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
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Erdős Problem 60

*Reference:* [erdosproblems.com/60](https://www.erdosproblems.com/60)

Does every graph on $n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges contain
$\gg n^{1/2}$ many copies of $C_4$?

Conjectured by Erdős and Simonovits [Er90][Er93], who could not even prove that
at least 2 copies of $C_4$ are guaranteed. The behaviour of $\mathrm{ex}(n; C_4)$
is the subject of problem [765].

He, Ma, and Yang [HeMaYa21] proved the conjecture for the special case
$n = q^2 + q + 1$ where $q$ is an even integer.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
(1990), 467–478.

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is
eighty, Vol. 2 (Keszthely, 1993), 97–132.

[HeMaYa21] He, J., Ma, J., Yang, T., _Some extremal results on 4-cycles_.
J. Combin. Theory Ser. B (2021).
-/

open SimpleGraph

namespace Erdos60

/--
Erdős Problem 60 [Er90][Er93]:

Does every graph on $n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges contain
$\gg n^{1/2}$ copies of $C_4$?

Formally: there exist $c > 0$ and $N_0$ such that for all $n \geq N_0$, every graph $G$ on
$n$ vertices with more than $\mathrm{ex}(n; C_4)$ edges has at least $c \cdot n^{1/2}$ labelled
copies of $C_4$.
-/
@[category research open, AMS 5]
theorem erdos_60 : answer(sorry) ↔
    ∃ (c : ℝ) (_ : c > 0) (N₀ : ℕ),
    ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber n (cycleGraph 4) →
      (G.labelledCopyCount (cycleGraph 4) : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
He–Ma–Yang partial result [HeMaYa21]: the conjecture holds for $n = q^2 + q + 1$ where $q$
is an even integer. That is, there exists $c > 0$ such that for all even $q$, every graph on
$n = q^2 + q + 1$ vertices with more than $\mathrm{ex}(n; C_4)$ edges has at least
$c \cdot n^{1/2}$ labelled copies of $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_60_even_prime_power : answer(sorry) ↔
    ∃ (c : ℝ) (_ : c > 0),
    ∀ q : ℕ, 2 ∣ q →
    let n := q ^ 2 + q + 1
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber n (cycleGraph 4) →
      (G.labelledCopyCount (cycleGraph 4) : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Weak form of Erdős Problem 60: every graph on $n$ vertices with more than $\mathrm{ex}(n; C_4)$
edges contains at least 2 (unlabelled) copies of $C_4$. Equivalently, at least 16 labelled
copies (each unlabelled $C_4$ yields 8 labelled copies: 4 rotations × 2 reflections, and we
need at least 2 unlabelled copies). Erdős and Simonovits noted they could not even prove this
weaker statement.
-/
@[category research open, AMS 5]
theorem erdos_60_at_least_two : answer(sorry) ↔
    ∃ (N₀ : ℕ), ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber n (cycleGraph 4) →
      G.labelledCopyCount (cycleGraph 4) ≥ 16 := by
  sorry

end Erdos60
