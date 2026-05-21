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
# Erdős Problem 112

*References:*
- [erdosproblems.com/112](https://www.erdosproblems.com/112)
- [ErRa67] Erdős, P. and Rado, R., _Partition relations and transitivity domains of binary
  relations_, J. London Math. Soc. (1967), 624–633.
- [LaMi97] Larson, J. and Mitchell, W., _On a problem of Erdős and Rado_, Ann. Comb. (1997),
  245–252.
-/

open Digraph SimpleGraph

namespace Erdos112

/--
Erdős Problem 112: Determine the directed Ramsey number $k(n,m)$.
-/
@[category research open, AMS 5]
theorem erdos_112 :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNumber n m = (answer(sorry) : ℕ → ℕ → ℕ) n m := by
  sorry

/-- Smallest open case: determine $k(3, 3)$. Known bounds: $7 \leq k(3,3) \leq 14$. -/
@[category research open, AMS 5]
theorem erdos_112.variants.k_3_3 :
    dirRamseyNumber 3 3 = answer(sorry) := by
  sorry

/-- Smallest open case: determine $k(3, 4)$. -/
@[category research open, AMS 5]
theorem erdos_112.variants.k_3_4 :
    dirRamseyNumber 3 4 = answer(sorry) := by
  sorry

/--
Erdős–Rado upper bound [ErRa67]:
$$k(n,m) \leq \frac{2^{m-1} (n-1)^m + n - 2}{2n - 3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.erdos_rado_upper_bound :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNumber n m ≤ (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3) := by
  sorry

/--
Larson–Mitchell bound [LaMi97]: $k(n, 3) \leq n^2$.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.larson_mitchell :
    ∀ n : ℕ, 2 ≤ n →
      dirRamseyNumber n 3 ≤ n ^ 2 := by
  sorry

/-- The 3-color graph Ramsey number $R(a, b, c)$: the minimal $k$ such that every
symmetric 3-coloring of the edges of $K_k$ contains a monochromatic clique of size $a$, $b$,
or $c$ in the respective color. -/
noncomputable def graphRamseyNum3 (a b c : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (col : Fin k → Fin k → Fin 3), (∀ x y, col x y = col y x) →
    (∃ S : Finset (Fin k), S.card = a ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 0) ∨
    (∃ S : Finset (Fin k), S.card = b ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 1) ∨
    (∃ S : Finset (Fin k), S.card = c ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = 2)}

/--
Ramsey number sandwich (Hunter): $R(n,m) \leq k(n,m) \leq R(n,m,m)$, where $R$ is the
classical graph Ramsey number and $R(n,m,m)$ is the 3-color Ramsey number. The lower bound
holds because any undirected graph can be oriented, and the upper bound holds because the
three options for each pair of vertices (no edge, forward edge, backward edge) correspond
to a 3-coloring.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.ramsey_sandwich :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      graphRamseyNumber n m ≤ dirRamseyNumber n m ∧
      dirRamseyNumber n m ≤ graphRamseyNum3 n m m := by
  sorry

/--
Hunter–Steiner result: replacing "transitive tournament" with "directed path" in the
definition of $k(n,m)$ yields the exact answer $k(n,m) = (n-1)(m-1) + 1$.
-/
@[category research solved, AMS 5]
theorem erdos_112.variants.hunter_steiner :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirPathRamseyNumber n m = (n - 1) * (m - 1) + 1 := by
  sorry

-- TODO: Formalize additional variants from erdosproblems.com/112 (e.g., exact values
-- for small cases, further bounds on k(n,m) for specific n,m).

end Erdos112
