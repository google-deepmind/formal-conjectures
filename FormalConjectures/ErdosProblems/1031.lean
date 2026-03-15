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
# Erdős Problem 1031

*Reference:* [erdosproblems.com/1031](https://www.erdosproblems.com/1031)

A question of Erdős, Fajtlowicz, and Staton [Er93, p.340].

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[PrRo99] Prömel, H.J. and Rödl, V., _Non-Ramsey graphs are c log n-universal_.
J. Combin. Theory Ser. A (1999), 379–384.
-/

open scoped Topology Real

namespace Erdos1031

/--
**Erdős Problem 1031** [Er93, p.340]:

If $G$ is a graph on $n$ vertices with no clique and no independent set of size
$\geq 10 \log n$, then $G$ contains an induced regular subgraph on $\geq c \log n$ vertices
(for some absolute constant $c > 0$) that is neither empty nor complete.

This was proved by Prömel and Rödl [PrRo99], who showed the stronger result
that for any $c > 0$, if $G$ contains no trivial subgraph on $\geq c \log n$ vertices
then $G$ contains all graphs with $O_c(\log n)$ vertices as induced subgraphs.
-/
@[category research solved, AMS 5]
theorem erdos_1031 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      G.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      Gᶜ.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ c * Real.log (↑n) ∧
        ∃ d : ℕ, d ≥ 1 ∧ d + 1 < S.card ∧
          ∀ v ∈ S, (S.filter (G.Adj v)).card = d := by
  sorry

end Erdos1031
